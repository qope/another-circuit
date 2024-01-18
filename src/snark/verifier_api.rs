use std::fs::File;
use std::io::Write;
use std::rc::Rc;
use std::time::Instant;

use colored::Colorize;
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::bn256::{Bn256, Fq, Fr, G1Affine};
use halo2_proofs::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey,
};
use halo2_proofs::poly::commitment::{Params, ParamsProver};
use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_proofs::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
use halo2_proofs::poly::kzg::strategy::AccumulatorStrategy;
use halo2_proofs::poly::VerificationStrategy;
use halo2_proofs::transcript::{TranscriptReadBuffer, TranscriptWriterBuffer};
use halo2curves::goldilocks::fp::Goldilocks;
use halo2wrong_maingate::{big_to_fe, fe_to_big};
use itertools::Itertools;
use lazy_static::lazy_static;
use plonky2::{field::goldilocks_field::GoldilocksField, plonk::config::PoseidonGoldilocksConfig};
use rand::rngs::OsRng;
use snark_verifier::loader::evm::{self, encode_calldata, EvmLoader};
use snark_verifier::pcs::kzg::{Gwc19, KzgAs};
use snark_verifier::system::halo2::transcript::evm::EvmTranscript;
use snark_verifier::system::halo2::{compile, Config};
use snark_verifier::verifier::{self, SnarkVerifier};

use super::types::{
    self, common_data::CommonData, proof::ProofValues, verification_key::VerificationKeyValues,
};
use super::verifier_circuit::Verifier;
use super::ProofTuple;

type PlonkVerifier = verifier::plonk::PlonkVerifier<KzgAs<Bn256, Gwc19>>;

const DEGREE: usize = 22;

lazy_static! {
    static ref SRS: ParamsKZG<Bn256> = EvmVerifier::gen_srs(DEGREE as u32);
}

pub struct EvmVerifier;

impl EvmVerifier {
    pub fn gen_srs(k: u32) -> ParamsKZG<Bn256> {
        ParamsKZG::<Bn256>::setup(k, OsRng)
    }

    pub fn gen_pk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
        let vk = keygen_vk(params, circuit).unwrap();
        keygen_pk(params, vk, circuit).unwrap()
    }

    pub fn gen_proof<C: Circuit<Fr>>(
        params: &ParamsKZG<Bn256>,
        pk: &ProvingKey<G1Affine>,
        circuit: C,
        instances: Vec<Vec<Fr>>,
    ) -> Vec<u8> {
        MockProver::run(params.k(), &circuit, instances.clone())
            .unwrap()
            .assert_satisfied();
        let instances = instances
            .iter()
            .map(|instances| instances.as_slice())
            .collect_vec();
        let proof = {
            let mut transcript = TranscriptWriterBuffer::<_, G1Affine, _>::init(Vec::new());
            create_proof::<
                KZGCommitmentScheme<Bn256>,
                ProverGWC<_>,
                _,
                _,
                EvmTranscript<_, _, _, _>,
                _,
            >(
                params,
                pk,
                &[circuit],
                &[instances.as_slice()],
                OsRng,
                &mut transcript,
            )
            .unwrap();
            transcript.finalize()
        };

        let accept = {
            let mut transcript = TranscriptReadBuffer::<_, G1Affine, _>::init(proof.as_slice());
            VerificationStrategy::<_, VerifierGWC<_>>::finalize(
                verify_proof::<_, VerifierGWC<_>, _, EvmTranscript<_, _, _, _>, _>(
                    params.verifier_params(),
                    pk.get_vk(),
                    AccumulatorStrategy::new(params.verifier_params()),
                    &[instances.as_slice()],
                    &mut transcript,
                )
                .unwrap(),
            )
        };
        assert!(accept);

        proof
    }

    /// Generates EVM verifier for the proof generated by circuit `stark_verifier`
    pub fn gen_evm_verifier(
        params: &ParamsKZG<Bn256>,
        vk: &VerifyingKey<G1Affine>,
        num_instance: Vec<usize>,
    ) -> Vec<u8> {
        let protocol = compile(
            params,
            vk,
            Config::kzg().with_num_instance(num_instance.clone()),
        );
        let vk = (params.get_g()[0], params.g2(), params.s_g2()).into();

        let loader = EvmLoader::new::<Fq, Fr>();
        let protocol = protocol.loaded(&loader);
        let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(&loader);

        let instances = transcript.load_instances(num_instance);
        let proof = PlonkVerifier::read_proof(&vk, &protocol, &instances, &mut transcript).unwrap();
        PlonkVerifier::verify(&vk, &protocol, &instances, &proof).unwrap();

        evm::compile_yul(&loader.yul_code())
    }
}

fn report_elapsed(now: Instant) {
    println!(
        "{}",
        format!("Took {} milliseconds", now.elapsed().as_millis())
            .blue()
            .bold()
    );
}

/// Public API for generating Halo2 proof for Plonky2 verifier circuit
/// feed Plonky2 proof, `VerifierOnlyCircuitData`, `CommonCircuitData`
/// This runs only mock prover for constraint check
pub fn verify_inside_snark_mock(proof: ProofTuple<GoldilocksField, PoseidonGoldilocksConfig, 2>) {
    let (proof_with_public_inputs, vd, cd) = proof;

    // proof_with_public_inputs -> ProofValues type
    let proof = ProofValues::<Fr, 2>::from(proof_with_public_inputs.proof);

    let instances = proof_with_public_inputs
        .public_inputs
        .iter()
        .map(|e| big_to_fe(fe_to_big::<Goldilocks>(types::to_goldilocks(*e))))
        .collect::<Vec<Fr>>();
    let vk = VerificationKeyValues::from(vd.clone());
    let common_data = CommonData::from(cd);

    let verifier_circuit = Verifier::new(proof, instances.clone(), vk, common_data);
    let _prover = MockProver::run(DEGREE as u32, &verifier_circuit, vec![instances]).unwrap();
    _prover.assert_satisfied()
}

/// Public API for generating Halo2 proof for Plonky2 verifier circuit
/// feed Plonky2 proof, `VerifierOnlyCircuitData`, `CommonCircuitData`
/// This runs real prover and generates valid SNARK proof, generates EVM verifier and runs the verifier
pub fn verify_inside_snark(proof: ProofTuple<GoldilocksField, PoseidonGoldilocksConfig, 2>) {
    let (proof_with_public_inputs, vd, cd) = proof;
    let proof = ProofValues::<Fr, 2>::from(proof_with_public_inputs.proof);
    let instances = proof_with_public_inputs
        .public_inputs
        .iter()
        .map(|e| big_to_fe(fe_to_big::<Goldilocks>(types::to_goldilocks(*e))))
        .collect::<Vec<Fr>>();
    let vk = VerificationKeyValues::from(vd.clone());
    let common_data = CommonData::from(cd);

    // runs mock prover
    let circuit = Verifier::new(proof, instances.clone(), vk, common_data);
    let mock_prover = MockProver::run(DEGREE as u32, &circuit, vec![instances.clone()]).unwrap();
    mock_prover.assert_satisfied();
    println!("{}", "Mock prover passes".white().bold());

    // generates EVM verifier
    let pk = EvmVerifier::gen_pk(&SRS, &circuit);
    let deployment_code = EvmVerifier::gen_evm_verifier(&SRS, pk.get_vk(), vec![instances.len()]);

    // generates SNARK proof and runs EVM verifier
    println!("{}", "Starting finalization phase".red().bold());
    let now = Instant::now();
    let proof = EvmVerifier::gen_proof(&SRS, &pk, circuit.clone(), vec![instances.clone()]);
    println!("{}", "SNARK proof generated successfully!".white().bold());
    report_elapsed(now);

    let calldata = encode_calldata(&[instances], &proof);
    let deployment_code_hex = "0x".to_string() + &hex::encode(deployment_code);
    let calldata_hex = "0x".to_string() + &hex::encode(calldata);
    let mut file = File::create("deployment_code.txt").unwrap();
    file.write_all(deployment_code_hex.as_bytes()).unwrap();
    let mut file = File::create("calldata.txt").unwrap();
    file.write_all(calldata_hex.as_bytes()).unwrap();
    // EvmVerifier::evm_verify(deployment_code, vec![instances], proof);
}

#[cfg(test)]
mod tests {
    use plonky2::{
        field::types::Field,
        hash::{
            hashing::hash_n_to_hash_no_pad,
            poseidon::{PoseidonHash, PoseidonPermutation},
        },
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };

    use crate::snark::ProofTuple;

    use super::verify_inside_snark_mock;
    use super::*;

    type F = <C as GenericConfig<D>>::F;
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;

    fn generate_proof_tuple() -> ProofTuple<F, C, D> {
        let (inner_target, inner_data) = {
            let hash_const =
                hash_n_to_hash_no_pad::<F, PoseidonPermutation<F>>(&[F::from_canonical_u64(42)]);
            dbg!(hash_const);

            let mut builder =
                CircuitBuilder::<F, D>::new(CircuitConfig::standard_inner_stark_verifier_config());
            let target = builder.add_virtual_target();
            let expected_hash = builder.constant_hash(hash_const);
            let hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(vec![target]);
            builder.connect_hashes(hash, expected_hash);
            builder.register_public_inputs(&expected_hash.elements);
            let data = builder.build::<C>();
            (target, data)
        };

        let mut builder =
            CircuitBuilder::<F, D>::new(CircuitConfig::standard_stark_verifier_config());
        let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
        let vd = builder.constant_verifier_data(&inner_data.verifier_only);
        builder.verify_proof::<C>(&proof_t, &vd, &inner_data.common);
        builder.register_public_inputs(&proof_t.public_inputs);
        let data = builder.build::<C>();

        let proof = {
            let mut pw = PartialWitness::new();
            pw.set_target(inner_target, F::from_canonical_usize(42));
            inner_data.prove(pw).unwrap()
        };

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_t, &proof);
        let final_proof = data.prove(pw).unwrap();

        let proof: ProofTuple<F, C, D> = (final_proof, data.verifier_only, data.common);
        proof
    }

    #[test]
    fn test_recursive_halo2_mock() {
        let proof = generate_proof_tuple();
        verify_inside_snark_mock(proof);
    }

    #[test]
    fn test_recursive_halo2_proof() {
        let proof = generate_proof_tuple();
        verify_inside_snark(proof);
    }

    #[test]
    fn test_save_srs() {
        let srs = EvmVerifier::gen_srs(23);
        let now = Instant::now();
        let mut buf = vec![];
        srs.write(&mut buf).unwrap();
        println!("write to buf {:?}", now.elapsed());

        let mut srs_file = File::create("srs_buf.dat").unwrap();
        srs_file.write(&buf).unwrap();
        println!("saved to file {:?}", now.elapsed());

        let now = Instant::now();
        let mut srs_file = File::create("srs_direct.dat").unwrap();
        srs.write(&mut srs_file).unwrap();
        println!("saved to file directory {:?}", now.elapsed());
    }
}
