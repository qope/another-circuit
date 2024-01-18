use std::{fs::File, io::Write};

use halo2_proofs::{
    circuit::{floor_planner::V1, Layouter, Value},
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fr},
    plonk::{Circuit, ConstraintSystem, Error},
    poly::kzg::commitment::ParamsKZG,
};
use halo2wrong::RegionCtx;
use snark_verifier::loader::evm::encode_calldata;

use crate::snark::verifier_api::EvmVerifier;

use super::chip::{
    goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig},
    native_chip::{
        arithmetic_chip::{ArithmeticChip, ArithmeticConfig},
        linear_chip::LinearConfig,
        poseidon_chip::{PoseidonChip, PoseidonConfig},
    },
};

#[derive(Clone, Default)]
pub struct TestCircuit;

impl Circuit<Fr> for TestCircuit {
    type Config = GoldilocksChipConfig<Fr>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let arithmetic_config = ArithmeticConfig::<Fr>::configure(meta);
        let linear_config = LinearConfig::<Fr>::configure(meta);
        GoldilocksChipConfig {
            arithmetic_config,
            linear_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let chip = GoldilocksChip::new(&config);

        layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                let x = chip.assign_value(ctx, Value::known(Fr::from(2)))?;
                let y = chip.assign_value(ctx, Value::known(Fr::from(2)))?;
                let _z = chip.mul(ctx, &x, &y)?;

                let poseidon_config = PoseidonConfig {
                    arithmetic_config: config.arithmetic_config.clone(),
                    linear_config: config.linear_config.clone(),
                };
                let hash_chip = PoseidonChip::construct(poseidon_config);

                let state = [(); 12].map(|_| x.clone());
                let _hash = hash_chip.permute(ctx, state)?;

                Ok(())
            },
        )?;

        let arithmetic = ArithmeticChip::construct(config.arithmetic_config);
        arithmetic.load_table(&mut layouter)?;

        Ok(())
    }
}

const DEGREE: u32 = 17;

#[test]
fn test_goldilocks_contract() {
    let circuit = TestCircuit;
    let mock_prover = MockProver::run(DEGREE, &circuit, vec![vec![]]).unwrap();
    mock_prover.assert_satisfied();
    println!("{}", "Mock prover passes");

    // generates EVM verifier
    let srs: ParamsKZG<Bn256> = EvmVerifier::gen_srs(DEGREE);
    let pk = EvmVerifier::gen_pk(&srs, &circuit);
    let deployment_code = EvmVerifier::gen_evm_verifier(&srs, pk.get_vk(), vec![0]);

    // generates SNARK proof and runs EVM verifier
    println!("{}", "Starting finalization phase");
    let proof = EvmVerifier::gen_proof(&srs, &pk, circuit.clone(), vec![vec![]]);
    println!("{}", "SNARK proof generated successfully!");

    let calldata = encode_calldata::<Fr>(&[vec![]], &proof);

    let deployment_code_hex = "0x".to_string() + &hex::encode(deployment_code);
    let calldata_hex = "0x".to_string() + &hex::encode(calldata);
    let mut file = File::create("deployment_code.txt").unwrap();
    file.write_all(deployment_code_hex.as_bytes()).unwrap();
    let mut file = File::create("calldata.txt").unwrap();
    file.write_all(calldata_hex.as_bytes()).unwrap();
}
