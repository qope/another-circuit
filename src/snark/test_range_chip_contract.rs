use std::{fs::File, io::Write};

use halo2_proofs::{
    circuit::{floor_planner::V1, Layouter, Value},
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fr},
    plonk::{Circuit, ConstraintSystem, Error},
    poly::kzg::commitment::ParamsKZG,
};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{MainGate, RangeChip, RangeConfig, RangeInstructions};
use snark_verifier::loader::evm::encode_calldata;

use crate::snark::verifier_api::EvmVerifier;

#[derive(Clone, Default)]
pub struct TestCircuit;

impl Circuit<Fr> for TestCircuit {
    type Config = RangeConfig;

    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let main_gate_config = MainGate::configure(meta);
        RangeChip::configure(meta, &main_gate_config, vec![16], vec![0, 1])
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let chip = RangeChip::new(config.clone());

        layouter.assign_region(
            || "mod contract",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let _x = chip.decompose(ctx, Value::known(Fr::from(3)), 16, 64)?;
                let _x = chip.decompose(ctx, Value::known(Fr::from(3)), 16, 65)?;
                Ok(())
            },
        )?;
        chip.load_table(&mut layouter)?;
        Ok(())
    }
}

const DEGREE: u32 = 22;

#[test]
fn test_range_contract() {
    let circuit = TestCircuit;
    let instance = Vec::<Fr>::new();
    let mock_prover = MockProver::run(DEGREE, &circuit, vec![instance.clone()]).unwrap();
    mock_prover.assert_satisfied();
    println!("{}", "Mock prover passes");

    // generates EVM verifier
    let srs: ParamsKZG<Bn256> = EvmVerifier::gen_srs(DEGREE);
    let pk = EvmVerifier::gen_pk(&srs, &circuit);
    let deployment_code = EvmVerifier::gen_evm_verifier(&srs, pk.get_vk(), vec![instance.len()]);

    // generates SNARK proof and runs EVM verifier
    println!("{}", "Starting finalization phase");
    let proof = EvmVerifier::gen_proof(&srs, &pk, circuit.clone(), vec![instance.clone()]);
    println!("{}", "SNARK proof generated successfully!");

    let calldata = encode_calldata::<Fr>(&[instance], &proof);
    let deployment_code_hex = "0x".to_string() + &hex::encode(deployment_code);
    let calldata_hex = "0x".to_string() + &hex::encode(calldata);
    let mut file = File::create("deployment_code.txt").unwrap();
    file.write_all(deployment_code_hex.as_bytes()).unwrap();
    let mut file = File::create("calldata.txt").unwrap();
    file.write_all(calldata_hex.as_bytes()).unwrap();
}
