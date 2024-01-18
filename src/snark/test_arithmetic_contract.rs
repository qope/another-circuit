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

use super::chip::native_chip::arithmetic_chip::{ArithmeticChip, ArithmeticConfig};

#[derive(Clone, Default)]
pub struct TestCircuit;

impl Circuit<Fr> for TestCircuit {
    type Config = ArithmeticConfig<Fr>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        ArithmeticConfig::<Fr>::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let chip = ArithmeticChip::construct(config.clone());

        layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let x = chip.assign_value(ctx, Value::known(Fr::from(2)))?;
                let y = chip.assign_value(ctx, Value::known(Fr::from(2)))?;

                let _z = chip.generic_mul(ctx, 1, 0, x, y)?;

                Ok(())
            },
        )?;
        chip.load_table(&mut layouter)?;
        Ok(())
    }
}

const DEGREE: u32 = 17;

#[test]
fn test_arithmetic_contract() {
    let circuit = TestCircuit;
    let mock_prover = MockProver::run(DEGREE, &circuit, vec![vec![]]).unwrap();
    mock_prover.assert_satisfied();
    println!("{}", "Mock prover passes");

    // generates EVM verifier
    let srs: ParamsKZG<Bn256> = EvmVerifier::gen_srs(DEGREE);
    let pk = EvmVerifier::gen_pk(&srs, &circuit);
    let _deployment_code = EvmVerifier::gen_evm_verifier(&srs, pk.get_vk(), vec![0]);

    // generates SNARK proof and runs EVM verifier
    println!("{}", "Starting finalization phase");
    let proof = EvmVerifier::gen_proof(&srs, &pk, circuit.clone(), vec![vec![]]);
    println!("{}", "SNARK proof generated successfully!");

    let _calldata = encode_calldata::<Fr>(&[vec![]], &proof);
}
