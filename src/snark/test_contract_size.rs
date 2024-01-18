use halo2_proofs::{
    circuit::{floor_planner::V1, Layouter, Value},
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fr},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::{kzg::commitment::ParamsKZG, Rotation},
};
use halo2curves::FieldExt;
use halo2wrong::RegionCtx;
use halo2wrong_maingate::AssignedValue;
use snark_verifier::loader::evm::encode_calldata;

use crate::snark::verifier_api::EvmVerifier;

#[derive(Clone, Debug)]
pub struct SquareChipConfig<F: FieldExt> {
    pub s: Selector,
    pub x: Column<Advice>,
    pub y: Column<Advice>,
    pub i: Column<Instance>,
    _maker: std::marker::PhantomData<F>,
}

impl<F: FieldExt> SquareChipConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let x = meta.advice_column();
        let y = meta.advice_column();
        let s = meta.selector();
        let i = meta.instance_column();
        meta.enable_equality(x);
        meta.enable_equality(y);
        meta.create_gate("square zip", |meta| {
            let x = meta.query_advice(x, Rotation::cur());
            let y = meta.query_advice(y, Rotation::cur());
            let s = meta.query_selector(s);
            vec![s * (x.clone() * x.clone() - y)]
        });

        Self {
            i,
            s,
            x,
            y,
            _maker: std::marker::PhantomData,
        }
    }
}

pub struct SquareChip<F: FieldExt> {
    pub config: SquareChipConfig<F>,
}

impl<F: FieldExt> SquareChip<F> {
    pub fn new(config: &SquareChipConfig<F>) -> Self {
        Self {
            config: config.clone(),
        }
    }

    pub fn assign(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: Value<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let assigned = ctx.assign_advice(|| "x", self.config.x, unassigned)?;
        ctx.next();
        Ok(assigned)
    }

    pub fn square(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let x_value = x.value().cloned();
        ctx.enable(self.config.s)?;
        let x_assigned = ctx.assign_advice(|| "x", self.config.x, x_value)?;
        let y_assigened = ctx.assign_advice(|| "y", self.config.y, x_value * x_value)?;
        ctx.constrain_equal(x.cell(), x_assigned.cell())?;
        ctx.next();
        Ok(y_assigened)
    }
}

#[derive(Clone, Default)]
pub struct TestCircuit;

impl Circuit<Fr> for TestCircuit {
    type Config = SquareChipConfig<Fr>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        SquareChipConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let chip = SquareChip::new(&config);

        layouter.assign_region(
            || "Verify proof",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let x = chip.assign(ctx, Value::known(Fr::one()))?;
                let _y = chip.square(ctx, &x)?;

                Ok(())
            },
        )?;
        Ok(())
    }
}

const DEGREE: u32 = 8;

#[test]
fn test_contract_compile() {
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
