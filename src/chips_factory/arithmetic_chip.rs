use std::collections::HashMap;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector},
    poly::Rotation,
};
use halo2curves::FieldExt;
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{big_to_fe, fe_to_big, AssignedValue};
use num_bigint::BigUint;
use num_integer::Integer;

use super::range_chip::{RangeChip, RangeChipConfig};

const NUM_VARS: usize = 2;
pub const GOLDILOCKS_MODULUS: u64 = ((1 << 32) - 1) * (1 << 32) + 1;

#[derive(Clone)]
pub enum Term<F: FieldExt> {
    /// Assigned value
    Assigned(AssignedValue<F>),
    /// Unassigned witness
    Unassigned(Value<F>),
    /// Unassigned fixed value
    UnassignedFixed(F),
}

/// consraints \sum_i a_i * b_i = c
#[derive(Clone, Debug)]
pub struct ArithmeticChipConfig<F: FieldExt> {
    pub a: [Column<Advice>; NUM_VARS],
    pub b: [Column<Advice>; NUM_VARS],
    pub c: Column<Advice>,
    pub instance: Column<Instance>,
    pub constant: Column<Fixed>,
    pub selector: Selector,
    pub range_chip_config: RangeChipConfig<F>,
}

impl<F: FieldExt> ArithmeticChipConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let a = [(); NUM_VARS].map(|_| meta.advice_column());
        let b = [(); NUM_VARS].map(|_| meta.advice_column());
        let c = meta.advice_column();
        let constant = meta.fixed_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        a.iter().for_each(|x| meta.enable_equality(*x));
        b.iter().for_each(|x| meta.enable_equality(*x));
        meta.enable_equality(c);
        meta.enable_equality(constant);
        meta.enable_equality(instance);

        meta.create_gate("arithmetic gate", |meta| {
            let s = meta.query_selector(selector);
            let a = a.map(|x| meta.query_advice(x, Rotation::cur())).to_vec();
            let b = b.map(|x| meta.query_advice(x, Rotation::cur())).to_vec();
            let c = meta.query_advice(c, Rotation::cur());
            let acc = a
                .iter()
                .zip(b.iter())
                .fold(Expression::Constant(F::zero()), |acc, (a, b)| {
                    acc + a.clone() * b.clone()
                });
            let diff = acc - c;
            vec![s * diff]
        });

        let range_chip_config = RangeChipConfig::configure(meta);

        ArithmeticChipConfig {
            a,
            b,
            c,
            instance,
            constant,
            selector,
            range_chip_config,
        }
    }
}

pub struct AssignedArithmetic<F: FieldExt> {
    pub a: [AssignedCell<F, F>; NUM_VARS],
    pub b: [AssignedCell<F, F>; NUM_VARS],
    pub c: AssignedCell<F, F>,
}

impl<F: FieldExt> AssignedArithmetic<F> {
    pub fn connect(&self, ctx: &mut RegionCtx<'_, F>, other: &Self) -> Result<(), Error> {
        for i in 0..NUM_VARS {
            ctx.constrain_equal(self.a[i].cell(), other.a[i].cell())?;
            ctx.constrain_equal(self.b[i].cell(), other.b[i].cell())?;
        }
        ctx.constrain_equal(self.c.cell(), other.c.cell())?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct ArithmeticChip<F: FieldExt> {
    config: ArithmeticChipConfig<F>,
    assigned_constants: HashMap<u64, AssignedCell<F, F>>,
}

impl<F: FieldExt> ArithmeticChip<F> {
    pub fn new(
        config: &ArithmeticChipConfig<F>,
        assigned_constants: &HashMap<u64, AssignedCell<F, F>>,
    ) -> Self {
        Self {
            config: config.clone(),
            assigned_constants: assigned_constants.clone(),
        }
    }

    pub fn load_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let range_chip = RangeChip::new(&self.config.range_chip_config);
        range_chip.load_table(layouter)?;
        Ok(())
    }

    pub fn assign_constant(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        constant: u64,
    ) -> Result<AssignedCell<F, F>, Error> {
        if let Some(cell) = self.assigned_constants.get(&constant) {
            return Ok(cell.clone());
        }
        let cell = ctx.assign_fixed(|| "constant", self.config.constant, F::from(constant))?;
        ctx.next();
        self.assigned_constants.insert(constant, cell.clone());
        Ok(cell)
    }

    pub fn assert_constant(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        cell: &AssignedCell<F, F>,
        constant: u64,
    ) -> Result<(), Error> {
        let constant = self.assign_constant(ctx, constant)?;
        ctx.constrain_equal(cell.cell(), constant.cell())?;
        Ok(())
    }

    pub fn assert_equal(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<(), Error> {
        ctx.constrain_equal(a.cell(), b.cell())?;
        Ok(())
    }

    pub fn assign_no_next(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        a: [Value<F>; NUM_VARS],
        b: [Value<F>; NUM_VARS],
    ) -> Result<AssignedArithmetic<F>, Error> {
        ctx.enable(self.config.selector)?;
        let config = &self.config;
        let a_assigned = config
            .a
            .iter()
            .zip(a.iter())
            .map(|(col, val)| ctx.assign_advice(|| "assign", *col, *val))
            .collect::<Result<Vec<_>, Error>>()?;
        let b_assigned = config
            .b
            .iter()
            .zip(b.iter())
            .map(|(col, val)| ctx.assign_advice(|| "assign", *col, *val))
            .collect::<Result<Vec<_>, Error>>()?;
        let c_val = a
            .iter()
            .zip(b.iter())
            .fold(Value::known(F::zero()), |acc, (a, b)| {
                acc + a.clone() * b.clone()
            });
        let c_assigned = ctx.assign_advice(|| "c", config.c, c_val)?;
        Ok(AssignedArithmetic {
            a: a_assigned.try_into().unwrap(),
            b: b_assigned.try_into().unwrap(),
            c: c_assigned,
        })
    }

    pub fn constrain_no_next(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        a: [AssignedCell<F, F>; NUM_VARS],
        b: [AssignedCell<F, F>; NUM_VARS],
    ) -> Result<AssignedCell<F, F>, Error> {
        let a_val = a.clone().map(|x| x.value().cloned());
        let b_val = b.clone().map(|x| x.value().cloned());
        let assigned = self.assign_no_next(ctx, a_val, b_val)?;
        for i in 0..NUM_VARS {
            ctx.constrain_equal(assigned.a[i].cell(), a[i].cell())?;
            ctx.constrain_equal(assigned.b[i].cell(), b[i].cell())?;
        }
        Ok(assigned.c)
    }

    // Compute c = \sum a*b mod p, ensuring c is 64bit number, but do not check if c < p.
    // this consumes 2 rows.
    pub fn assign_take_mod_loose(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        a: [Value<F>; NUM_VARS],
        b: [Value<F>; NUM_VARS],
    ) -> Result<AssignedArithmetic<F>, Error> {
        // assign constants to avoid unwanted ctx.next()
        // let _zero = self.assign_constant(ctx, 0)?;
        // let _one = self.assign_constant(ctx, 1)?;
        // let _modulus = self.assign_constant(ctx, GOLDILOCKS_MODULUS)?;
        let range_chip = RangeChip::new(&self.config.range_chip_config);

        // the first row
        let abc_assigned = self.assign_no_next(ctx, a, b)?;
        let (m, r) = abc_assigned
            .c
            .value()
            .map(|&c| {
                let c = fe_to_big(c);
                let (m, r) = c.div_rem(&BigUint::from(GOLDILOCKS_MODULUS));
                let m = big_to_fe::<F>(m);
                let r = big_to_fe::<F>(r);
                (m, r)
            })
            .unzip();
        let (m_assigned, _m_limbs_assigned) = range_chip.assign_decompose_no_next(ctx, m)?;
        ctx.next();

        // the second row
        let modulus = Value::known(F::from(GOLDILOCKS_MODULUS));
        let zero = Value::known(F::zero());
        let one = Value::known(F::one());

        let mut a = vec![m, r];
        a.resize(NUM_VARS, zero);
        let mut b = vec![modulus, one];
        b.resize(NUM_VARS, zero);
        let mul_add_assigned =
            self.assign_no_next(ctx, a.try_into().unwrap(), b.try_into().unwrap())?; // c = m * modulus + r
        ctx.constrain_equal(m_assigned.cell(), mul_add_assigned.a[0].cell())?;
        let r_assigned = mul_add_assigned.a[1].clone();
        self.assert_constant(ctx, &mul_add_assigned.a[2], 0)?;
        self.assert_constant(ctx, &mul_add_assigned.a[3], 0)?;
        self.assert_constant(ctx, &mul_add_assigned.b[0], GOLDILOCKS_MODULUS)?;
        self.assert_constant(ctx, &mul_add_assigned.b[1], 1)?;
        self.assert_constant(ctx, &mul_add_assigned.b[2], 0)?;
        self.assert_constant(ctx, &mul_add_assigned.b[3], 0)?;
        let r_limbs_assigned = range_chip.decompose(ctx, &r_assigned)?;
        self.assert_constant(ctx, &r_limbs_assigned[4], 0)?;

        Ok(abc_assigned)
    }

    pub fn take_mod_loose(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        a: [AssignedCell<F, F>; NUM_VARS],
        b: [AssignedCell<F, F>; NUM_VARS],
    ) -> Result<AssignedCell<F, F>, Error> {
        let assigned = self.assign_take_mod_loose(
            ctx,
            a.clone().map(|x| x.value().cloned()),
            b.clone().map(|x| x.value().cloned()),
        )?;
        for i in 0..NUM_VARS {
            self.assert_equal(ctx, &assigned.a[i], &a[i])?;
            self.assert_equal(ctx, &assigned.b[i], &b[i])?;
        }
        Ok(assigned.c)
    }

    // pub fn assign_take_mod_strict(
    //     &mut self,
    //     ctx: &mut RegionCtx<'_, F>,
    //     a: [Value<F>; NUM_VARS],
    //     b: [Value<F>; NUM_VARS],
    // ) -> Result<AssignedArithmetic<F>, Error> {
    //     let assigned = self.assign_take_mod_loose(ctx, a, b)?;
    //     let range_chip = RangeChip::new(&self.config.range_chip_config);

    //     let c = assigned.c.clone();
    //     let modulus = Value::known(F::from(GOLDILOCKS_MODULUS));
    //     let diff = modulus.clone() - c.value().cloned();
    //     let (diff_assigned, diff_limbs_assigned) =
    //         range_chip.assign_decompose_no_next(ctx, diff)?;

    //     let (c_loose, c_limbs) = range_chip.assign_decompose_no_next(ctx, c.value().cloned())?;

    //     Ok(c_loose)
    // }

    pub fn assign_with_loose_range_check(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let range_chip = RangeChip::new(&self.config.range_chip_config);
        let (assigned, assigned_limbs) = range_chip.assign_decompose_no_next(ctx, unassigned)?;
        ctx.next();
        self.assert_constant(ctx, &assigned_limbs[4], 0)?;
        Ok(assigned)
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, fs::File, io::Write};

    use halo2_proofs::{
        circuit::{floor_planner::V1, Layouter},
        dev::MockProver,
        halo2curves::bn256::{Bn256, Fr},
        plonk::{Circuit, ConstraintSystem, Error},
        poly::kzg::commitment::ParamsKZG,
    };
    use halo2wrong::RegionCtx;
    use snark_verifier::loader::evm::encode_calldata;

    use crate::snark::verifier_api::EvmVerifier;

    use super::{ArithmeticChip, ArithmeticChipConfig};

    #[derive(Clone, Default)]
    pub struct TestCircuit;

    impl Circuit<Fr> for TestCircuit {
        type Config = ArithmeticChipConfig<Fr>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            ArithmeticChipConfig::<Fr>::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let chip = ArithmeticChip::new(&config, &HashMap::new());

            layouter.assign_region(
                || "Verify proof",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    // let x = chip.assign_value(ctx, Value::known(Fr::from(2)))?;
                    // let y = chip.assign_value(ctx, Value::known(Fr::from(2)))?;

                    // let _z = chip.generic_mul(ctx, 1, 0, x, y)?;

                    Ok(())
                },
            )?;
            chip.load_table(&mut layouter)?;
            Ok(())
        }
    }

    #[test]
    fn test_new_arithmetic_contract() {
        const DEGREE: u32 = 17;

        let circuit = TestCircuit;
        let instance = vec![];
        let mock_prover = MockProver::run(DEGREE, &circuit, vec![instance.clone()]).unwrap();
        mock_prover.assert_satisfied();
        println!("{}", "Mock prover passes");

        // // generates EVM verifier
        let srs: ParamsKZG<Bn256> = EvmVerifier::gen_srs(DEGREE);
        let pk = EvmVerifier::gen_pk(&srs, &circuit);
        let deployment_code =
            EvmVerifier::gen_evm_verifier(&srs, pk.get_vk(), vec![instance.len()]);

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
}
