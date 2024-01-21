use std::collections::HashMap;

use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
use halo2curves::FieldExt;
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{big_to_fe, fe_to_big};
use num_bigint::BigUint;
use num_integer::Integer;

use super::range_chip::{RangeChip, RangeChipConfig};

const NUM_VARS: usize = 4;
pub const GOLDILOCKS_MODULUS: u64 = ((1 << 32) - 1) * (1 << 32) + 1;

/// consraints \sum_i a_i * b_i = c
#[derive(Clone, Debug)]
pub struct ArithmeticChipConfig<F: FieldExt> {
    pub a: [Column<Advice>; NUM_VARS],
    pub b: [Column<Advice>; NUM_VARS],
    pub c: Column<Advice>,
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

        a.iter().for_each(|x| meta.enable_equality(*x));
        b.iter().for_each(|x| meta.enable_equality(*x));
        meta.enable_equality(c);
        meta.enable_equality(constant);

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
    pub fn assign_take_mod_lazy(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        a: [Value<F>; NUM_VARS],
        b: [Value<F>; NUM_VARS],
    ) -> Result<AssignedArithmetic<F>, Error> {
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
        let range_chip = RangeChip::new(&self.config.range_chip_config);
        let modulus = Value::known(F::from(GOLDILOCKS_MODULUS));
        let zero = Value::known(F::zero());
        let one = Value::known(F::one());
        let mul_add_assigned =
            self.assign_no_next(ctx, [m, r, zero, zero], [modulus, one, zero, zero])?; // c = m * modulus + r
        let (m_assigned, _m_limbs_assigned) = range_chip.assign_decompose_no_next(ctx, m)?;
        ctx.constrain_equal(m_assigned.cell(), mul_add_assigned.a[0].cell())?;
        let r_assigned = mul_add_assigned.a[1].clone();
        self.assert_constant(ctx, &mul_add_assigned.a[2], 0)?;
        self.assert_constant(ctx, &mul_add_assigned.a[3], 0)?;
        self.assert_constant(ctx, &mul_add_assigned.b[0], GOLDILOCKS_MODULUS)?;
        self.assert_constant(ctx, &mul_add_assigned.b[1], 1)?;
        self.assert_constant(ctx, &mul_add_assigned.b[2], 0)?;
        self.assert_constant(ctx, &mul_add_assigned.b[3], 0)?;
        ctx.next();
        let r_limbs_assigned = range_chip.decompose(ctx, &r_assigned)?;
        self.assert_constant(ctx, &r_limbs_assigned[4], 0)?; // r[4] = 0
        Ok(abc_assigned)
    }

    pub fn take_mod_lazy(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        a: [AssignedCell<F, F>; NUM_VARS],
        b: [AssignedCell<F, F>; NUM_VARS],
    ) -> Result<AssignedCell<F, F>, Error> {
        let assigned = self.assign_take_mod_lazy(
            ctx,
            a.clone().map(|x| x.value().cloned()),
            b.clone().map(|x| x.value().cloned()),
        )?;
        for i in 0..NUM_VARS {
            ctx.constrain_equal(assigned.a[i].cell(), a[i].cell())?;
            ctx.constrain_equal(assigned.b[i].cell(), b[i].cell())?;
        }
        Ok(assigned.c)
    }

    // pub fn assign(
    //     &mut self,
    //     meta: &mut ConstraintSystem<F>,
    //     a: [F; NUM_VARS],
    //     b: [F; NUM_VARS],
    //     c: F,
    // ) {
    //     let config = &self.config;
    //     let a = a.map(|x| self.assign_constant(meta, x));
    //     let b = b.map(|x| self.assign_constant(meta, x));
    //     let c = self.assign_constant(meta, c);
    //     meta.assign_advice(|| "a", config.a[0], 0, || Ok(a[0].value))
    //         .unwrap();
    //     meta.assign_advice(|| "a", config.a[1], 0, || Ok(a[1].value))
    //         .unwrap();
    //     meta.assign_advice(|| "a", config.a[2], 0, || Ok(a[2].value))
    //         .unwrap();
    //     meta.assign_advice(|| "a", config.a[3], 0, || Ok(a[3].value))
    //         .unwrap();
    //     meta.assign_advice(|| "b", config.b[0], 0, || Ok(b[0].value))
    //         .unwrap();
    //     meta.assign_advice(|| "b", config.b[1], 0, || Ok(b[1].value))
    //         .unwrap();
    //     meta.assign_advice(|| "b", config.b[2], 0, || Ok(b[2].value))
    //         .unwrap();
    //     meta.assign_advice(|| "b", config.b[3], 0, || Ok(b[3].value))
    //         .unwrap();
    //     meta.assign_advice(|| "c", config.c, 0, || Ok(c.value))
    //         .unwrap();
    // }
}
