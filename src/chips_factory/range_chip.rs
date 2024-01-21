use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{decompose, fe_to_big};
use num_bigint::BigUint;

pub const RANGE_CHIP_NUM_BITS: usize = 16;
pub const RANGE_CHIP_NUM_LIMBS: usize = 5;
pub const RANGE_CHIP_MAX_BITS: usize = RANGE_CHIP_NUM_BITS * RANGE_CHIP_NUM_LIMBS;

#[derive(Clone, Debug)]
pub struct RangeChipConfig<F: FieldExt> {
    pub target: Column<Advice>,
    pub limbs: [Column<Advice>; RANGE_CHIP_NUM_LIMBS],
    pub selector: Selector,
    pub table: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RangeChipConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let target = meta.advice_column();
        let limbs = [(); RANGE_CHIP_NUM_LIMBS].map(|_| meta.advice_column());
        let selector = meta.selector();
        let table = meta.lookup_table_column();
        meta.enable_equality(target);
        limbs.iter().for_each(|limb| meta.enable_equality(*limb));

        // check that 0<= target < 2^MAX_BITS
        meta.create_gate("range chip: limb decompose", |meta| {
            let s = meta.query_selector(selector);
            let target = meta.query_advice(target, Rotation::cur());
            let limbs = limbs
                .map(|l| meta.query_advice(l, Rotation::cur()))
                .to_vec();
            let acc = (0..RANGE_CHIP_NUM_LIMBS).fold(Expression::Constant(F::zero()), |acc, i| {
                acc + limbs[i].clone()
                    * Expression::Constant(F::from(1 << (RANGE_CHIP_NUM_BITS * i)))
            });
            let diff = acc - target;
            vec![s * diff]
        });
        limbs.iter().for_each(|limb| {
            meta.lookup("range chip: limbs range check", |meta| {
                let l = meta.query_advice(*limb, Rotation::cur());
                vec![(l, table)]
            });
        });

        RangeChipConfig {
            target,
            limbs,
            selector,
            table,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct RangeChip<F: FieldExt> {
    config: RangeChipConfig<F>,
}

impl<F: FieldExt> RangeChip<F> {
    pub fn new(config: &RangeChipConfig<F>) -> Self {
        Self {
            config: config.clone(),
        }
    }

    pub fn assign_decompose_no_next(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: Value<F>,
    ) -> Result<
        (
            AssignedCell<F, F>,
            [AssignedCell<F, F>; RANGE_CHIP_NUM_LIMBS],
        ),
        Error,
    > {
        unassigned.assert_if_known(|x| {
            fe_to_big(*x) < BigUint::from(2usize).pow(RANGE_CHIP_MAX_BITS as u32)
        });
        ctx.enable(self.config.selector)?;
        let target = ctx.assign_advice(|| "target", self.config.target, unassigned)?;
        let limbs = unassigned
            .map(|x| decompose(x, RANGE_CHIP_NUM_LIMBS, RANGE_CHIP_NUM_BITS))
            .transpose_vec(RANGE_CHIP_NUM_LIMBS);
        let limbs_assigned = self
            .config
            .limbs
            .iter()
            .zip(limbs.iter())
            .map(|(limb, &limb_value)| {
                let limb = ctx.assign_advice(|| "limb", *limb, limb_value)?;
                Ok(limb)
            })
            .collect::<Result<Vec<_>, Error>>()?;
        Ok((target, limbs_assigned.try_into().unwrap()))
    }

    pub fn decompose(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedCell<F, F>,
    ) -> Result<[AssignedCell<F, F>; RANGE_CHIP_NUM_LIMBS], Error> {
        let (target, limbs) = self.assign_decompose_no_next(ctx, x.value().cloned())?;
        ctx.constrain_equal(x.cell(), target.cell())?;
        ctx.next();
        Ok(limbs)
    }

    pub fn load_table(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        layouter.assign_table(
            || "range table",
            |mut table| {
                for offset in 0..1 << RANGE_CHIP_NUM_BITS {
                    table.assign_cell(
                        || "value",
                        self.config.table,
                        offset,
                        || Value::known(F::from(offset as u64)),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::arithmetic::Field;
    use halo2_proofs::circuit::{Layouter, Value};
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::{circuit::SimpleFloorPlanner, plonk::Circuit};
    use halo2curves::goldilocks::fp::Goldilocks;
    use halo2wrong::RegionCtx;

    use super::{RangeChip, RangeChipConfig};

    #[derive(Default, Clone)]
    struct TestCircuit;

    impl Circuit<Fr> for TestCircuit {
        type Config = RangeChipConfig<Fr>;

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
            RangeChipConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<Fr>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            let range_chip = RangeChip::new(&config);
            range_chip.load_table(&mut layouter)?;
            let mut layouter = layouter.namespace(|| "bit decompose");
            layouter.assign_region(
                || "value",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);
                    let (_target, _limbs) = range_chip.assign_decompose_no_next(
                        &mut ctx,
                        Value::known(Fr::from((-Goldilocks::one()).to_canonical_u64())),
                    )?;
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_range_chip() {
        const DEGREE: u32 = 17;

        let circuit = TestCircuit;
        MockProver::run(DEGREE, &circuit, vec![])
            .unwrap()
            .assert_satisfied();
    }
}
