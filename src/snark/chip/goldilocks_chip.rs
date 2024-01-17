use halo2_proofs::{arithmetic::Field, circuit::Value, plonk::Error};
use halo2curves::{goldilocks::fp::Goldilocks, FieldExt};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{big_to_fe, fe_to_big, AssignedCondition, AssignedValue};
use num_bigint::BigUint;
use num_traits::Num;

use super::native_chip::{
    arithmetic_chip::{ArithmeticChip, ArithmeticConfig},
    linear_chip::{LinearChip, LinearConfig},
    mod_chip::GOLDILOCKS_MODULUS,
};

#[derive(Clone, Debug)]
pub struct GoldilocksChipConfig<F: FieldExt> {
    pub arithmetic_config: ArithmeticConfig<F>,
    pub linear_config: LinearConfig<F>,
}

pub struct GoldilocksChip<F: FieldExt> {
    goldilocks_chip_config: GoldilocksChipConfig<F>,
}

impl<F: FieldExt> GoldilocksChip<F> {
    pub fn configure(
        arithmetic_config: &ArithmeticConfig<F>,
        linear_config: &LinearConfig<F>,
    ) -> GoldilocksChipConfig<F> {
        GoldilocksChipConfig {
            arithmetic_config: arithmetic_config.clone(),
            linear_config: linear_config.clone(),
        }
    }

    pub fn new(goldilocks_chip_config: &GoldilocksChipConfig<F>) -> Self {
        Self {
            goldilocks_chip_config: goldilocks_chip_config.clone(),
        }
    }

    fn arithmetic_chip(&self) -> ArithmeticChip<F> {
        ArithmeticChip::construct(self.goldilocks_chip_config.arithmetic_config.clone())
    }

    fn linear_chip(&self) -> LinearChip<F> {
        LinearChip::construct(self.goldilocks_chip_config.linear_config.clone())
    }

    pub fn goldilocks_modulus(&self) -> BigUint {
        BigUint::from_str_radix(&Goldilocks::MODULUS[2..], 16).unwrap()
    }

    pub fn goldilocks_to_native_fe(&self, goldilocks: Goldilocks) -> F {
        big_to_fe::<F>(fe_to_big::<Goldilocks>(goldilocks))
    }

    pub fn assign_value(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: Value<F>,
    ) -> Result<AssignedValue<F>, Error> {
        self.arithmetic_chip().assign_value(ctx, unassigned)
    }

    pub fn assign_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        constant: Goldilocks,
    ) -> Result<AssignedValue<F>, Error> {
        self.arithmetic_chip()
            .assign_fixed(ctx, constant.to_canonical_u64())
    }

    pub fn add(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        self.arithmetic_chip()
            .generic_add(ctx, 1, 0, lhs.clone(), rhs.clone())
    }

    pub fn sub(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        self.arithmetic_chip().sub(ctx, lhs.clone(), rhs.clone())
    }

    pub fn mul(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        self.mul_with_constant(ctx, lhs, rhs, Goldilocks::one())
    }

    /// Assigns a new witness `r` as:
    /// `lhs * rhs * constant - p * q - r = 0`
    pub fn mul_with_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
        constant: Goldilocks,
    ) -> Result<AssignedValue<F>, Error> {
        self.arithmetic_chip()
            .generic_mul(ctx, constant.0, 0, lhs.clone(), rhs.clone())
    }

    pub fn mul_add_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
        to_add: Goldilocks,
    ) -> Result<AssignedValue<F>, Error> {
        self.arithmetic_chip()
            .generic_mul(ctx, 1, to_add.0, a.clone(), b.clone())
    }

    pub fn add_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        constant: Goldilocks,
    ) -> Result<AssignedValue<F>, Error> {
        let zero = self.assign_constant(ctx, Goldilocks::zero())?;
        self.arithmetic_chip()
            .generic_add(ctx, 1, constant.0, a.clone(), zero)
    }

    pub fn assert_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<(), Error> {
        ctx.constrain_equal(lhs.cell(), rhs.cell())
    }

    pub fn assert_one(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
    ) -> Result<(), Error> {
        let one = self.assign_constant(ctx, Goldilocks::one())?;
        self.assert_equal(ctx, a, &one)
    }

    pub fn assert_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
    ) -> Result<(), Error> {
        let zero = self.assign_constant(ctx, Goldilocks::zero())?;
        self.assert_equal(ctx, a, &zero)
    }

    pub fn select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
        cond: &AssignedCondition<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let assigned = self.arithmetic_chip().select_two(
            ctx,
            cond.clone(),
            [a.clone(), a.clone()],
            [b.clone(), b.clone()],
        )?;
        Ok(assigned[0].clone())
    }

    pub fn is_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
    ) -> Result<AssignedCondition<F>, Error> {
        let b = a.value().map(|&v| {
            if v == F::zero() {
                F::zero()
            } else {
                v.invert().unwrap()
            }
        });
        let b_assigned = self.assign_value(ctx, b)?;
        let minus_one = GOLDILOCKS_MODULUS - 1;
        let r = self
            .arithmetic_chip()
            .generic_add(ctx, minus_one, 1, a.clone(), b_assigned)?;
        let should_zero = self.mul(ctx, &r, a)?;
        self.assert_zero(ctx, &should_zero)?;
        Ok(r)
    }

    /// Assigns array values of bit values which is equal to decomposition of
    /// given assigned value
    pub fn to_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        composed: &AssignedValue<F>,
        number_of_bits: usize,
    ) -> Result<Vec<AssignedCondition<F>>, Error> {
        assert!(number_of_bits <= 64);
        let bits = self.linear_chip().to_bits(ctx, composed.clone())?;
        Ok(bits[..number_of_bits].to_vec())
    }

    pub fn from_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &Vec<AssignedValue<F>>,
    ) -> Result<AssignedValue<F>, Error> {
        assert!(bits.len() <= 64);
        let mut bits = bits.to_vec();
        if bits.len() != 64 {
            let zero = self.assign_constant(ctx, Goldilocks::zero())?;
            bits.resize(64, zero);
        }
        self.linear_chip().from_bits(ctx, bits.try_into().unwrap())
    }

    pub fn exp_power_of_2(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        power_log: usize,
    ) -> Result<AssignedValue<F>, Error> {
        let mut result = a.clone();
        for _ in 0..power_log {
            result = self.mul(ctx, &result, &result)?;
        }
        Ok(result)
    }

    pub fn exp_from_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        base: Goldilocks,
        power_bits: &[AssignedValue<F>],
    ) -> Result<AssignedValue<F>, Error> {
        let mut x = self.assign_constant(ctx, Goldilocks::one())?;
        let one = self.assign_constant(ctx, Goldilocks::one())?;
        for (i, bit) in power_bits.iter().enumerate() {
            let is_zero_bit = self.is_zero(ctx, bit)?;
            let power = u64::from(1u64 << i).to_le();
            let base = self.assign_constant(ctx, base.pow(&[power, 0, 0, 0]))?;
            let multiplicand = self.select(ctx, &one, &base, &is_zero_bit)?;
            x = self.mul(ctx, &x, &multiplicand)?;
        }
        Ok(x)
    }

    pub fn is_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedCondition<F>, Error> {
        let a_mimus_b = self.sub(ctx, a, b)?;
        self.is_zero(ctx, &a_mimus_b)
    }
}

#[cfg(test)]
mod tests {

    use crate::snark::chip::goldilocks_chip::GoldilocksChipConfig;
    use crate::snark::chip::native_chip::arithmetic_chip::{ArithmeticChip, ArithmeticConfig};
    use crate::snark::chip::native_chip::linear_chip::LinearConfig;
    use crate::snark::chip::native_chip::utils::gf_to_fr;

    use halo2_proofs::circuit::{Layouter, Value};
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::{circuit::SimpleFloorPlanner, plonk::Circuit};
    use halo2wrong::RegionCtx;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::Sample;

    use super::GoldilocksChip;

    #[derive(Default)]
    pub struct TestCircuit {
        pub x: Fr,
        pub y: Fr,
        pub z: Fr,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = GoldilocksChipConfig<Fr>;

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
            let arithmetic_config = ArithmeticConfig::configure(meta);
            let linear_config = LinearConfig::configure(meta);
            GoldilocksChipConfig {
                arithmetic_config,
                linear_config,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<Fr>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            let goldilocks_chip = GoldilocksChip::new(&config);

            let mut layouter = layouter.namespace(|| "decompose");
            layouter.assign_region(
                || "value",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let _zero = goldilocks_chip.assign_value(&mut ctx, Value::known(Fr::zero()))?;
                    let _one = goldilocks_chip.assign_value(&mut ctx, Value::known(Fr::from(1)))?;

                    // goldilocks_chip.assert_equal(&mut ctx, &zero, &one)?;

                    // let y_value = self.y.map(|x| Value::known(x));
                    // let y_assigned =
                    //     goldilocks_extension_chip.assign_value_extension(&mut ctx, &y_value)?;
                    // let z_value = self.z.map(|x| Value::known(x));
                    // let z_assigned =
                    //     goldilocks_extension_chip.assign_value_extension(&mut ctx, &z_value)?;

                    // let a = Goldilocks::from(2);
                    // let b = Goldilocks::from(3);

                    // let output = goldilocks_extension_chip.arithmetic_extension(
                    //     &mut ctx,
                    //     a,
                    //     b,
                    //     &x_assigned,
                    //     &y_assigned,
                    //     &z_assigned,
                    // )?;
                    // let expected = {
                    //     let x = fr2_to_gfe(self.x);
                    //     let y = fr2_to_gfe(self.y);
                    //     let z = fr2_to_gfe(self.z);
                    //     let a =
                    //         <GoldilocksField as Extendable<2>>::Extension::from_canonical_u64(a.0);
                    //     let b =
                    //         <GoldilocksField as Extendable<2>>::Extension::from_canonical_u64(b.0);
                    //     gfe_to_fr(a)
                    // };
                    // let expected_assigned = goldilocks_extension_chip
                    //     .assign_value_extension(&mut ctx, &expected.map(|x| Value::known(x)))?;
                    // goldilocks_extension_chip.assert_equal_extension(
                    //     &mut ctx,
                    //     &output,
                    //     &expected_assigned,
                    // )?;

                    Ok(())
                },
            )?;
            let arithmetic_chip = ArithmeticChip::construct(config.arithmetic_config);
            arithmetic_chip.load_table(&mut layouter)?;
            Ok(())
        }
    }

    #[test]
    fn test_goldilocks_chip() {
        let x = GoldilocksField::rand();
        let x = gf_to_fr(x);
        let y = GoldilocksField::rand();
        let y = gf_to_fr(y);
        let z = GoldilocksField::rand();
        let z = gf_to_fr(z);
        let circuit = TestCircuit { x, y, z };
        MockProver::run(17, &circuit, vec![vec![]])
            .unwrap()
            .assert_satisfied();
    }
}
