use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::Value;
use halo2_proofs::plonk::Error;
use halo2curves::{goldilocks::fp::Goldilocks, FieldExt};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::AssignedValue;

use crate::snark::types::assigned::AssignedExtensionFieldValue;

use super::goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig};
use super::native_chip::arithmetic_chip::ArithmeticChip;
use super::native_chip::utils::assigned_ext_div;

pub struct AssignedExtensionAlgebra<F: FieldExt>(pub [AssignedExtensionFieldValue<F, 2>; 2]);

pub struct GoldilocksExtensionChip<F: FieldExt> {
    goldilocks_chip_config: GoldilocksChipConfig<F>,
}

impl<F: FieldExt> GoldilocksExtensionChip<F> {
    pub fn new(goldilocks_chip_config: &GoldilocksChipConfig<F>) -> Self {
        Self {
            goldilocks_chip_config: goldilocks_chip_config.clone(),
        }
    }

    pub fn arithmetic_chip(&self) -> ArithmeticChip<F> {
        ArithmeticChip::construct(self.goldilocks_chip_config.arithmetic_config.clone())
    }

    pub fn goldilocks_chip(&self) -> GoldilocksChip<F> {
        GoldilocksChip::new(&self.goldilocks_chip_config)
    }

    pub fn w() -> Goldilocks {
        Goldilocks::from(7)
    }
}

// Layouts Goldilocks quadratic extension field arithmetic constraints
impl<F: FieldExt> GoldilocksExtensionChip<F> {
    pub fn mul(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedExtensionFieldValue<F, 2>,
        rhs: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let z = self.arithmetic_chip().generic_mul_ext(
            ctx,
            [1, 0],
            [0, 0],
            lhs.0.clone(),
            rhs.0.clone(),
        )?;
        Ok(AssignedExtensionFieldValue(z))
    }

    fn assign_value_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: &[Value<F>; 2],
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let z = self
            .arithmetic_chip()
            .assign_value_ext(ctx, unassigned.clone())?;
        Ok(AssignedExtensionFieldValue(z))
    }

    pub fn div_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedExtensionFieldValue<F, 2>,
        y: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        y.0[0]
            .value()
            .zip(y.0[1].value())
            .map(|(a, b)| assert!(*a != F::zero() || *b != F::zero()));
        let x_div_y = assigned_ext_div(x.0.clone(), y.0.clone());
        let x_div_y_assigned = self.assign_value_extension(ctx, &x_div_y)?;
        let one = self.one_extension(ctx)?;
        let output = self.mul_extension(ctx, &x_div_y_assigned, &y)?;
        self.assert_equal_extension(ctx, &output, &one)?;
        Ok(x_div_y_assigned)
    }

    pub fn div_add_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedExtensionFieldValue<F, 2>,
        y: &AssignedExtensionFieldValue<F, 2>,
        z: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let x_div_y = self.div_extension(ctx, x, y)?;
        self.add_extension(ctx, &x_div_y, z)
    }

    pub fn add_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        addend_0: &AssignedExtensionFieldValue<F, 2>,
        addend_1: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let z = self.arithmetic_chip().generic_add_ext(
            ctx,
            [1, 0],
            [0, 0],
            addend_0.0.clone(),
            addend_1.0.clone(),
        )?;
        Ok(AssignedExtensionFieldValue(z))
    }

    pub fn scalar_mul(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        multiplicand: &AssignedExtensionFieldValue<F, 2>,
        scalar: Goldilocks,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let one = self.one_extension(ctx)?;
        let z = self.arithmetic_chip().generic_mul_ext(
            ctx,
            [scalar.to_canonical_u64(), 0],
            [0, 0],
            multiplicand.0.clone(),
            one.0.clone(),
        )?;
        Ok(AssignedExtensionFieldValue(z))
    }

    /// const_0 * multiplicand_0 * multiplicand_1 + const_1 * addend
    pub fn arithmetic_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        const_0: Goldilocks,
        const_1: Goldilocks,
        multiplicand_0: &AssignedExtensionFieldValue<F, 2>,
        multiplicand_1: &AssignedExtensionFieldValue<F, 2>,
        addend: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let z = self.arithmetic_chip().generic_mul_add_ext(
            ctx,
            [const_0.to_canonical_u64(), 0],
            [const_1.to_canonical_u64(), 0],
            [0, 0],
            multiplicand_0.0.clone(),
            multiplicand_1.0.clone(),
            addend.0.clone(),
        )?;
        Ok(AssignedExtensionFieldValue(z))
    }

    pub fn zero_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        self.constant_extension(ctx, &[Goldilocks::zero(), Goldilocks::zero()])
    }

    pub fn one_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        self.constant_extension(ctx, &[Goldilocks::one(), Goldilocks::zero()])
    }

    pub fn two_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        self.constant_extension(ctx, &[Goldilocks::from(2), Goldilocks::zero()])
    }

    pub fn mul_extension_with_const(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        const_0: Goldilocks,
        multiplicand_0: &AssignedExtensionFieldValue<F, 2>,
        multiplicand_1: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let zero = self.zero_extension(ctx)?;
        self.arithmetic_extension(
            ctx,
            const_0,
            Goldilocks::zero(),
            multiplicand_0,
            multiplicand_1,
            &zero,
        )
    }

    pub fn mul_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        multiplicand_0: &AssignedExtensionFieldValue<F, 2>,
        multiplicand_1: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        self.mul_extension_with_const(ctx, Goldilocks::one(), multiplicand_0, multiplicand_1)
    }

    pub fn mul_add_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedExtensionFieldValue<F, 2>,
        b: &AssignedExtensionFieldValue<F, 2>,
        c: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let one = Goldilocks::one();
        self.arithmetic_extension(ctx, one, one, a, b, c)
    }

    pub fn mul_sub_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedExtensionFieldValue<F, 2>,
        b: &AssignedExtensionFieldValue<F, 2>,
        c: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let one = Goldilocks::one();
        self.arithmetic_extension(ctx, one, -one, a, b, c)
    }

    pub fn square_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        self.mul_extension(ctx, x, x)
    }

    pub fn exp_power_of_2_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        mut base: AssignedExtensionFieldValue<F, 2>,
        power_log: usize,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        for _ in 0..power_log {
            base = self.square_extension(ctx, &base)?;
        }
        Ok(base)
    }

    pub fn exp(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        base: &AssignedExtensionFieldValue<F, 2>,
        power: usize,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        match power {
            0 => return self.one_extension(ctx),
            1 => return Ok(base.clone()),
            2 => return self.square_extension(ctx, base),
            _ => (),
        }
        let mut product = self.one_extension(ctx)?;
        for _ in 0..power {
            product = self.mul_extension(ctx, &product, base)?;
        }
        Ok(product)
    }

    pub fn mul_many_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        terms: Vec<AssignedExtensionFieldValue<F, 2>>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let one = self.one_extension(ctx)?;
        let result = terms.into_iter().fold(one, |acc, term| {
            self.mul_extension(ctx, &acc, &term).unwrap()
        });
        Ok(result)
    }

    pub fn sub_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedExtensionFieldValue<F, 2>,
        rhs: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let one = Goldilocks::one();
        let one_extension = self.one_extension(ctx)?;
        self.arithmetic_extension(ctx, one, -one, lhs, &one_extension, rhs)
    }

    pub fn constant_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        constant: &[Goldilocks; 2],
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let z = self
            .arithmetic_chip()
            .assign_fixed_ext(ctx, constant.clone().map(|x| x.to_canonical_u64()))?;
        Ok(AssignedExtensionFieldValue(z))
    }

    pub fn convert_to_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        value: &AssignedValue<F>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let goldilocks_chip = self.goldilocks_chip();
        Ok(AssignedExtensionFieldValue([
            value.clone(),
            goldilocks_chip.assign_constant(ctx, Goldilocks::zero())?,
        ]))
    }

    pub fn reduce_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        base: &AssignedExtensionFieldValue<F, 2>,
        terms: &Vec<AssignedExtensionFieldValue<F, 2>>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let zero_extension = self.zero_extension(ctx)?;
        let result = terms.iter().rev().fold(zero_extension, |acc, term| {
            self.mul_add_extension(ctx, &acc, base, term).unwrap()
        });
        Ok(result)
    }

    pub fn reduce_base_field_terms_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        base: &AssignedExtensionFieldValue<F, 2>,
        terms: &Vec<AssignedValue<F>>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let terms = terms
            .iter()
            .map(|t| self.convert_to_extension(ctx, t))
            .collect::<Result<Vec<AssignedExtensionFieldValue<F, 2>>, Error>>()?;
        self.reduce_extension(ctx, base, &terms)
    }

    pub fn reduce_extension_field_terms_base(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        base: &AssignedValue<F>,
        terms: &Vec<AssignedExtensionFieldValue<F, 2>>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let base = self.convert_to_extension(ctx, base)?;
        self.reduce_extension(ctx, &base, terms)
    }

    // shifted * factor^power
    pub fn shift(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        factor: &AssignedExtensionFieldValue<F, 2>,
        power: usize,
        shifted: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let exp = self.exp(ctx, factor, power)?;
        self.mul_extension(ctx, &exp, shifted)
    }

    pub fn assert_equal_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedExtensionFieldValue<F, 2>,
        rhs: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();
        goldilocks_chip.assert_equal(ctx, &lhs.0[0], &rhs.0[0])?;
        goldilocks_chip.assert_equal(ctx, &lhs.0[1], &rhs.0[1])?;
        Ok(())
    }

    pub fn assert_one_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<(), Error> {
        let goldilocks_chip = self.goldilocks_chip();
        goldilocks_chip.assert_one(ctx, &a.0[0])?;
        goldilocks_chip.assert_zero(ctx, &a.0[1])?;
        Ok(())
    }

    /// Accepts a condition input which does not necessarily have to be
    /// binary. In this case, it computes the arithmetic generalization of `if b { x } else { y }`,
    /// i.e. `bx - (by-y)`.
    pub fn select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        cond: &AssignedExtensionFieldValue<F, 2>,
        a: &AssignedExtensionFieldValue<F, 2>,
        b: &AssignedExtensionFieldValue<F, 2>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        // cond * (a - b) + b
        let a_minus_b = self.sub_extension(ctx, a, b)?;
        let one = Goldilocks::one();
        self.arithmetic_extension(ctx, one, one, cond, &a_minus_b, b)
    }
}

#[cfg(test)]
mod tests {

    use crate::snark::chip::goldilocks_chip::GoldilocksChipConfig;
    use crate::snark::chip::native_chip::arithmetic_chip::{ArithmeticChip, ArithmeticConfig};
    use crate::snark::chip::native_chip::linear_chip::LinearConfig;
    use crate::snark::chip::native_chip::utils::{fr2_to_gfe, gfe_to_fr};

    use halo2_proofs::circuit::{Layouter, Value};
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::{circuit::SimpleFloorPlanner, plonk::Circuit};
    use halo2curves::goldilocks::fp::Goldilocks;
    use halo2wrong::RegionCtx;
    use plonky2::field::extension::Extendable;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::{Field, Sample};

    use super::GoldilocksExtensionChip;

    #[derive(Default)]
    struct TestCircuit {
        x: [Fr; 2],
        y: [Fr; 2],
        z: [Fr; 2],
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
            let goldilocks_extension_chip = GoldilocksExtensionChip::new(&config);

            let mut layouter = layouter.namespace(|| "decompose");
            layouter.assign_region(
                || "value",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let x_value = self.x.map(|x| Value::known(x));
                    let x_assigned =
                        goldilocks_extension_chip.assign_value_extension(&mut ctx, &x_value)?;

                    let x_pow_7 = goldilocks_extension_chip.exp(&mut ctx, &x_assigned, 7)?;
                    let expected = gfe_to_fr(fr2_to_gfe(self.x).exp_u64(7));
                    let expected_assigned = goldilocks_extension_chip
                        .assign_value_extension(&mut ctx, &expected.map(|x| Value::known(x)))?;
                    goldilocks_extension_chip.assert_equal_extension(
                        &mut ctx,
                        &x_pow_7,
                        &expected_assigned,
                    )?;

                    let y_value = self.y.map(|x| Value::known(x));
                    let y_assigned =
                        goldilocks_extension_chip.assign_value_extension(&mut ctx, &y_value)?;
                    let z_value = self.z.map(|x| Value::known(x));
                    let z_assigned =
                        goldilocks_extension_chip.assign_value_extension(&mut ctx, &z_value)?;

                    let a = Goldilocks::from(2);
                    let b = Goldilocks::from(3);

                    let output = goldilocks_extension_chip.arithmetic_extension(
                        &mut ctx,
                        a,
                        b,
                        &x_assigned,
                        &y_assigned,
                        &z_assigned,
                    )?;
                    let expected = {
                        let x = fr2_to_gfe(self.x);
                        let y = fr2_to_gfe(self.y);
                        let z = fr2_to_gfe(self.z);
                        let a =
                            <GoldilocksField as Extendable<2>>::Extension::from_canonical_u64(a.0);
                        let b =
                            <GoldilocksField as Extendable<2>>::Extension::from_canonical_u64(b.0);
                        gfe_to_fr(a * x * y + b * z)
                    };
                    let expected_assigned = goldilocks_extension_chip
                        .assign_value_extension(&mut ctx, &expected.map(|x| Value::known(x)))?;
                    goldilocks_extension_chip.assert_equal_extension(
                        &mut ctx,
                        &output,
                        &expected_assigned,
                    )?;

                    Ok(())
                },
            )?;
            let arithmetic_chip = ArithmeticChip::construct(config.arithmetic_config);
            arithmetic_chip.load_table(&mut layouter)?;
            Ok(())
        }
    }

    #[test]
    fn test_goldilocks_extension_chip() {
        let x = <GoldilocksField as Extendable<2>>::Extension::rand();
        let x = gfe_to_fr(x);
        let y = <GoldilocksField as Extendable<2>>::Extension::rand();
        let y = gfe_to_fr(y);
        let z = <GoldilocksField as Extendable<2>>::Extension::rand();
        let z = gfe_to_fr(z);
        let circuit = TestCircuit { x, y, z };
        MockProver::run(17, &circuit, vec![vec![]])
            .unwrap()
            .assert_satisfied();
    }
}
