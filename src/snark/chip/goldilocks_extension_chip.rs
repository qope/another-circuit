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
        let x_div_y = assigned_ext_div(x.0.clone(), y.0.clone());
        let x_div_y_assigned = self.assign_value_extension(ctx, &x_div_y)?;
        let one = self.one_extension(ctx)?;
        let output = self.mul_extension(ctx, &x_div_y_assigned, &one)?;
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
        let goldilocks_chip = self.goldilocks_chip();
        let added = addend_0
            .0
            .iter()
            .zip(addend_1.0.iter())
            .map(|(addend_0, addend_1)| goldilocks_chip.add(ctx, addend_0, addend_1))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        Ok(AssignedExtensionFieldValue(added.try_into().unwrap()))
    }

    pub fn scalar_mul(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        multiplicand: &AssignedExtensionFieldValue<F, 2>,
        scalar: Goldilocks,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let assigned_scalar = goldilocks_chip.assign_constant(ctx, scalar)?;
        let multiplied = multiplicand
            .0
            .iter()
            .map(|v| goldilocks_chip.mul(ctx, v, &assigned_scalar))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        Ok(AssignedExtensionFieldValue(multiplied.try_into().unwrap()))
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
        // multiplicand_0 * multiplicand_1
        let mut term_1 = self.mul(ctx, multiplicand_0, multiplicand_1)?;
        // const_0 * multiplicand_0 * multiplicand_1
        term_1 = self.scalar_mul(ctx, &term_1, const_0)?;
        // const_1 * addend
        let term_2 = self.scalar_mul(ctx, addend, const_1)?;
        self.add_extension(ctx, &term_1, &term_2)
    }

    pub fn zero_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let elements = (0..2)
            .map(|_| goldilocks_chip.assign_constant(ctx, Goldilocks::zero()))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        Ok(AssignedExtensionFieldValue(elements.try_into().unwrap()))
    }

    pub fn one_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let elements = [
            goldilocks_chip.assign_constant(ctx, Goldilocks::one())?,
            goldilocks_chip.assign_constant(ctx, Goldilocks::zero())?,
        ];
        Ok(AssignedExtensionFieldValue(elements))
    }

    pub fn two_extension(
        &self,
        ctx: &mut RegionCtx<'_, F>,
    ) -> Result<AssignedExtensionFieldValue<F, 2>, Error> {
        let goldilocks_chip = self.goldilocks_chip();
        let elements = [
            goldilocks_chip.assign_constant(ctx, Goldilocks::from(2))?,
            goldilocks_chip.assign_constant(ctx, Goldilocks::zero())?,
        ];
        Ok(AssignedExtensionFieldValue(elements))
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
        let goldilocks_chip = self.goldilocks_chip();
        let elements = constant
            .into_iter()
            .map(|c| goldilocks_chip.assign_constant(ctx, *c))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        Ok(AssignedExtensionFieldValue(elements.try_into().unwrap()))
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


