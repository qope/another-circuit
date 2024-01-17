use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector},
    poly::Rotation,
};
use halo2curves::FieldExt;
use halo2wrong::RegionCtx;

use super::mod_chip::{ModChip, ModConfig, GOLDILOCKS_MODULUS};

// const_a*x*y + const_b*z + const_c = result
#[derive(Clone, Debug)]
pub struct ArithmeticConfig<F: FieldExt> {
    pub mod_config: ModConfig<F>,
    pub is_base: Selector,
    pub is_ext: Selector,
    pub is_select: Selector,
    pub flag: Column<Advice>,
    pub x: [Column<Advice>; 2],
    pub y: [Column<Advice>; 2],
    pub z: [Column<Advice>; 2],
    pub const_a: [Column<Fixed>; 2],
    pub const_b: [Column<Fixed>; 2],
    pub const_c: [Column<Fixed>; 2],
    pub result: [Column<Advice>; 2],
    pub pi: Column<Instance>,
}

impl<F: FieldExt> ArithmeticConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let mod_config = ModConfig::configure(meta);
        let is_base = meta.selector();
        let is_ext = meta.selector();
        let is_select = meta.selector();
        let const_a = [(); 2].map(|_| meta.fixed_column());
        let const_b = [(); 2].map(|_| meta.fixed_column());
        let const_c = [(); 2].map(|_| meta.fixed_column());
        let flag = meta.advice_column();
        let x = [(); 2].map(|_| meta.advice_column());
        let y = [(); 2].map(|_| meta.advice_column());
        let z = [(); 2].map(|_| meta.advice_column());
        let result = [(); 2].map(|_| meta.advice_column());
        let pi = meta.instance_column();

        const_a.map(|c| meta.enable_equality(c));
        const_b.map(|c| meta.enable_equality(c));
        const_c.map(|c| meta.enable_equality(c));
        x.map(|c| meta.enable_equality(c));
        y.map(|c| meta.enable_equality(c));
        z.map(|c| meta.enable_equality(c));
        result.map(|c| meta.enable_equality(c));
        meta.enable_equality(flag);
        meta.enable_equality(pi);

        meta.create_gate("main gate: base", |meta| {
            let is_base = meta.query_selector(is_base);
            let x = meta.query_advice(x[0], Rotation::cur());
            let y = meta.query_advice(y[0], Rotation::cur());
            let z = meta.query_advice(z[0], Rotation::cur());
            let const_a = meta.query_fixed(const_a[0], Rotation::cur());
            let const_b = meta.query_fixed(const_b[0], Rotation::cur());
            let const_c = meta.query_fixed(const_c[0], Rotation::cur());
            let result = meta.query_advice(result[0], Rotation::cur());

            let xy = x.clone() * y.clone();
            let xy_consta = xy.clone() * const_a.clone();
            let z_constb = z.clone() * const_b.clone();
            vec![
                is_base.clone()
                    * (xy_consta.clone() + z_constb.clone() + const_c.clone() - result.clone()),
            ]
        });

        meta.create_gate("main gate: extension", |meta| {
            let is_ext = meta.query_selector(is_ext);
            let x = x.map(|x| meta.query_advice(x, Rotation::cur()));
            let y = y.map(|y| meta.query_advice(y, Rotation::cur()));
            let z = z.map(|z| meta.query_advice(z, Rotation::cur()));
            let const_a = const_a.map(|a| meta.query_fixed(a, Rotation::cur()));
            let const_b = const_b.map(|b| meta.query_fixed(b, Rotation::cur()));
            let const_c = const_c.map(|c| meta.query_fixed(c, Rotation::cur()));
            let result = result.map(|r| meta.query_advice(r, Rotation::cur()));
            let x2 = Expression::Constant(F::from(7));

            let xy0 = x[0].clone() * y[0].clone() + x2.clone() * x[1].clone() * y[1].clone();
            let xy1 = x[1].clone() * y[0].clone() + x[0].clone() * y[1].clone();

            let xy_consta_0 =
                xy0.clone() * const_a[0].clone() + x2.clone() * xy1.clone() * const_a[1].clone();
            let xy_consta_1 = xy1.clone() * const_a[0].clone() + xy0.clone() * const_a[1].clone();

            let z_constb_0 =
                z[0].clone() * const_b[0].clone() + x2.clone() * z[1].clone() * const_b[1].clone();
            let z_constb_1 = z[1].clone() * const_b[0].clone() + z[0].clone() * const_b[1].clone();

            vec![
                is_ext.clone()
                    * (xy_consta_0.clone() + z_constb_0.clone() + const_c[0].clone()
                        - result[0].clone()),
                is_ext.clone()
                    * (xy_consta_1.clone() + z_constb_1.clone() + const_c[1].clone()
                        - result[1].clone()),
            ]
        });

        meta.create_gate("main gate: selector", |meta| {
            let is_select = meta.query_selector(is_select);
            let flag = meta.query_advice(flag, Rotation::cur());
            let x = x.map(|x| meta.query_advice(x, Rotation::cur()));
            let y = y.map(|y| meta.query_advice(y, Rotation::cur()));
            let result = result.map(|r| meta.query_advice(r, Rotation::cur()));

            let x_flag = x.map(|x| x * flag.clone());
            let one_minus_flag = Expression::Constant(F::one()) - flag.clone();
            let y_one_minus_flag = y.map(|y| y * one_minus_flag.clone());
            vec![
                is_select.clone() * flag * one_minus_flag,
                is_select.clone()
                    * (x_flag[0].clone() + y_one_minus_flag[0].clone() - result[0].clone()),
                is_select.clone()
                    * (x_flag[1].clone() + y_one_minus_flag[1].clone() - result[1].clone()),
            ]
        });

        Self {
            mod_config,
            const_a,
            const_b,
            const_c,
            is_base,
            is_ext,
            is_select,
            flag,
            x,
            y,
            z,
            result,
            pi,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ArithmeticChip<F: FieldExt> {
    config: ArithmeticConfig<F>,
}

pub struct ArithmeticAssignedBase<F: FieldExt> {
    pub x: AssignedCell<F, F>,
    pub y: AssignedCell<F, F>,
    pub z: AssignedCell<F, F>,
    pub const_a: AssignedCell<F, F>,
    pub const_b: AssignedCell<F, F>,
    pub const_c: AssignedCell<F, F>,
    pub result: AssignedCell<F, F>,
}

pub struct ArithmeticAssignedExt<F: FieldExt> {
    pub x: [AssignedCell<F, F>; 2],
    pub y: [AssignedCell<F, F>; 2],
    pub z: [AssignedCell<F, F>; 2],
    pub const_a: [AssignedCell<F, F>; 2],
    pub const_b: [AssignedCell<F, F>; 2],
    pub const_c: [AssignedCell<F, F>; 2],
    pub result: [AssignedCell<F, F>; 2],
}

pub struct ArithmeticAssignedSelect<F: FieldExt> {
    pub flag: AssignedCell<F, F>,
    pub x: [AssignedCell<F, F>; 2],
    pub y: [AssignedCell<F, F>; 2],
    pub result: [AssignedCell<F, F>; 2],
}

impl<F: FieldExt> ArithmeticChip<F> {
    pub fn construct(config: ArithmeticConfig<F>) -> Self {
        Self { config }
    }

    pub fn load_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let mod_chip = ModChip::construct(self.config.mod_config.clone());
        mod_chip.load_table(layouter)
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        value: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(value.cell(), self.config.pi, row)
    }

    pub fn assign_base(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: Value<F>,
        y: Value<F>,
        z: Value<F>,
        const_a: u64,
        const_b: u64,
        const_c: u64,
    ) -> Result<ArithmeticAssignedBase<F>, Error> {
        ctx.enable(self.config.is_base).unwrap();

        let const_a = F::from(const_a);
        let const_b = F::from(const_b);
        let const_c = F::from(const_c);

        let xy = x.clone() * y.clone();
        let xy_consta = xy.clone() * Value::known(const_a.clone());
        let z_constb = z.clone() * Value::known(const_b.clone());
        let result = xy_consta.clone() + z_constb.clone() + Value::known(const_c).clone();

        // assign
        let x_assigned = ctx.assign_advice(|| "x", self.config.x[0], x)?;
        let y_assigned = ctx.assign_advice(|| "y", self.config.y[0], y)?;
        let z_assigned = ctx.assign_advice(|| "z", self.config.z[0], z)?;
        let const_a_assigned = ctx.assign_fixed(|| "const_a", self.config.const_a[0], const_a)?;
        let const_b_assigned = ctx.assign_fixed(|| "const_b", self.config.const_b[0], const_b)?;
        let const_c_assigned = ctx.assign_fixed(|| "const_c", self.config.const_c[0], const_c)?;
        let result_assigned = ctx.assign_advice(|| "result", self.config.result[0], result)?;

        Ok(ArithmeticAssignedBase {
            x: x_assigned,
            y: y_assigned,
            z: z_assigned,
            const_a: const_a_assigned,
            const_b: const_b_assigned,
            const_c: const_c_assigned,
            result: result_assigned,
        })
    }

    pub fn assign_ext(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: [Value<F>; 2],
        y: [Value<F>; 2],
        z: [Value<F>; 2],
        const_a: [u64; 2],
        const_b: [u64; 2],
        const_c: [u64; 2],
    ) -> Result<ArithmeticAssignedExt<F>, Error> {
        ctx.enable(self.config.is_ext).unwrap();

        let const_a = const_a.map(|x| F::from(x));
        let const_b = const_b.map(|x| F::from(x));
        let const_c = const_c.map(|x| F::from(x));
        let x2 = Value::known(F::from(7));

        let xy0 = x[0].clone() * y[0].clone() + x2.clone() * x[1].clone() * y[1].clone();
        let xy1 = x[1].clone() * y[0].clone() + x[0].clone() * y[1].clone();

        let xy_consta_0 = xy0.clone() * Value::known(const_a[0])
            + x2.clone() * xy1.clone() * Value::known(const_a[1]);
        let xy_consta_1 =
            xy1.clone() * Value::known(const_a[0]) + xy0.clone() * Value::known(const_a[1]);
        let z_constb_0 = z[0].clone() * Value::known(const_b[0])
            + x2.clone() * z[1].clone() * Value::known(const_b[1]);
        let z_constb_1 =
            z[1].clone() * Value::known(const_b[0]) + z[0].clone() * Value::known(const_b[1]);

        let result0 = xy_consta_0.clone() + z_constb_0.clone() + Value::known(const_c[0]);
        let result1 = xy_consta_1.clone() + z_constb_1.clone() + Value::known(const_c[1]);
        let result = [result0, result1];

        // assign
        let x_assigned = self
            .config
            .x
            .iter()
            .zip(x)
            .map(|(x, x_val)| ctx.assign_advice(|| "x", *x, x_val).unwrap())
            .collect::<Vec<_>>();
        let y_assigned = self
            .config
            .y
            .iter()
            .zip(y)
            .map(|(y, y_val)| ctx.assign_advice(|| "y", *y, y_val).unwrap())
            .collect::<Vec<_>>();
        let z_assigned = self
            .config
            .z
            .iter()
            .zip(z)
            .map(|(z, z_val)| ctx.assign_advice(|| "z", *z, z_val).unwrap())
            .collect::<Vec<_>>();
        let const_a_assigned = self
            .config
            .const_a
            .iter()
            .zip(const_a)
            .map(|(const_a, const_a_val)| {
                ctx.assign_fixed(|| "const_a", *const_a, const_a_val)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let const_b_assigned = self
            .config
            .const_b
            .iter()
            .zip(const_b)
            .map(|(const_b, const_b_val)| {
                ctx.assign_fixed(|| "const_b", *const_b, const_b_val)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let const_c_assigned = self
            .config
            .const_c
            .iter()
            .zip(const_c)
            .map(|(const_c, const_c_val)| {
                ctx.assign_fixed(|| "const_c", *const_c, const_c_val)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let result_assigned = self
            .config
            .result
            .iter()
            .zip(result)
            .map(|(pi, result_val)| ctx.assign_advice(|| "result", *pi, result_val).unwrap())
            .collect::<Vec<_>>();

        Ok(ArithmeticAssignedExt {
            x: x_assigned.try_into().unwrap(),
            y: y_assigned.try_into().unwrap(),
            z: z_assigned.try_into().unwrap(),
            const_a: const_a_assigned.try_into().unwrap(),
            const_b: const_b_assigned.try_into().unwrap(),
            const_c: const_c_assigned.try_into().unwrap(),
            result: result_assigned.try_into().unwrap(),
        })
    }

    pub fn assign_selection(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        flag: Value<F>,
        x: [Value<F>; 2],
        y: [Value<F>; 2],
    ) -> Result<ArithmeticAssignedSelect<F>, Error> {
        ctx.enable(self.config.is_select).unwrap();
        let flag_assiged = ctx
            .assign_advice(|| "flag", self.config.flag, flag)
            .unwrap();
        let x_assigned = self
            .config
            .x
            .iter()
            .zip(x)
            .map(|(x, x_val)| ctx.assign_advice(|| "x", *x, x_val).unwrap())
            .collect::<Vec<_>>();
        let y_assigned = self
            .config
            .y
            .iter()
            .zip(y)
            .map(|(y, y_val)| ctx.assign_advice(|| "y", *y, y_val).unwrap())
            .collect::<Vec<_>>();

        let one_minus_flag = Value::known(F::one()) - flag.clone();
        let result = [
            x[0].clone() * flag.clone() + y[0].clone() * (one_minus_flag.clone()),
            x[1].clone() * flag.clone() + y[1].clone() * (one_minus_flag.clone()),
        ];

        let result_assigned = self
            .config
            .result
            .iter()
            .zip(result)
            .map(|(pi, result_val)| ctx.assign_advice(|| "result", *pi, result_val).unwrap())
            .collect::<Vec<_>>();
        Ok(ArithmeticAssignedSelect {
            flag: flag_assiged,
            x: x_assigned.try_into().unwrap(),
            y: y_assigned.try_into().unwrap(),
            result: result_assigned.try_into().unwrap(),
        })
    }

    pub fn take_mod(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        assigned: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mod_chip = ModChip::construct(self.config.mod_config.clone());
        let r = mod_chip.take_mod(ctx, assigned)?;
        ctx.next();
        Ok(r)
    }

    pub fn take_mod_ext(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        assigned: [AssignedCell<F, F>; 2],
    ) -> Result<[AssignedCell<F, F>; 2], Error> {
        let mod_chip = ModChip::construct(self.config.mod_config.clone());
        let r0 = mod_chip.take_mod(ctx, assigned[0].clone())?;
        ctx.next();
        let r1 = mod_chip.take_mod(ctx, assigned[1].clone())?;
        ctx.next();
        Ok([r0, r1])
    }

    /// c0 * a + b + c1
    pub fn generic_add(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        c0: u64,
        c1: u64,
        a: AssignedCell<F, F>,
        b: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        // x = a, y = 1, z = b, const_a = c0, const_b = 1, const_c = c1
        let assigned = self.assign_base(
            ctx,
            a.value().cloned(),
            Value::known(F::one()),
            b.value().cloned(),
            c0,
            1,
            c1,
        )?;
        ctx.constrain_equal(a.cell(), assigned.x.cell())?;
        ctx.constrain_equal(b.cell(), assigned.z.cell())?;
        ctx.constrain_equal(assigned.y.cell(), assigned.const_b.cell())?; // constrain y = 1
        self.take_mod(ctx, assigned.result)
    }

    /// c0 * a + b + c1
    pub fn generic_add_ext(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        c0: [u64; 2],
        c1: [u64; 2],
        a: [AssignedCell<F, F>; 2],
        b: [AssignedCell<F, F>; 2],
    ) -> Result<[AssignedCell<F, F>; 2], Error> {
        // x = a, y = 1, z = b, const_a = c0, const_b = 1, const_c = c1
        let assigned = self.assign_ext(
            ctx,
            a.clone().map(|x| x.value().cloned()),
            [Value::known(F::one()); 2],
            b.clone().map(|x| x.value().cloned()),
            c0,
            [1; 2],
            c1,
        )?;
        ctx.constrain_equal(a[0].cell(), assigned.x[0].cell())?;
        ctx.constrain_equal(a[1].cell(), assigned.x[1].cell())?;
        ctx.constrain_equal(b[0].cell(), assigned.z[0].cell())?;
        ctx.constrain_equal(b[1].cell(), assigned.z[1].cell())?;
        ctx.constrain_equal(assigned.y[0].cell(), assigned.const_b[0].cell())?; // constrain y = 1
        ctx.constrain_equal(assigned.y[1].cell(), assigned.const_b[1].cell())?;
        self.take_mod_ext(ctx, assigned.result)
    }

    /// c0*a*b + c1
    pub fn generic_mul(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        c0: u64,
        c1: u64,
        a: AssignedCell<F, F>,
        b: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        // x = a, y = b, z = 0, const_a = c0, const_b = 0, const_c = c1
        let assigned = self.assign_base(
            ctx,
            a.value().cloned(),
            b.value().cloned(),
            Value::known(F::zero()),
            c0,
            0,
            c1,
        )?;
        ctx.constrain_equal(a.cell(), assigned.x.cell())?;
        ctx.constrain_equal(b.cell(), assigned.y.cell())?;
        ctx.constrain_equal(assigned.z.cell(), assigned.const_b.cell())?; // constrain z = 0
        self.take_mod(ctx, assigned.result)
    }

    /// c0*a*b + c1
    pub fn generic_mul_ext(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        c0: [u64; 2],
        c1: [u64; 2],
        a: [AssignedCell<F, F>; 2],
        b: [AssignedCell<F, F>; 2],
    ) -> Result<[AssignedCell<F, F>; 2], Error> {
        // x = a, y = b, z = 0, const_a = c0, const_b = 0, const_c = c1
        let assigned = self.assign_ext(
            ctx,
            a.clone().map(|x| x.value().cloned()),
            b.clone().map(|x| x.value().cloned()),
            [Value::known(F::zero()); 2],
            c0,
            [0; 2],
            c1,
        )?;
        ctx.constrain_equal(a[0].cell(), assigned.x[0].cell())?;
        ctx.constrain_equal(a[1].cell(), assigned.x[1].cell())?;
        ctx.constrain_equal(b[0].cell(), assigned.y[0].cell())?;
        ctx.constrain_equal(b[1].cell(), assigned.y[1].cell())?;
        ctx.constrain_equal(assigned.z[0].cell(), assigned.const_b[0].cell())?; // constrain z = 0
        ctx.constrain_equal(assigned.z[1].cell(), assigned.const_b[1].cell())?; // constrain z = 0
        self.take_mod_ext(ctx, assigned.result)
    }

    /// c0*a*b + c1*c + c2
    pub fn generic_mul_add(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        c0: u64,
        c1: u64,
        c2: u64,
        a: AssignedCell<F, F>,
        b: AssignedCell<F, F>,
        c: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        // x = a, y = b, z = c, const_a = c0, const_b = c1, const_c = c2
        let assigned = self.assign_base(
            ctx,
            a.value().cloned(),
            b.value().cloned(),
            c.value().cloned(),
            c0,
            c1,
            c2,
        )?;
        ctx.constrain_equal(a.cell(), assigned.x.cell())?;
        ctx.constrain_equal(b.cell(), assigned.y.cell())?;
        ctx.constrain_equal(c.cell(), assigned.z.cell())?;
        self.take_mod(ctx, assigned.result)
    }

    /// c0*a*b + c1*c + c2
    pub fn generic_mul_add_ext(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        c0: [u64; 2],
        c1: [u64; 2],
        c2: [u64; 2],
        a: [AssignedCell<F, F>; 2],
        b: [AssignedCell<F, F>; 2],
        c: [AssignedCell<F, F>; 2],
    ) -> Result<[AssignedCell<F, F>; 2], Error> {
        // x = a, y = b, z = c, const_a = c0, const_b = c1, const_c = c2
        let assigned = self.assign_ext(
            ctx,
            a.clone().map(|x| x.value().cloned()),
            b.clone().map(|x| x.value().cloned()),
            c.clone().map(|x| x.value().cloned()),
            c0,
            c1,
            c2,
        )?;
        ctx.constrain_equal(a[0].cell(), assigned.x[0].cell())?;
        ctx.constrain_equal(a[1].cell(), assigned.x[1].cell())?;
        ctx.constrain_equal(b[0].cell(), assigned.y[0].cell())?;
        ctx.constrain_equal(b[1].cell(), assigned.y[1].cell())?;
        ctx.constrain_equal(c[0].cell(), assigned.z[0].cell())?;
        ctx.constrain_equal(c[1].cell(), assigned.z[1].cell())?;
        self.take_mod_ext(ctx, assigned.result)
    }

    pub fn assign_value(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let assigned = self.assign_base(
            ctx,
            unassigned,
            Value::known(F::zero()),
            Value::known(F::zero()),
            0,
            0,
            0,
        )?;
        self.take_mod(ctx, assigned.x)
    }

    pub fn assign_value_ext(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: [Value<F>; 2],
    ) -> Result<[AssignedCell<F, F>; 2], Error> {
        let assigned = self.assign_ext(
            ctx,
            unassigned,
            [Value::known(F::zero()); 2],
            [Value::known(F::zero()); 2],
            [0; 2],
            [0; 2],
            [0; 2],
        )?;
        self.take_mod_ext(ctx, assigned.x)
    }

    pub fn assign_fixed(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        constant: u64,
    ) -> Result<AssignedCell<F, F>, Error> {
        let assigned = self.assign_base(
            ctx,
            Value::known(F::zero()),
            Value::known(F::zero()),
            Value::known(F::zero()),
            constant,
            0,
            0,
        )?;
        ctx.next();
        Ok(assigned.const_a)
    }

    pub fn assign_fixed_ext(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        constant: [u64; 2],
    ) -> Result<[AssignedCell<F, F>; 2], Error> {
        let assigned = self.assign_ext(
            ctx,
            [Value::known(F::zero()); 2],
            [Value::known(F::zero()); 2],
            [Value::known(F::zero()); 2],
            constant,
            [0; 2],
            [0; 2],
        )?;
        ctx.next();
        Ok(assigned.const_a)
    }

    pub fn sub(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedCell<F, F>,
        b: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.generic_add(ctx, GOLDILOCKS_MODULUS - 1, 0, b, a)
    }

    pub fn sub_ext(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: [AssignedCell<F, F>; 2],
        b: [AssignedCell<F, F>; 2],
    ) -> Result<[AssignedCell<F, F>; 2], Error> {
        self.generic_add_ext(ctx, [GOLDILOCKS_MODULUS - 1, 0], [0; 2], b, a)
    }

    pub fn assign_bool(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: Value<bool>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let x = x.map(|x| F::from(x as u64));
        let dummy = [Value::known(F::zero()); 2];
        let assigned = self.assign_selection(ctx, x, dummy, dummy)?;
        ctx.next();
        Ok(assigned.flag)
    }

    pub fn not(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let one = self.assign_fixed(ctx, 1)?;
        self.sub(ctx, one, a)
    }

    /// b * x + (1-b) * y
    pub fn select_two(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        b: AssignedCell<F, F>,
        x: [AssignedCell<F, F>; 2],
        y: [AssignedCell<F, F>; 2],
    ) -> Result<[AssignedCell<F, F>; 2], Error> {
        let b_value = b.value().cloned();
        let x_value = x.clone().map(|x| x.value().cloned());
        let y_value = y.clone().map(|y| y.value().cloned());
        let assigned = self.assign_selection(ctx, b_value, x_value, y_value)?;
        ctx.constrain_equal(b.cell(), assigned.flag.cell())?;
        x.iter().zip(assigned.x.iter()).for_each(|(x, x_assigned)| {
            ctx.constrain_equal(x.cell(), x_assigned.cell()).unwrap();
        });
        y.iter().zip(assigned.y.iter()).for_each(|(y, y_assigned)| {
            ctx.constrain_equal(y.cell(), y_assigned.cell()).unwrap();
        });
        ctx.next();
        Ok(assigned.result)
    }

    pub fn select_four(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        b: AssignedCell<F, F>,
        x: [AssignedCell<F, F>; 4],
        y: [AssignedCell<F, F>; 4],
    ) -> Result<[AssignedCell<F, F>; 4], Error> {
        let result0 = self.select_two(
            ctx,
            b.clone(),
            x[0..2].to_vec().try_into().unwrap(),
            y[0..2].to_vec().try_into().unwrap(),
        )?;
        let result1 = self.select_two(
            ctx,
            b.clone(),
            x[2..4].to_vec().try_into().unwrap(),
            y[2..4].to_vec().try_into().unwrap(),
        )?;
        let result = [result0, result1].concat();
        Ok(result.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {

    use crate::snark::chip::native_chip::utils::{gf_to_fr, gfe_to_fr, gfe_to_u64};

    use super::{ArithmeticChip, ArithmeticConfig};
    use halo2_proofs::circuit::{Layouter, Value};
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::{circuit::SimpleFloorPlanner, plonk::Circuit};
    use halo2wrong::RegionCtx;
    use plonky2::field::extension::Extendable;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::Sample;

    #[derive(Default)]
    struct TestCircuit {
        x: [Value<Fr>; 2],
        y: [Value<Fr>; 2],
        z: [Value<Fr>; 2],
        const_a: [u64; 2],
        const_b: [u64; 2],
        const_c: [u64; 2],
        result_base_expected: Value<Fr>,
        result_ext_expected: [Value<Fr>; 2],
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = ArithmeticConfig<Fr>;

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
            ArithmeticConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<Fr>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            let main_gate = ArithmeticChip::construct(config);
            main_gate.load_table(&mut layouter)?;
            let mut layouter = layouter.namespace(|| "decompose");
            layouter.assign_region(
                || "value",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    let assigned_base = main_gate
                        .assign_base(
                            &mut ctx,
                            self.x[0],
                            self.y[0],
                            self.z[0],
                            self.const_a[0],
                            self.const_b[0],
                            self.const_c[0],
                        )
                        .unwrap();
                    let result_base = main_gate.take_mod(&mut ctx, assigned_base.result).unwrap();
                    dbg!(self.result_base_expected);
                    dbg!(result_base.value());

                    let assigned_ext = main_gate
                        .assign_ext(
                            &mut ctx,
                            self.x,
                            self.y,
                            self.z,
                            self.const_a,
                            self.const_b,
                            self.const_c,
                        )
                        .unwrap();
                    let result_ext = main_gate
                        .take_mod_ext(&mut ctx, assigned_ext.result)
                        .unwrap();
                    dbg!(self.result_ext_expected);
                    dbg!(result_ext[0].value(), result_ext[1].value());

                    // test selection
                    let flag = main_gate
                        .assign_bool(&mut ctx, Value::known(false))
                        .unwrap();
                    let result = main_gate
                        .select_two(
                            &mut ctx,
                            flag,
                            assigned_ext.y.clone(),
                            assigned_ext.x.clone(),
                        )
                        .unwrap();
                    ctx.constrain_equal(result[0].cell(), assigned_ext.x[0].cell())
                        .unwrap();
                    ctx.constrain_equal(result[1].cell(), assigned_ext.x[1].cell())
                        .unwrap();

                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_main_chip() {
        let x = <GoldilocksField as Extendable<2>>::Extension::rand();
        let y = <GoldilocksField as Extendable<2>>::Extension::rand();
        let z = <GoldilocksField as Extendable<2>>::Extension::rand();
        let const_a = <GoldilocksField as Extendable<2>>::Extension::rand();
        let const_b = <GoldilocksField as Extendable<2>>::Extension::rand();
        let const_c = <GoldilocksField as Extendable<2>>::Extension::rand();
        let result_base_expected = x.0[0].clone() * y.0[0].clone() * const_a.0[0].clone()
            + z.0[0].clone() * const_b.0[0].clone()
            + const_c.0[0].clone();
        let result_ext_expected =
            x.clone() * y.clone() * const_a.clone() + z.clone() * const_b.clone() + const_c.clone();

        let x = gfe_to_fr(x).map(|x| Value::known(x));
        let y = gfe_to_fr(y).map(|x| Value::known(x));
        let z = gfe_to_fr(z).map(|x| Value::known(x));
        let result_ext_expected = gfe_to_fr(result_ext_expected).map(|x| Value::known(x));
        let result_base_expected = Value::known(gf_to_fr(result_base_expected));
        let const_a = gfe_to_u64(const_a);
        let const_b = gfe_to_u64(const_b);
        let const_c = gfe_to_u64(const_c);
        let circuit = TestCircuit {
            x,
            y,
            z,
            const_a,
            const_b,
            const_c,
            result_base_expected,
            result_ext_expected,
        };
        MockProver::run(17, &circuit, vec![vec![]])
            .unwrap()
            .assert_satisfied();
    }
}
