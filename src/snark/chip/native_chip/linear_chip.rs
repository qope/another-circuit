use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
use halo2curves::FieldExt;
use halo2wrong::RegionCtx;

pub const NUM_REGISTERS: usize = 16;

/// \sum_{i=0}^{NUM_REGISTERS} r_i*c_i = output if is_combination
/// r_i + c_i = r_i' if is_addition
/// r_i is constrained to 0 or 1 if is_bool
#[derive(Clone, Debug)]
pub struct LinearConfig<F: FieldExt> {
    pub registers: [Column<Advice>; NUM_REGISTERS],
    pub constant_registers: [Column<Fixed>; NUM_REGISTERS],
    pub output: Column<Advice>,
    pub is_combination: Selector,
    pub is_addition: Selector,
    pub is_bool: Selector,
    _maker: std::marker::PhantomData<F>,
}

impl<F: FieldExt> LinearConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let registers = [(); NUM_REGISTERS].map(|_| meta.advice_column());
        let constant_registers = [(); NUM_REGISTERS].map(|_| meta.fixed_column());
        let output = meta.advice_column();
        let is_addition = meta.selector();
        let is_combination = meta.selector();
        let is_bool = meta.selector();

        registers.map(|x| meta.enable_equality(x));
        constant_registers.map(|x| meta.enable_equality(x));
        meta.enable_equality(output);

        meta.create_gate("combination gate", |meta| {
            let is_combination = meta.query_selector(is_combination);
            let registers = registers.map(|x| meta.query_advice(x, Rotation::cur()));
            let constant_registers =
                constant_registers.map(|x| meta.query_fixed(x, Rotation::cur()));
            let sum = registers
                .iter()
                .zip(constant_registers)
                .fold(Expression::Constant(F::zero()), |acc, (r, c)| {
                    acc + r.clone() * c.clone()
                });
            let output = meta.query_advice(output, Rotation::cur());
            vec![is_combination * (sum - output)]
        });

        meta.create_gate("addition gate", |meta| {
            let is_addition = meta.query_selector(is_addition);
            let registers_cur = registers.map(|x| meta.query_advice(x, Rotation::cur()));
            let constant_registers =
                constant_registers.map(|x| meta.query_fixed(x, Rotation::cur()));
            let registers_next = registers.map(|x| meta.query_advice(x, Rotation::next()));
            let constraints = (0..NUM_REGISTERS)
                .map(|i| {
                    is_addition.clone()
                        * (registers_cur[i].clone() + constant_registers[i].clone()
                            - registers_next[i].clone())
                })
                .collect::<Vec<_>>();
            constraints
        });

        meta.create_gate("bool constraint", |meta| {
            let is_bool = meta.query_selector(is_bool);
            let registers = registers.map(|x| meta.query_advice(x, Rotation::cur()));
            let constraints = registers
                .map(|x| is_bool.clone() * x.clone() * (Expression::Constant(F::one()) - x.clone()))
                .to_vec();
            constraints
        });

        Self {
            registers,
            constant_registers,
            output,
            is_combination,
            is_addition,
            is_bool,
            _maker: std::marker::PhantomData,
        }
    }
}

pub struct AssignedCombination<F: FieldExt> {
    pub register: [AssignedCell<F, F>; NUM_REGISTERS],
    pub constant_register: [AssignedCell<F, F>; NUM_REGISTERS],
    pub output: AssignedCell<F, F>,
}

pub struct AssignedAddition<F: FieldExt> {
    pub register: [AssignedCell<F, F>; NUM_REGISTERS],
    pub constant_register: [AssignedCell<F, F>; NUM_REGISTERS],
    pub next_register: [AssignedCell<F, F>; NUM_REGISTERS],
}

#[derive(Clone, Debug)]
pub struct LinearChip<F: FieldExt> {
    config: LinearConfig<F>,
}

impl<F: FieldExt> LinearChip<F> {
    pub fn construct(config: LinearConfig<F>) -> Self {
        Self { config }
    }

    pub fn assign_combination(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        registers: [Value<F>; NUM_REGISTERS],
        constant_registers: [u64; NUM_REGISTERS],
    ) -> Result<AssignedCombination<F>, Error> {
        ctx.enable(self.config.is_combination)?;
        let output = registers
            .iter()
            .zip(constant_registers.iter())
            .fold(Value::known(F::zero()), |acc, (r, c)| {
                acc + r.clone() * Value::known(F::from(*c))
            });
        let register_assigned = self
            .config
            .registers
            .iter()
            .zip(registers.iter())
            .map(|(r, v)| ctx.assign_advice(|| "register", *r, *v).unwrap())
            .collect::<Vec<_>>();
        let constant_register_assigned = self
            .config
            .constant_registers
            .iter()
            .zip(constant_registers.iter())
            .map(|(r, v)| {
                ctx.assign_fixed(|| "constant register", *r, F::from(*v))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let output_assigned = ctx.assign_advice(|| "output", self.config.output, output)?;
        Ok(AssignedCombination {
            register: register_assigned.try_into().unwrap(),
            constant_register: constant_register_assigned.try_into().unwrap(),
            output: output_assigned.try_into().unwrap(),
        })
    }

    pub fn assign_addition(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        registers: [Value<F>; NUM_REGISTERS],
        constant_registers: [u64; NUM_REGISTERS],
    ) -> Result<AssignedAddition<F>, Error> {
        ctx.enable(self.config.is_addition)?;
        let next_registers = registers
            .iter()
            .zip(constant_registers.iter())
            .map(|(r, c)| r.clone() + Value::known(F::from(*c)))
            .collect::<Vec<_>>();
        let register_assigned = self
            .config
            .registers
            .iter()
            .zip(registers.iter())
            .map(|(r, v)| ctx.assign_advice(|| "register", *r, *v).unwrap())
            .collect::<Vec<_>>();
        let constant_register_assigned = self
            .config
            .constant_registers
            .iter()
            .zip(constant_registers.iter())
            .map(|(r, v)| {
                ctx.assign_fixed(|| "constant register", *r, F::from(*v))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        ctx.next();
        let next_register_assigned = self
            .config
            .registers
            .iter()
            .zip(next_registers.iter())
            .map(|(r, v)| ctx.assign_advice(|| "next register", *r, *v).unwrap())
            .collect::<Vec<_>>();
        Ok(AssignedAddition {
            register: register_assigned.try_into().unwrap(),
            constant_register: constant_register_assigned.try_into().unwrap(),
            next_register: next_register_assigned.try_into().unwrap(),
        })
    }

    pub fn assign_constants(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        constants: [u64; NUM_REGISTERS],
    ) -> Result<[AssignedCell<F, F>; NUM_REGISTERS], Error> {
        let assigned = constants
            .iter()
            .zip(self.config.constant_registers.iter())
            .map(|(c, r)| {
                ctx.assign_fixed(|| "constant register", *r, F::from(*c))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        ctx.next();
        Ok(assigned.try_into().unwrap())
    }

    // decomposet to bits assuming that the value is less than 64 bits.
    pub fn to_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: AssignedCell<F, F>,
    ) -> Result<[AssignedCell<F, F>; 64], Error> {
        // decompose to 16 bits limbs
        let mut a_limbs = a
            .value()
            .map(|&v| {
                let limbs = v.to_repr().as_ref()[0..8]
                    .chunks(2)
                    .map(|chunk| F::from(chunk[0] as u64 + ((chunk[1] as u64) << 8)))
                    .collect::<Vec<_>>();
                limbs
            })
            .transpose_vec(4);
        a_limbs.resize(NUM_REGISTERS, Value::known(F::zero()));
        let mut contants = (0..4).map(|i| 1u64 << (16 * i)).collect::<Vec<_>>();
        contants.resize(NUM_REGISTERS, 0);
        let limb_assigned = self.assign_combination(
            ctx,
            a_limbs.try_into().unwrap(),
            contants.try_into().unwrap(),
        )?;
        ctx.next();
        ctx.constrain_equal(a.cell(), limb_assigned.output.cell())?;
        let mut bits = Vec::new();
        for i in 0..4 {
            let bits_value = limb_assigned.register[i]
                .value()
                .map(|&v| {
                    let b = v.clone().to_repr();
                    let b = b.as_ref();
                    let v = b[0] as u64 + ((b[1] as u64) << 8);
                    let mut bits = vec![];
                    for j in 0..16 {
                        bits.push(F::from((v >> j) & 1));
                    }
                    bits
                })
                .transpose_vec(16);
            let constants = (0..16).map(|i| 1 << i).collect::<Vec<u64>>();
            let bits_assigned = self.assign_combination(
                ctx,
                bits_value.try_into().unwrap(),
                constants.try_into().unwrap(),
            )?;
            ctx.constrain_equal(
                limb_assigned.register[i].cell(),
                bits_assigned.output.cell(),
            )?;
            ctx.next();
            bits.extend_from_slice(&bits_assigned.register);
        }

        Ok(bits.try_into().unwrap())
    }

    pub fn from_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: [AssignedCell<F, F>; 64],
    ) -> Result<AssignedCell<F, F>, Error> {
        let limbs = bits
            .chunks(16)
            .map(|chunk| {
                let values = chunk.iter().map(|x| x.value().cloned()).collect::<Vec<_>>();
                let constants = (0..16).map(|i| 1u64 << i).collect::<Vec<_>>();
                let assigned = self
                    .assign_combination(
                        ctx,
                        values.try_into().unwrap(),
                        constants.try_into().unwrap(),
                    )
                    .unwrap();
                ctx.enable(self.config.is_bool).unwrap();
                ctx.next();
                for i in 0..NUM_REGISTERS {
                    ctx.constrain_equal(assigned.register[i].cell(), chunk[i].cell())
                        .unwrap();
                }
                assigned.output
            })
            .collect::<Vec<_>>();
        let mut limbs_value = limbs.iter().map(|x| x.value().cloned()).collect::<Vec<_>>();
        limbs_value.resize(NUM_REGISTERS, Value::known(F::zero()));
        let mut contants = (0..4).map(|i| 1u64 << (16 * i)).collect::<Vec<_>>();
        contants.resize(NUM_REGISTERS, 0);
        let assigned = self.assign_combination(
            ctx,
            limbs_value.try_into().unwrap(),
            contants.try_into().unwrap(),
        )?;
        for i in 0..4 {
            ctx.constrain_equal(limbs[i].cell(), assigned.register[i].cell())
                .unwrap();
        }
        ctx.next();
        Ok(assigned.output)
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::circuit::Layouter;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::{circuit::SimpleFloorPlanner, plonk::Circuit};
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::{PrimeField64, Sample};

    use crate::snark::chip::native_chip::utils::{bu_to_le_bits, fr_to_bu};

    use super::*;

    #[derive(Default)]
    struct TestCircuit {
        r: [Fr; NUM_REGISTERS],
        c: [u64; NUM_REGISTERS],
        r0_bits: Vec<Fr>,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = LinearConfig<Fr>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
            LinearConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<Fr>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            let linear_chip = LinearChip::construct(config);
            let mut layouter = layouter.namespace(|| "combination");
            layouter.assign_region(
                || "value",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);
                    let r = self.r.map(|x| Value::known(x));
                    let assigned_combination = linear_chip
                        .assign_combination(&mut ctx, r.clone(), self.c)
                        .unwrap();
                    ctx.next();
                    let _assigned_addition = linear_chip
                        .assign_addition(&mut ctx, r.clone(), self.c)
                        .unwrap();
                    ctx.next();

                    let r0 = assigned_combination.register[0].clone();
                    let r0_bits = self
                        .r0_bits
                        .iter()
                        .map(|x| Value::known(*x))
                        .collect::<Vec<_>>();

                    let decomposed_x_bits = linear_chip.to_bits(&mut ctx, r0.clone()).unwrap();
                    decomposed_x_bits
                        .iter()
                        .zip(r0_bits.iter())
                        .for_each(|(x, y)| {
                            x.value().zip(*y).map(|(&x, y)| assert!(x == y));
                        });

                    let composed = linear_chip.from_bits(&mut ctx, decomposed_x_bits).unwrap();
                    ctx.constrain_equal(r0.cell(), composed.cell()).unwrap();

                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_linear_chip() {
        let mut rng = rand::thread_rng();
        let r = [(); NUM_REGISTERS]
            .map(|_| GoldilocksField::sample(&mut rng))
            .map(|x| Fr::from(x.to_canonical_u64()));
        let c = [(); NUM_REGISTERS]
            .map(|_| GoldilocksField::sample(&mut rng))
            .map(|x| x.to_canonical_u64());

        let r0 = r[0];
        let mut r0_bits = bu_to_le_bits(fr_to_bu(r0));
        r0_bits.resize(64, false);
        let r0_bits = r0_bits.into_iter().map(|x| Fr::from(x)).collect::<Vec<_>>();
        let circuit = TestCircuit { r, c, r0_bits };
        MockProver::run(10, &circuit, vec![])
            .unwrap()
            .assert_satisfied();
    }
}
