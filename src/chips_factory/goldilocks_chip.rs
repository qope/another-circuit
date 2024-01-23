use std::marker::PhantomData;

use halo2_proofs::{arithmetic::Field, circuit::Value, plonk::Error};
use halo2curves::{goldilocks::fp::Goldilocks, FieldExt};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{
    big_to_fe, decompose, fe_to_big, power_of_two, AssignedCondition, AssignedValue,
    CombinationOptionCommon, MainGate, MainGateConfig, MainGateInstructions, RangeChip,
    RangeConfig, RangeInstructions, Term,
};
use itertools::Itertools;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Num, Zero};

#[derive(Clone, Debug)]
pub struct GoldilocksChipConfig<F: FieldExt> {
    pub main_gate_config: MainGateConfig,
    pub range_config: RangeConfig,
    _marker: PhantomData<F>,
}

pub struct GoldilocksChip<F: FieldExt> {
    goldilocks_chip_config: GoldilocksChipConfig<F>,
}

impl<F: FieldExt> GoldilocksChip<F> {
    pub fn configure(
        main_gate_config: &MainGateConfig,
        range_config: &RangeConfig,
    ) -> GoldilocksChipConfig<F> {
        GoldilocksChipConfig {
            main_gate_config: main_gate_config.clone(),
            range_config: range_config.clone(),
            _marker: PhantomData,
        }
    }

    pub fn new(goldilocks_chip_config: &GoldilocksChipConfig<F>) -> Self {
        Self {
            goldilocks_chip_config: goldilocks_chip_config.clone(),
        }
    }

    fn main_gate(&self) -> MainGate<F> {
        MainGate::new(self.goldilocks_chip_config.main_gate_config.clone())
    }

    fn range_chip(&self) -> RangeChip<F> {
        RangeChip::new(self.goldilocks_chip_config.range_config.clone())
    }

    fn quotient_range_check(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        quotient: &AssignedValue<F>,
    ) -> Result<(), Error> {
        quotient.value().map(|&x| {
            assert!(
                fe_to_big(x).bits() <= 80,
                "quotient range check: sanity check failed"
            )
        });
        let range_chip = self.range_chip();
        let (q, _limbs) = range_chip.decompose(ctx, quotient.value().cloned(), 16, 80)?;
        ctx.constrain_equal(q.cell(), quotient.cell())?;
        Ok(())
    }

    fn remainder_range_check(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        remainder: &AssignedValue<F>,
    ) -> Result<(), Error> {
        remainder.value().map(|&x| {
            assert!(
                fe_to_big(x).bits() <= 64,
                "remainder range check: sanity check failed"
            )
        });
        let range_chip = self.range_chip();
        let (q, _limbs) = range_chip.decompose(ctx, remainder.value().cloned(), 16, 64)?;
        ctx.constrain_equal(q.cell(), remainder.cell())?;
        Ok(())
    }

    pub fn goldilocks_modulus(&self) -> BigUint {
        BigUint::from_str_radix(&Goldilocks::MODULUS[2..], 16).unwrap()
    }

    pub fn goldilocks_to_native_fe(&self, goldilocks: Goldilocks) -> F {
        big_to_fe::<F>(fe_to_big::<Goldilocks>(goldilocks))
    }

    // assumes `fe` is already in goldilocks field
    fn native_fe_to_goldilocks(&self, fe: F) -> Goldilocks {
        big_to_fe::<Goldilocks>(fe_to_big::<F>(fe))
    }

    pub fn assign_value(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: Value<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        main_gate.assign_value(ctx, unassigned)
    }

    // TODO : decompose the Goldilocks value and range check
    pub fn assign_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        constant: Goldilocks,
    ) -> Result<AssignedValue<F>, Error> {
        let constant: F = big_to_fe(fe_to_big::<Goldilocks>(constant));
        MainGateInstructions::assign_constant(&self.main_gate(), ctx, constant)
    }

    pub fn add(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let (quotient, remainder) = lhs
            .value()
            .zip(rhs.value())
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) + fe_to_big(*r)).div_rem(&goldilocks_modulus);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        let assigned = main_gate.apply(
            ctx,
            [
                Term::assigned_to_add(lhs),
                Term::assigned_to_add(rhs),
                Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                Term::unassigned_to_sub(remainder),
            ],
            F::zero(),
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;
        let q_assigned = assigned[2].clone();
        let r_assigned = assigned[3].clone();

        // range check
        self.quotient_range_check(ctx, &q_assigned)?;
        self.remainder_range_check(ctx, &r_assigned)?;
        Ok(r_assigned)
    }

    pub fn sub(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let (quotient, remainder) = lhs
            .value()
            .zip(rhs.value())
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) + goldilocks_modulus.clone() - fe_to_big(*r))
                    .div_rem(&goldilocks_modulus.clone());
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        let assigned = main_gate.apply(
            ctx,
            [
                Term::assigned_to_add(lhs),
                Term::assigned_to_sub(rhs),
                Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus.clone())),
                Term::unassigned_to_sub(remainder),
            ],
            big_to_fe::<F>(goldilocks_modulus.clone()),
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;
        let q_assigned = assigned[2].clone();
        let r_assigned = assigned[3].clone();
        // range check
        self.quotient_range_check(ctx, &q_assigned)?;
        self.remainder_range_check(ctx, &r_assigned)?;
        Ok(r_assigned)
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
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let constant = self.goldilocks_to_native_fe(constant);
        let (quotient, remainder) = lhs
            .value()
            .zip(rhs.value())
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) * fe_to_big(*r) * fe_to_big(constant))
                    .div_rem(&goldilocks_modulus);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        let assigned = main_gate.apply(
            ctx,
            [
                Term::assigned_to_mul(lhs),
                Term::assigned_to_mul(rhs),
                Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                Term::unassigned_to_sub(remainder),
            ],
            F::zero(),
            CombinationOptionCommon::CombineToNextScaleMul(F::zero(), constant).into(),
        )?;
        let q_assigned = assigned[2].clone();
        let r_assigned = assigned[3].clone();
        // range check
        self.quotient_range_check(ctx, &q_assigned)?;
        self.remainder_range_check(ctx, &r_assigned)?;
        Ok(r_assigned)
    }

    pub fn mul_add_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
        to_add: Goldilocks,
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let to_add = self.goldilocks_to_native_fe(to_add);
        let (quotient, remainder) = a
            .value()
            .zip(b.value())
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) * fe_to_big(*r) + fe_to_big(to_add))
                    .div_rem(&goldilocks_modulus);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        let assigned = main_gate.apply(
            ctx,
            [
                Term::assigned_to_mul(a),
                Term::assigned_to_mul(b),
                Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                Term::unassigned_to_sub(remainder),
            ],
            to_add,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;
        let q_assigned = assigned[2].clone();
        let r_assigned = assigned[3].clone();
        // range check
        self.quotient_range_check(ctx, &q_assigned)?;
        self.remainder_range_check(ctx, &r_assigned)?;
        Ok(r_assigned)
    }

    pub fn add_constant(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        constant: Goldilocks,
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let (quotient, remainder) = a
            .value()
            .zip(Value::known(self.goldilocks_to_native_fe(constant)))
            .map(|(l, r)| {
                let (q, r) = (fe_to_big(*l) + fe_to_big(r)).div_rem(&goldilocks_modulus);
                (big_to_fe(q), big_to_fe(r))
            })
            .unzip();
        let assigned = main_gate.apply(
            ctx,
            [
                Term::assigned_to_add(a),
                Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                Term::unassigned_to_sub(remainder),
            ],
            self.goldilocks_to_native_fe(constant),
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;
        let q_assigned = assigned[1].clone();
        let r_assigned = assigned[2].clone();
        // range check
        self.quotient_range_check(ctx, &q_assigned)?;
        self.remainder_range_check(ctx, &r_assigned)?;
        Ok(r_assigned)
    }

    pub fn assert_equal(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        lhs: &AssignedValue<F>,
        rhs: &AssignedValue<F>,
    ) -> Result<(), Error> {
        let main_gate = self.main_gate();
        let lhs_minus_rhs = self.sub(ctx, lhs, rhs)?;
        main_gate.assert_zero(ctx, &lhs_minus_rhs)
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

    // TODO : optimize, underconstrained?
    pub fn compose(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        terms: &[Term<F>],
        constant: Goldilocks,
    ) -> Result<AssignedValue<F>, Error> {
        assert!(!terms.is_empty(), "At least one term is expected");
        let goldilocks_modulus = self.goldilocks_modulus();
        let composed = terms.iter().fold(
            Value::known(self.goldilocks_to_native_fe(constant)),
            |acc, term| {
                acc.zip(term.coeff()).map(|(acc, coeff)| {
                    let (_, remainder) = (fe_to_big(acc)
                        + fe_to_big(coeff) * fe_to_big(term.base()))
                    .div_rem(&goldilocks_modulus);
                    big_to_fe(remainder)
                })
            },
        );
        let composed = self.assign_value(ctx, composed)?;
        Ok(composed)
    }

    fn assign_bit(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bit: Value<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        main_gate.assign_bit(ctx, bit)
    }

    pub fn invert(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
    ) -> Result<(AssignedValue<F>, AssignedCondition<F>), Error> {
        let main_gate = self.main_gate();
        let goldilocks_modulus = self.goldilocks_modulus();
        let (one, zero) = (Goldilocks::one(), Goldilocks::zero());

        // Returns 'r' as a condition bit that defines if inversion successful or not
        // First enfoce 'r' to be a bit
        // (a * a') - 1 + r = p * q
        // r * a' - r = 0
        // if r = 1 then a' = 1
        // if r = 0 then a' = 1/a

        // Witness layout:
        // | A | B  | C |
        // | - | -- | - |
        // | a | a' | r |
        // | r | a' | r |

        let (r, a_inv) = a
            .value()
            .map(|a| {
                Option::from(self.native_fe_to_goldilocks(*a).invert())
                    .map(|a_inverted| {
                        (
                            self.goldilocks_to_native_fe(zero),
                            self.goldilocks_to_native_fe(a_inverted),
                        )
                    })
                    .unwrap_or_else(|| {
                        (
                            self.goldilocks_to_native_fe(one),
                            self.goldilocks_to_native_fe(one),
                        )
                    })
            })
            .unzip();

        let r = self.assign_bit(ctx, r)?;

        // (a * a') - 1 + r = p * q
        let quotient = a
            .value()
            .zip(a_inv)
            .zip(r.value())
            .map(|((&a, a_inv), &r)| {
                let (q, r) = (fe_to_big(a * a_inv - F::one() + r)).div_rem(&goldilocks_modulus);
                assert_eq!(r, BigUint::zero());
                big_to_fe::<F>(q)
            });

        let a_inv = main_gate
            .apply(
                ctx,
                [
                    Term::assigned_to_mul(a),
                    Term::unassigned_to_mul(a_inv),
                    Term::unassigned_to_sub(Value::known(self.goldilocks_to_native_fe(one))),
                    Term::assigned_to_add(&r),
                    Term::Unassigned(quotient, -big_to_fe::<F>(goldilocks_modulus)),
                ],
                F::zero(),
                CombinationOptionCommon::OneLinerMul.into(),
            )?
            .swap_remove(1);

        // r * a' - r = 0
        main_gate.apply(
            ctx,
            [
                Term::assigned_to_mul(&r),
                Term::assigned_to_mul(&a_inv),
                Term::assigned_to_sub(&r),
            ],
            F::zero(),
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok((a_inv, r))
    }

    pub fn select(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
        cond: &AssignedCondition<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        main_gate.select(ctx, a, b, cond)
    }

    pub fn is_zero(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        a: &AssignedValue<F>,
    ) -> Result<AssignedCondition<F>, Error> {
        let (_, is_zero) = self.invert(ctx, a)?;
        Ok(is_zero)
    }

    /// Assigns array values of bit values which is equal to decomposition of
    /// given assigned value
    pub fn to_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        composed: &AssignedValue<F>,
        number_of_bits: usize,
    ) -> Result<Vec<AssignedCondition<F>>, Error> {
        println!("to_bits called");
        assert!(number_of_bits <= F::NUM_BITS as usize);

        let decomposed_value = composed.value().map(|value| {
            decompose(self.native_fe_to_goldilocks(*value), number_of_bits, 1)
                .iter()
                .map(|v| self.goldilocks_to_native_fe(*v))
                .collect::<Vec<F>>()
        });

        let (bits, bases): (Vec<_>, Vec<_>) = (0..number_of_bits)
            .map(|i| {
                let bit = decomposed_value.as_ref().map(|bits| bits[i]);
                let bit = self.assign_bit(ctx, bit)?;
                let base = power_of_two::<F>(i);
                Ok((bit, base))
            })
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter()
            .unzip();

        let terms = bits
            .iter()
            .zip(bases.into_iter())
            .map(|(bit, base)| Term::Assigned(bit, base))
            .collect::<Vec<_>>();
        let result = self.compose(ctx, &terms, Goldilocks::zero())?;
        self.assert_equal(ctx, &result, composed)?;
        Ok(bits[..number_of_bits].to_vec())
    }

    pub fn from_bits(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        bits: &Vec<AssignedValue<F>>,
    ) -> Result<AssignedValue<F>, Error> {
        println!("from_bits called");
        let terms = bits
            .iter()
            .enumerate()
            .map(|(i, bit)| Term::Assigned(bit, power_of_two(i)))
            .collect_vec();
        self.compose(ctx, &terms[..], Goldilocks::zero())
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
    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::{floor_planner::V1, Layouter},
        dev::MockProver,
        halo2curves::bn256::Fr,
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use halo2curves::goldilocks::fp::Goldilocks;
    use halo2wrong::RegionCtx;
    use halo2wrong_maingate::{MainGate, RangeChip, RangeInstructions};

    use super::{GoldilocksChip, GoldilocksChipConfig};

    #[derive(Clone, Default)]
    pub struct TestCircuit;

    impl Circuit<Fr> for TestCircuit {
        type Config = GoldilocksChipConfig<Fr>;

        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let main_gate_config = MainGate::configure(meta);
            let range_config = RangeChip::configure(meta, &main_gate_config, vec![16], vec![0]);
            GoldilocksChipConfig {
                main_gate_config,
                range_config,
                _marker: PhantomData,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let chip = GoldilocksChip::new(&config);

            layouter.assign_region(
                || "mod contract",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    let a = chip.assign_constant(ctx, Goldilocks::from(2))?;
                    let b = chip.assign_constant(ctx, Goldilocks::from(3))?;
                    let _c = chip.add(ctx, &a, &b)?;

                    Ok(())
                },
            )?;
            let range_chip = RangeChip::new(config.range_config);
            range_chip.load_table(&mut layouter)?;
            Ok(())
        }
    }

    const DEGREE: u32 = 17;

    #[test]
    fn test_fixed_goldilocks_chip() {
        let circuit = TestCircuit;
        let instance = Vec::<Fr>::new();
        let mock_prover = MockProver::run(DEGREE, &circuit, vec![instance.clone()]).unwrap();
        mock_prover.assert_satisfied();

        // // generates EVM verifier
        // let srs: ParamsKZG<Bn256> = EvmVerifier::gen_srs(DEGREE);
        // let pk = EvmVerifier::gen_pk(&srs, &circuit);
        // let deployment_code =
        //     EvmVerifier::gen_evm_verifier(&srs, pk.get_vk(), vec![instance.len()]);

        // // generates SNARK proof and runs EVM verifier
        // println!("{}", "Starting finalization phase");
        // let proof = EvmVerifier::gen_proof(&srs, &pk, circuit.clone(), vec![instance.clone()]);
        // println!("{}", "SNARK proof generated successfully!");

        // let calldata = encode_calldata::<Fr>(&[instance], &proof);
        // let deployment_code_hex = "0x".to_string() + &hex::encode(deployment_code);
        // let calldata_hex = "0x".to_string() + &hex::encode(calldata);
        // let mut file = File::create("deployment_code.txt").unwrap();
        // file.write_all(deployment_code_hex.as_bytes()).unwrap();
        // let mut file = File::create("calldata.txt").unwrap();
        // file.write_all(calldata_hex.as_bytes()).unwrap();
    }
}
