use std::vec;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{ConstraintSystem, Error},
};
use halo2curves::FieldExt;
use halo2wrong::RegionCtx;

use super::{
    arithmetic_chip::{ArithmeticChip, ArithmeticConfig},
    linear_chip::{LinearChip, LinearConfig, NUM_REGISTERS},
    poseidon_constants::{
        ALL_ROUND_CONSTANTS, HALF_N_FULL_ROUNDS, MDS_MATRIX_CIRC, MDS_MATRIX_DIAG,
        N_PARTIAL_ROUNDS, WIDTH,
    },
};

#[derive(Clone, Debug)]
pub struct PoseidonConfig<F: FieldExt> {
    pub arithmetic_config: ArithmeticConfig<F>,
    pub linear_config: LinearConfig<F>,
}

impl<F: FieldExt> PoseidonConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let main_config = ArithmeticConfig::configure(meta);
        let linear_config = LinearConfig::configure(meta);

        Self {
            arithmetic_config: main_config,
            linear_config,
        }
    }
}

#[derive(Clone, Debug)]
pub struct PoseidonChip<F: FieldExt> {
    pub config: PoseidonConfig<F>,
}

impl<F: FieldExt> PoseidonChip<F> {
    pub fn construct(config: PoseidonConfig<F>) -> Self {
        Self { config }
    }

    pub fn linear_chip(&self) -> LinearChip<F> {
        LinearChip::construct(self.config.linear_config.clone())
    }

    pub fn load_table(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        let main_chip = ArithmeticChip::construct(self.config.arithmetic_config.clone());
        main_chip.load_table(layouter)
    }

    pub fn assign_state(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: [Value<F>; WIDTH],
    ) -> Result<[AssignedCell<F, F>; WIDTH], Error> {
        let linear_chip = LinearChip::construct(self.config.linear_config.clone());
        let mut registers = state.to_vec();
        registers.resize(NUM_REGISTERS, Value::known(F::zero()));
        let constants = [0; NUM_REGISTERS];
        let assigned =
            linear_chip.assign_combination(ctx, registers.try_into().unwrap(), constants)?;
        ctx.next();
        Ok(assigned.register[0..WIDTH].to_vec().try_into().unwrap())
    }

    fn mds_circ_sum(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: [AssignedCell<F, F>; WIDTH],
        r: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let linear_chip = LinearChip::construct(self.config.linear_config.clone());
        let mut registers = state.iter().map(|x| x.value().cloned()).collect::<Vec<_>>();
        let mut constants = (0..WIDTH)
            .map(|i| MDS_MATRIX_CIRC[(WIDTH + i - r) % WIDTH])
            .collect::<Vec<_>>();
        registers.resize(NUM_REGISTERS, Value::known(F::zero()));
        constants.resize(NUM_REGISTERS, 0);
        let assigned = linear_chip.assign_combination(
            ctx,
            registers.try_into().unwrap(),
            constants.try_into().unwrap(),
        )?;
        // connect states
        for i in 0..WIDTH {
            ctx.constrain_equal(state[i].cell(), assigned.register[i].cell())
                .unwrap();
        }
        // connect unused registers to zero
        for i in WIDTH..NUM_REGISTERS {
            ctx.constrain_equal(
                assigned.register[i].cell(),
                assigned.constant_register[i].cell(),
            )
            .unwrap();
        }
        Ok(assigned.output)
    }

    pub fn mds_layer(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: [AssignedCell<F, F>; WIDTH],
    ) -> Result<[AssignedCell<F, F>; WIDTH], Error> {
        let main_chip = ArithmeticChip::construct(self.config.arithmetic_config.clone());
        let mut new_state = vec![];
        for r in 0..WIDTH {
            let sum = self.mds_circ_sum(ctx, state.clone(), r)?;
            let elm = main_chip.generic_add(ctx, MDS_MATRIX_DIAG[r], 0, state[r].clone(), sum)?;
            new_state.push(elm);
        }
        Ok(new_state.try_into().unwrap())
    }

    pub fn constant_round(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: [AssignedCell<F, F>; WIDTH],
        round: usize,
    ) -> Result<[AssignedCell<F, F>; WIDTH], Error> {
        let linear_chip = LinearChip::construct(self.config.linear_config.clone());
        let mut registers = state.iter().map(|x| x.value().cloned()).collect::<Vec<_>>();
        let mut constants = (0..WIDTH)
            .map(|i| ALL_ROUND_CONSTANTS[i + WIDTH * round])
            .collect::<Vec<_>>();
        registers.resize(NUM_REGISTERS, Value::known(F::zero()));
        constants.resize(NUM_REGISTERS, 0);
        let assigned = linear_chip.assign_addition(
            ctx,
            registers.try_into().unwrap(),
            constants.try_into().unwrap(),
        )?;
        // connect states
        for i in 0..WIDTH {
            ctx.constrain_equal(state[i].cell(), assigned.register[i].cell())
                .unwrap();
        }
        // connect unused registers to zero
        for i in WIDTH..NUM_REGISTERS {
            ctx.constrain_equal(
                assigned.register[i].cell(),
                assigned.constant_register[i].cell(),
            )
            .unwrap();
        }
        Ok(assigned.next_register[0..WIDTH]
            .to_vec()
            .try_into()
            .unwrap())
    }

    pub fn sbox_monomial(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let main_chip = ArithmeticChip::construct(self.config.arithmetic_config.clone());
        let x2 = main_chip.generic_mul(ctx, 1, 0, x.clone(), x.clone())?;
        let x4 = main_chip.generic_mul(ctx, 1, 0, x2.clone(), x2.clone())?;
        let x3 = main_chip.generic_mul(ctx, 1, 0, x2.clone(), x.clone())?;
        let x7 = main_chip.generic_mul(ctx, 1, 0, x4.clone(), x3.clone())?;
        Ok(x7)
    }

    pub fn sbox_layer(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: [AssignedCell<F, F>; WIDTH],
    ) -> Result<[AssignedCell<F, F>; WIDTH], Error> {
        let mut new_state = vec![];
        for i in 0..WIDTH {
            let elm = self.sbox_monomial(ctx, state[i].clone())?;
            new_state.push(elm);
        }
        Ok(new_state.try_into().unwrap())
    }

    pub fn full_round(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: [AssignedCell<F, F>; WIDTH],
        round: &mut usize,
    ) -> Result<[AssignedCell<F, F>; WIDTH], Error> {
        let mut result = state;
        for _ in 0..HALF_N_FULL_ROUNDS {
            result = self.constant_round(ctx, result, *round)?;
            result = self.sbox_layer(ctx, result)?;
            result = self.mds_layer(ctx, result)?;
            *round += 1;
        }
        Ok(result)
    }

    pub fn partial_round(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: [AssignedCell<F, F>; WIDTH],
        round: &mut usize,
    ) -> Result<[AssignedCell<F, F>; WIDTH], Error> {
        let mut result = state;
        for _ in 0..N_PARTIAL_ROUNDS {
            result = self.constant_round(ctx, result, *round)?;
            result[0] = self.sbox_monomial(ctx, result[0].clone())?;
            result = self.mds_layer(ctx, result)?;
            *round += 1;
        }
        Ok(result)
    }

    pub fn permute(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        state: [AssignedCell<F, F>; WIDTH],
    ) -> Result<[AssignedCell<F, F>; WIDTH], Error> {
        let mut state = state;
        let mut round = 0;
        state = self.full_round(ctx, state, &mut round)?;
        state = self.partial_round(ctx, state, &mut round)?;
        state = self.full_round(ctx, state, &mut round)?;
        Ok(state)
    }

    pub fn two_to_one_swapped(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        left: [AssignedCell<F, F>; 4],
        right: [AssignedCell<F, F>; 4],
        is_swapped: AssignedCell<F, F>,
    ) -> Result<[AssignedCell<F, F>; 4], Error> {
        let main_chip = ArithmeticChip::construct(self.config.arithmetic_config.clone());
        let left_selected =
            main_chip.select_four(ctx, is_swapped.clone(), right.clone(), left.clone())?;
        let right_selected = main_chip.select_four(ctx, is_swapped, left, right)?;
        let zero = main_chip.assign_fixed(ctx, 0)?;
        let mut state = [left_selected, right_selected].concat();
        state.resize(WIDTH, zero);
        let new_state = self.permute(ctx, state.try_into().unwrap())?;
        Ok(new_state[0..4].to_vec().try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{circuit::SimpleFloorPlanner, halo2curves::bn256::Fr, plonk::Circuit};
    use halo2wrong::RegionCtx;
    use num_bigint::BigUint;
    use num_integer::Integer;
    use plonky2::{
        field::{
            goldilocks_field::GoldilocksField,
            types::{PrimeField64, Sample},
        },
        hash::{
            hash_types::HashOut,
            poseidon::{Poseidon, PoseidonHash},
        },
        plonk::config::Hasher,
    };

    use crate::snark::chip::native_chip::{
        arithmetic_chip::ArithmeticChip,
        mod_chip::GOLDILOCKS_MODULUS,
        poseidon_constants::{
            ALL_ROUND_CONSTANTS, HALF_N_FULL_ROUNDS, MDS_MATRIX_CIRC, MDS_MATRIX_DIAG,
            N_PARTIAL_ROUNDS, WIDTH,
        },
        utils::fr_to_bu,
    };

    type F = Fr;

    fn mock_mds_layer(state: [F; WIDTH]) -> [F; WIDTH] {
        let mut result = [F::zero(); WIDTH];
        // This is a hacky way of fully unrolling the loop.
        for r in 0..12 {
            let mut sum = F::zero();
            for i in 0..12 {
                sum += state[i] * F::from(MDS_MATRIX_CIRC[(WIDTH + i - r) % WIDTH]);
            }
            result[r] = take_mod(sum + state[r] * F::from(MDS_MATRIX_DIAG[r]));
        }
        result
    }

    fn mock_constant_layer(state: [F; WIDTH], round: usize) -> [F; WIDTH] {
        let mut result = [F::zero(); WIDTH];
        for i in 0..WIDTH {
            let round_constant = ALL_ROUND_CONSTANTS[i + WIDTH * round];
            result[i] = state[i] + F::from(round_constant);
        }
        result
    }

    fn take_mod(x: F) -> F {
        let x_bu = fr_to_bu(x);
        let (_, r) = x_bu.div_rem(&BigUint::from(GOLDILOCKS_MODULUS));
        let digits = r.to_u64_digits();
        let r = if digits.len() == 0 { 0 } else { digits[0] };
        F::from(r)
    }

    fn mock_sbox_monomial(x: F) -> F {
        let x3 = take_mod(x * x * x);
        let x7 = take_mod(x3 * x3 * x);
        return x7;
    }

    fn mock_sbox_layer(state: [F; WIDTH]) -> [F; WIDTH] {
        let mut result = [F::zero(); WIDTH];
        for i in 0..WIDTH {
            result[i] = mock_sbox_monomial(state[i]);
        }
        result
    }

    fn full_round(state: [F; WIDTH], round: &mut usize) -> [F; WIDTH] {
        let mut result = state;
        for _ in 0..HALF_N_FULL_ROUNDS {
            result = mock_constant_layer(result, *round);
            result = mock_sbox_layer(result);
            result = mock_mds_layer(result);
            *round += 1;
        }
        result
    }

    fn partial_round(state: [F; WIDTH], round: &mut usize) -> [F; WIDTH] {
        let mut result = state;
        for _ in 0..N_PARTIAL_ROUNDS {
            result = mock_constant_layer(result, *round);
            result[0] = mock_sbox_monomial(result[0]);
            result = mock_mds_layer(result);
            *round += 1;
        }
        result
    }

    fn mock_permute(state: [F; WIDTH]) -> [F; WIDTH] {
        let mut result = state;
        let mut round = 0;
        result = full_round(result, &mut round);
        result = partial_round(result, &mut round);
        result = full_round(result, &mut round);
        result
    }

    fn mock_hash_two_to_one(left: [F; 4], right: [F; 4], is_swapped: bool) -> [F; 4] {
        let mut input = if !is_swapped {
            [left, right].concat()
        } else {
            [right, left].concat()
        };
        input.resize(WIDTH, F::zero());
        let result = mock_permute(input.try_into().unwrap());
        result[0..4].to_vec().try_into().unwrap()
    }

    use halo2_proofs::circuit::Layouter;
    use halo2_proofs::circuit::Value;

    use super::{PoseidonChip, PoseidonConfig};

    #[derive(Default)]
    struct TestCircuit {
        state: [F; WIDTH],
    }

    impl Circuit<F> for TestCircuit {
        type Config = PoseidonConfig<F>;

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
            PoseidonConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            let hash_chip = PoseidonChip::construct(config);

            let mut layouter = layouter.namespace(|| "combination");
            layouter.assign_region(
                || "value",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);

                    // test mds
                    let state_value = self.state.map(|x| Value::known(x));
                    let assiged_state = hash_chip.assign_state(&mut ctx, state_value).unwrap();
                    let result = hash_chip
                        .mds_layer(&mut ctx, assiged_state.clone())
                        .unwrap();
                    let expected = mock_mds_layer(self.state.clone());
                    result
                        .iter()
                        .zip(expected.iter())
                        .for_each(|(x, y)| x.value().assert_if_known(|x| *x == y));

                    // test constant round
                    let constant_result = hash_chip
                        .constant_round(&mut ctx, assiged_state.clone(), 3)
                        .unwrap();
                    let constant_expected = mock_constant_layer(self.state.clone(), 3);
                    constant_result
                        .iter()
                        .zip(constant_expected.iter())
                        .for_each(|(x, y)| x.value().assert_if_known(|x| *x == y));

                    // test sbox_layer
                    let sbox_result = hash_chip
                        .sbox_layer(&mut ctx, assiged_state.clone())
                        .unwrap();
                    let sbox_expected = mock_sbox_layer(self.state.clone());
                    sbox_result
                        .iter()
                        .zip(sbox_expected.iter())
                        .for_each(|(x, y)| x.value().assert_if_known(|x| *x == y));

                    let init_offset = ctx.offset();
                    // for _ in 0..2000 {
                    //     let permuted_result = hash_chip.permute(&mut ctx, assiged_state.clone());
                    //     let permuted_expected = mock_permute(self.state.clone());
                    //     permuted_result
                    //         .iter()
                    //         .zip(permuted_expected.iter())
                    //         .for_each(|(x, y)| x.value().assert_if_known(|x| *x == y));
                    // }

                    let main_chip =
                        ArithmeticChip::construct(hash_chip.config.arithmetic_config.clone());
                    let left = assiged_state[0..4].to_vec();
                    let right = assiged_state[4..8].to_vec();
                    let is_swapped = main_chip.assign_bool(&mut ctx, Value::known(true)).unwrap();
                    let hash_result_not_swap = hash_chip
                        .two_to_one_swapped(
                            &mut ctx,
                            left.clone().try_into().unwrap(),
                            right.clone().try_into().unwrap(),
                            is_swapped,
                        )
                        .unwrap();
                    let left_fr = self.state[0..4].to_vec();
                    let right_fr = self.state[4..8].to_vec();
                    let mut input = [right_fr, left_fr].concat();
                    input.resize(WIDTH, F::zero());

                    let hash_result_expected =
                        mock_permute(input.try_into().unwrap())[0..4].to_vec();
                    hash_result_not_swap
                        .iter()
                        .zip(hash_result_expected.iter())
                        .for_each(|(x, y)| x.value().assert_if_known(|x| *x == y));

                    let final_offset = ctx.offset();
                    dbg!(final_offset - init_offset);

                    Ok(())
                },
            )?;
            hash_chip.load_table(&mut layouter).unwrap();
            Ok(())
        }
    }

    #[test]
    fn test_permute() {
        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let state = [(); WIDTH].map(|_| GoldilocksField::sample(&mut rng));
            let state_fr = state.map(|x| F::from(x.to_canonical_u64()));
            let result_fr = mock_permute(state_fr);
            let expected = GoldilocksField::poseidon(state);
            let expected_fr = expected.map(|x| F::from(x.to_canonical_u64()));

            assert_eq!(result_fr, expected_fr);
        }
    }

    #[test]
    fn test_hash_two_to_one() {
        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let left = [(); 4].map(|_| GoldilocksField::sample(&mut rng));
            let right = [(); 4].map(|_| GoldilocksField::sample(&mut rng));
            let left_fr = left.map(|x| F::from(x.to_canonical_u64()));
            let right_fr = right.map(|x| F::from(x.to_canonical_u64()));
            let result_fr = mock_hash_two_to_one(left_fr, right_fr, false);
            let expected = <PoseidonHash as Hasher<GoldilocksField>>::two_to_one(
                HashOut { elements: left },
                HashOut { elements: right },
            );
            let expected_fr = expected.elements.map(|x| F::from(x.to_canonical_u64()));
            assert_eq!(result_fr, expected_fr);
        }
    }

    #[test]
    fn test_hash_circuit() {
        let mut rng = rand::thread_rng();
        let state = [(); WIDTH].map(|_| GoldilocksField::sample(&mut rng));
        let state_fr = state.map(|x| F::from(x.to_canonical_u64()));
        let circuit = TestCircuit { state: state_fr };
        halo2_proofs::dev::MockProver::run(17, &circuit, vec![vec![]])
            .unwrap()
            .assert_satisfied();
    }
}
