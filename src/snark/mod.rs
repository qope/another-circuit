use plonky2::hash::poseidon::{HALF_N_FULL_ROUNDS, N_PARTIAL_ROUNDS, SPONGE_WIDTH};
const T: usize = SPONGE_WIDTH;
// const T_MINUS_ONE: usize = SPONGE_WIDTH - 1;
// const RATE: usize = SPONGE_WIDTH - 4;

const R_F: usize = HALF_N_FULL_ROUNDS * 2;
const R_F_HALF: usize = R_F / 2;
const R_P: usize = N_PARTIAL_ROUNDS;

pub mod chip;
pub mod types;
