use plonky2::{
    hash::poseidon::{HALF_N_FULL_ROUNDS, N_PARTIAL_ROUNDS, SPONGE_WIDTH},
    plonk::{
        circuit_data::{CommonCircuitData, VerifierOnlyCircuitData},
        proof::ProofWithPublicInputs,
    },
};
const T: usize = SPONGE_WIDTH;
// const T_MINUS_ONE: usize = SPONGE_WIDTH - 1;
// const RATE: usize = SPONGE_WIDTH - 4;

const R_F: usize = HALF_N_FULL_ROUNDS * 2;
const R_F_HALF: usize = R_F / 2;
const R_P: usize = N_PARTIAL_ROUNDS;

pub mod chip;
pub mod types;
pub mod verifier_api;
pub mod verifier_circuit;

pub type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

#[cfg(test)]
pub mod test_contract_size;

#[cfg(test)]
pub mod test_arithmetic_contract;

#[cfg(test)]
pub mod test_linear_contract;

#[cfg(test)]
pub mod test_goldilocks_contract;

#[cfg(test)]
pub mod test_mod_contract;
