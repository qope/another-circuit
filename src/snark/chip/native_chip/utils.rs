use std::ops::Div;

use halo2_proofs::circuit::{AssignedCell, Value};
use halo2_proofs::halo2curves::bn256::Fr;
use num_bigint::BigUint;
use plonky2::field::extension::FieldExtension;
use plonky2::field::{
    extension::Extendable,
    goldilocks_field::GoldilocksField,
    types::{Field, PrimeField64},
};

use super::mod_chip::GOLDILOCKS_MODULUS;

pub fn fr_to_bu(x: Fr) -> BigUint {
    BigUint::from_bytes_le(&x.to_bytes())
}

pub fn bu_to_le_bits(x: BigUint) -> Vec<bool> {
    let x_bytes = x.to_bytes_le();
    let mut bits_le = Vec::new();
    for byte in x_bytes {
        bits_le.extend(u8_to_le_bits(byte));
    }
    bits_le
}

pub fn u8_to_le_bits(x: u8) -> Vec<bool> {
    let mut bits_le = Vec::new();
    for i in 0..8 {
        bits_le.push((x >> i) & 1 == 1);
    }
    bits_le
}

pub fn gf_to_fr(x: GoldilocksField) -> Fr {
    Fr::from(x.to_canonical_u64())
}

pub fn gfe_to_fr(x: <GoldilocksField as Extendable<2>>::Extension) -> [Fr; 2] {
    [
        Fr::from(x.0[0].to_canonical_u64()),
        Fr::from(x.0[1].to_canonical_u64()),
    ]
}

pub fn gfe_value_to_fr_value(
    x: Value<<GoldilocksField as Extendable<2>>::Extension>,
) -> [Value<Fr>; 2] {
    let fr_vec = x
        .map(|x| {
            vec![
                Fr::from(x.0[0].to_canonical_u64()),
                Fr::from(x.0[1].to_canonical_u64()),
            ]
        })
        .transpose_vec(2);
    fr_vec.try_into().unwrap()
}

pub fn gfe_to_u64(x: <GoldilocksField as Extendable<2>>::Extension) -> [u64; 2] {
    [x.0[0].to_canonical_u64(), x.0[1].to_canonical_u64()]
}

pub fn fr_to_gf(x: Fr) -> GoldilocksField {
    let x = BigUint::from_bytes_le(&x.to_bytes());
    let r = x % GOLDILOCKS_MODULUS;
    GoldilocksField::from_canonical_u64(r.to_u64_digits()[0])
}

pub fn fr2_to_gfe(x: [Fr; 2]) -> <GoldilocksField as Extendable<2>>::Extension {
    <GoldilocksField as Extendable<2>>::Extension::from_basefield_array([
        fr_to_gf(x[0]),
        fr_to_gf(x[1]),
    ])
}

pub fn assigned_ext_to_gfe(
    x: [AssignedCell<Fr, Fr>; 2],
) -> Value<<GoldilocksField as Extendable<2>>::Extension> {
    let x = x.map(|x| x.value().map(|x| fr_to_gf(*x)));
    x[0].zip(x[1]).map(|(x0, x1)| {
        <GoldilocksField as Extendable<2>>::Extension::from_basefield_array([x0, x1])
    })
}

pub fn assigned_ext_div(
    x: [AssignedCell<Fr, Fr>; 2],
    y: [AssignedCell<Fr, Fr>; 2],
) -> [Value<Fr>; 2] {
    let x_gfe = assigned_ext_to_gfe(x);
    let y_gfe = assigned_ext_to_gfe(y);
    let output_gfe = x_gfe.zip(y_gfe).map(|(x, y)| x.div(y));

    gfe_value_to_fr_value(output_gfe)
}
