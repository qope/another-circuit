use std::marker::PhantomData;

use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::plonk::Error;
use halo2curves::{goldilocks::fp::Goldilocks, FieldExt};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::AssignedValue;
use plonky2::field::extension::Extendable;
use plonky2::{
    field::goldilocks_field::GoldilocksField,
    hash::{hash_types::HashOut, merkle_tree::MerkleCap, poseidon::PoseidonHash},
};

use self::assigned::{AssignedExtensionFieldValue, AssignedHashValues, AssignedMerkleCapValues};

use super::chip::goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig};

pub mod assigned;
pub mod common_data;
pub mod fri;
pub mod proof;
pub mod verification_key;

pub fn to_goldilocks(e: GoldilocksField) -> Goldilocks {
    Goldilocks::from(e.0)
}

#[derive(Clone, Debug, Default)]
pub struct HashValues<F: FieldExt> {
    pub elements: [Goldilocks; 4],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> HashValues<F> {
    pub fn assign(
        config: &GoldilocksChipConfig<F>,
        mut layouter: impl Layouter<F>,
        hash_value: &Self,
    ) -> Result<AssignedHashValues<F>, Error> {
        layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let goldilocks_chip = GoldilocksChip::new(config);
                let elements = hash_value
                    .elements
                    .iter()
                    .map(|e| goldilocks_chip.assign_constant(ctx, *e))
                    .collect::<Result<Vec<AssignedValue<F>>, Error>>()
                    .unwrap()
                    .try_into()
                    .unwrap();
                Ok(AssignedHashValues { elements })
            },
        )
    }
}

impl<F: FieldExt> From<HashOut<GoldilocksField>> for HashValues<F> {
    fn from(value: HashOut<GoldilocksField>) -> Self {
        let mut elements = [Goldilocks::zero(); 4];
        for (to, from) in elements.iter_mut().zip(value.elements.iter()) {
            *to = to_goldilocks(*from);
        }
        HashValues {
            elements,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct MerkleCapValues<F: FieldExt>(pub Vec<HashValues<F>>);

impl<F: FieldExt> MerkleCapValues<F> {
    pub fn assign(
        config: &GoldilocksChipConfig<F>,
        mut layouter: impl Layouter<F>,
        merkle_cap_values: &Self,
    ) -> Result<AssignedMerkleCapValues<F>, Error> {
        let elements = merkle_cap_values
            .0
            .iter()
            .map(|hash_value| HashValues::assign(config, layouter.namespace(|| ""), hash_value))
            .collect::<Result<Vec<AssignedHashValues<F>>, Error>>()?;
        Ok(AssignedMerkleCapValues(elements))
    }
}

impl<F: FieldExt> From<MerkleCap<GoldilocksField, PoseidonHash>> for MerkleCapValues<F> {
    fn from(value: MerkleCap<GoldilocksField, PoseidonHash>) -> Self {
        let cap_values = value.0.iter().map(|h| HashValues::from(*h)).collect();
        MerkleCapValues(cap_values)
    }
}

/// Contains a extension field value
#[derive(Clone, Debug)]
pub struct ExtensionFieldValue<F: FieldExt, const D: usize> {
    pub elements: [Goldilocks; D],
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const D: usize> Default for ExtensionFieldValue<F, D> {
    fn default() -> Self {
        Self {
            elements: [Goldilocks::zero(); D],
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt, const D: usize> ExtensionFieldValue<F, D> {
    pub fn assign(
        config: &GoldilocksChipConfig<F>,
        mut layouter: impl Layouter<F>,
        extension_field_value: &Self,
    ) -> Result<AssignedExtensionFieldValue<F, D>, Error> {
        layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let goldilocks_chip = GoldilocksChip::new(config);
                let elements = extension_field_value
                    .elements
                    .iter()
                    .map(|v| goldilocks_chip.assign_constant(ctx, *v))
                    .collect::<Result<Vec<AssignedValue<F>>, Error>>()?
                    .try_into()
                    .unwrap();
                Ok(AssignedExtensionFieldValue(elements))
            },
        )
    }
}

// impl From<<GoldilocksField as Extendable<2>>::Extension> for ExtensionFieldValue<Goldilocks, 2> {

// }

impl<F: FieldExt> From<[GoldilocksField; 2]> for ExtensionFieldValue<F, 2> {
    fn from(value: [GoldilocksField; 2]) -> Self {
        let mut elements = vec![];
        for from in value.iter() {
            elements.push(to_goldilocks(*from));
        }
        ExtensionFieldValue {
            elements: elements.try_into().unwrap(),
            _marker: PhantomData,
        }
    }
}

pub fn to_extension_field_values<F: FieldExt>(
    extension_fields: Vec<<GoldilocksField as Extendable<2>>::Extension>,
) -> Vec<ExtensionFieldValue<F, 2>> {
    extension_fields
        .iter()
        .map(|e| ExtensionFieldValue::from(e.0))
        .collect()
}
