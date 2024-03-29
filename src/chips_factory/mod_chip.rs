use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};
use halo2wrong::RegionCtx;
use halo2wrong_maingate::{big_to_fe, decompose, fe_to_big};
use num_bigint::BigUint;
use num_integer::Integer;

pub const GOLDILOCKS_MODULUS: u64 = ((1 << 32) - 1) * (1 << 32) + 1;
const NUM_BITS: usize = 16;
const NUM_M_LIMBS: usize = 9;
const MAX_M_BITS: usize = NUM_BITS * NUM_M_LIMBS;

#[derive(Clone, Debug)]
pub struct ModConfig<F: FieldExt> {
    pub target: Column<Advice>,
    pub m: Column<Advice>,
    pub m_limbs: [Column<Advice>; NUM_M_LIMBS],
    pub selector: Selector,
    pub table: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ModConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let target = meta.advice_column();
        let table = meta.lookup_table_column();
        let m = meta.advice_column();
        let m_limbs = [(); NUM_M_LIMBS].map(|_| meta.advice_column());
        let selector = meta.selector();

        meta.enable_equality(target);

        // check that 0<= m < 2^(NUM_BITS * NUM_M_LIMBS)
        meta.create_gate("m decompose", |meta| {
            let s = meta.query_selector(selector);
            let m = meta.query_advice(m, Rotation::cur());
            let m_limbs = m_limbs
                .map(|l| meta.query_advice(l, Rotation::cur()))
                .to_vec();
            let acc = (0..NUM_M_LIMBS).fold(Expression::Constant(F::zero()), |acc, i| {
                let two_pow_num_bits_i =
                    Expression::Constant(F::from(2).pow(&[(NUM_BITS * i) as u64, 0, 0, 0]));
                acc + m_limbs[i].clone() * two_pow_num_bits_i
            });
            let diff = acc - m;
            vec![s * diff]
        });
        m_limbs.iter().for_each(|limb| {
            meta.lookup("m_limbs range check", |meta| {
                let l = meta.query_advice(*limb, Rotation::cur());
                vec![(l, table)]
            });
        });

        ModConfig {
            target,
            m,
            m_limbs,
            selector,
            table,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ModChip<F: FieldExt> {
    config: ModConfig<F>,
}

impl<F: FieldExt> ModChip<F> {
    pub fn construct(config: ModConfig<F>) -> Self {
        Self { config }
    }

    // Assume that x < 2^(NUM_BITS * NUM_M_LIMBS + 64).
    // Then we can compute m and r such that x = m * GOLDILOCKS_MODULUS + r
    // if x > 2^(NUM_BITS * NUM_M_LIMBS + 64), the circuit will safely fails.
    pub fn assign_mod(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        unassigned: Value<F>,
    ) -> Result<(), Error> {
        ctx.enable(self.config.selector).unwrap();
        let (m, _) = unassigned
            .map(|x| {
                let x_bu = fe_to_big(x);
                assert!(x_bu.bits() <= (MAX_M_BITS + 64) as u64);
                let (m, r) = x_bu.div_rem(&BigUint::from(GOLDILOCKS_MODULUS));
                let m = big_to_fe(m);
                (m, r)
            })
            .unzip();
        let _m_assigned = ctx.assign_advice(|| "", self.config.m, m)?;
        let m_limbs = m
            .map(|x| decompose(x, NUM_M_LIMBS, NUM_BITS))
            .transpose_vec(NUM_M_LIMBS);
        let _m_limbs_assigned = self
            .config
            .m_limbs
            .iter()
            .zip(m_limbs.iter())
            .map(|(limb_col, limb)| ctx.assign_advice(|| "", *limb_col, *limb).unwrap())
            .collect::<Vec<_>>();
        let _target_assigned = ctx.assign_advice(|| "", self.config.target, unassigned)?;
        Ok(())
    }

    pub fn load_table(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        layouter.assign_table(
            || "range table",
            |mut table| {
                for offset in 0..1 << NUM_BITS {
                    table.assign_cell(
                        || "value",
                        self.config.table,
                        offset,
                        || Value::known(F::from(offset as u64)),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Write;

    use halo2_proofs::circuit::{Layouter, Value};
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::{Bn256, Fr};
    use halo2_proofs::poly::kzg::commitment::ParamsKZG;
    use halo2_proofs::{circuit::SimpleFloorPlanner, plonk::Circuit};
    use halo2wrong::RegionCtx;

    use crate::snark::verifier_api::EvmVerifier;

    use super::{ModChip, ModConfig};

    #[derive(Default, Clone)]
    struct TestCircuit {
        value: Fr,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = ModConfig<Fr>;

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
            ModConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl halo2_proofs::circuit::Layouter<Fr>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            let range_chip = ModChip::construct(config);
            range_chip.load_table(&mut layouter)?;
            let mut layouter = layouter.namespace(|| "bit decompose");
            layouter.assign_region(
                || "value",
                |region| {
                    let mut ctx = RegionCtx::new(region, 0);
                    range_chip
                        .assign_mod(&mut ctx, Value::known(self.value))
                        .unwrap();
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_mod_chip_size() {
        const DEGREE: u32 = 22;

        let circuit = TestCircuit {
            value: Fr::from(124),
        };
        MockProver::run(DEGREE, &circuit, vec![])
            .unwrap()
            .assert_satisfied();
        println!("{}", "Mock prover passes");

        // generates EVM verifier
        let srs: ParamsKZG<Bn256> = EvmVerifier::gen_srs(DEGREE);
        let pk = EvmVerifier::gen_pk(&srs, &circuit);
        let deployment_code = EvmVerifier::gen_evm_verifier(&srs, pk.get_vk(), vec![]);

        // generates SNARK proof and runs EVM verifier
        println!("{}", "Starting finalization phase");
        let _proof = EvmVerifier::gen_proof(&srs, &pk, circuit.clone(), vec![]);
        println!("{}", "SNARK proof generated successfully!");

        let deployment_code_hex = "0x".to_string() + &hex::encode(deployment_code);
        let mut file = File::create("deployment_code.txt").unwrap();
        file.write_all(deployment_code_hex.as_bytes()).unwrap();
    }
}
