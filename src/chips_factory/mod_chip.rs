use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
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
const NUM_R_LIMBS: usize = 4;

#[derive(Clone, Debug)]
pub struct ModConfig<F: FieldExt> {
    pub target: Column<Advice>,
    pub m: Column<Advice>,
    pub m_limbs: [Column<Advice>; NUM_M_LIMBS],
    pub r: Column<Advice>,
    pub r_limbs: [Column<Advice>; NUM_R_LIMBS],
    pub p_r_limbs: [Column<Advice>; NUM_R_LIMBS], // p-r
    pub selector: Selector,
    pub table: TableColumn,
    _marker: PhantomData<F>,
}

pub struct ModAssigned<F: FieldExt> {
    pub target: AssignedCell<F, F>,
    pub r: AssignedCell<F, F>,
    pub r_limbs: Vec<AssignedCell<F, F>>,
}

impl<F: FieldExt> ModConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let target = meta.advice_column();
        let table = meta.lookup_table_column();
        let m = meta.advice_column();
        let m_limbs = [(); NUM_M_LIMBS].map(|_| meta.advice_column());
        let r = meta.advice_column();
        let r_limbs = [(); NUM_R_LIMBS].map(|_| meta.advice_column());
        let p_r_limbs = [(); NUM_R_LIMBS].map(|_| meta.advice_column());
        let selector = meta.selector();

        meta.enable_equality(r);
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
        // check that r < 2^64
        meta.create_gate("r decompose", |meta| {
            let s = meta.query_selector(selector);
            let r = meta.query_advice(r, Rotation::cur());
            let r_limbs = r_limbs
                .map(|l| meta.query_advice(l, Rotation::cur()))
                .to_vec();
            let acc = (0..4).fold(Expression::Constant(F::zero()), |acc, i| {
                let two_pow_i = Expression::Constant(F::from(1 << (NUM_BITS * i)));
                acc + r_limbs[i].clone() * two_pow_i
            });
            let diff = acc - r;
            vec![s * diff]
        });
        r_limbs.iter().for_each(|limb| {
            meta.lookup("r_limbs range check", |meta| {
                let l = meta.query_advice(*limb, Rotation::cur());
                vec![(l, table)]
            });
        });
        // check that p-r < 2^64
        meta.create_gate("p-r decompose", |meta| {
            let s = meta.query_selector(selector);
            let r = meta.query_advice(r, Rotation::cur());
            let p_r = Expression::Constant(F::from(GOLDILOCKS_MODULUS)) - r;
            let p_r_limbs = p_r_limbs
                .map(|l| meta.query_advice(l, Rotation::cur()))
                .to_vec();
            let acc = (0..4).fold(Expression::Constant(F::zero()), |acc, i| {
                let two_pow_i = Expression::Constant(F::from(1 << (NUM_BITS * i)));
                acc + p_r_limbs[i].clone() * two_pow_i
            });
            let diff = acc - p_r;
            vec![s * diff]
        });
        p_r_limbs.iter().for_each(|limb| {
            meta.lookup("r_limbs range check", |meta| {
                let l = meta.query_advice(*limb, Rotation::cur());
                vec![(l, table)]
            });
        });

        // check that target = m * p + r
        meta.create_gate("target = m * p + r", |meta| {
            let s = meta.query_selector(selector);
            let t = meta.query_advice(target, Rotation::cur());
            let m = meta.query_advice(m, Rotation::cur());
            let r = meta.query_advice(r, Rotation::cur());
            vec![s * (t - m * Expression::Constant(F::from(GOLDILOCKS_MODULUS)) - r)]
        });

        ModConfig {
            target,
            m,
            m_limbs,
            r,
            r_limbs,
            p_r_limbs,
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
    ) -> Result<ModAssigned<F>, Error> {
        ctx.enable(self.config.selector).unwrap();
        // assertion and compute m and r
        let (m, r) = unassigned
            .map(|x| {
                let x_bu = fe_to_big(x);
                assert!(x_bu.bits() <= (MAX_M_BITS + 64) as u64);
                let (m, r) = x_bu.div_rem(&BigUint::from(GOLDILOCKS_MODULUS));
                let m = big_to_fe(m);
                let r = big_to_fe(r);
                (m, r)
            })
            .unzip();
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
        let r_limbs = r
            .map(|x| decompose(x, NUM_R_LIMBS, NUM_BITS))
            .transpose_vec(NUM_R_LIMBS);
        let r_limbs_assigned = self
            .config
            .r_limbs
            .iter()
            .zip(r_limbs.iter())
            .map(|(limb_col, limb)| ctx.assign_advice(|| "", *limb_col, *limb).unwrap())
            .collect::<Vec<_>>();
        let p_r = Value::known(F::from(GOLDILOCKS_MODULUS)) - r;
        let p_r_limbs = p_r
            .map(|x| decompose(x, NUM_R_LIMBS, NUM_BITS))
            .transpose_vec(NUM_R_LIMBS);
        let _p_r_limbs_assigned = self
            .config
            .p_r_limbs
            .iter()
            .zip(p_r_limbs.iter())
            .map(|(limb_col, limb)| ctx.assign_advice(|| "", *limb_col, *limb).unwrap())
            .collect::<Vec<_>>();
        let _m_assigned = ctx.assign_advice(|| "", self.config.m, m)?;
        let r_assigned = ctx.assign_advice(|| "", self.config.r, r)?;
        let target_assigned = ctx.assign_advice(|| "", self.config.target, unassigned)?;
        Ok(ModAssigned {
            target: target_assigned,
            r: r_assigned,
            r_limbs: r_limbs_assigned,
        })
    }

    pub fn take_mod(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        x: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let assigned = self.assign_mod(ctx, x.value().cloned())?;
        ctx.constrain_equal(assigned.target.cell(), x.cell())?;
        Ok(assigned.r)
    }

    pub fn range_check(
        &self,
        ctx: &mut RegionCtx<'_, F>,
        assigned: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        let r = self.take_mod(ctx, assigned.clone())?;
        ctx.constrain_equal(r.cell(), assigned.cell())?;
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
                    let assigned = range_chip
                        .assign_mod(&mut ctx, Value::known(self.value))
                        .unwrap();
                    range_chip
                        .range_check(&mut ctx, assigned.r.clone())
                        .unwrap();
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_mod_chip_size() {
        const DEGREE: u32 = 17;

        let circuit = TestCircuit {
            value: Fr::from(124),
        };
        MockProver::run(17, &circuit, vec![])
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
