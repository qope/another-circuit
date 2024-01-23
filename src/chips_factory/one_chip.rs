use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, Table, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Instance, Selector, TableColumn},
    poly::Rotation,
};
use halo2curves::FieldExt;

pub const GOLDILOCKS_MODULUS: u64 = ((1 << 32) - 1) * (1 << 32) + 1;

// a*b + c = q*p + r, with range check of q and r
#[derive(Clone, Debug)]
pub struct OneChipConfig<F: FieldExt> {
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    pub q: Column<Advice>,
    pub r: Column<Advice>,
    pub q_limbs: [Column<Advice>; 5],
    pub r_limbs: [Column<Advice>; 4],
    pub table: TableColumn,
    pub instance: Column<Instance>,
    pub constant: Column<Fixed>,
    pub selector: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> OneChipConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let q = meta.advice_column();
        let r = meta.advice_column();
        let q_limbs = [(); 5].map(|_| meta.advice_column());
        let r_limbs = [(); 4].map(|_| meta.advice_column());

        let constant = meta.fixed_column();
        let selector = meta.selector();
        let table = meta.lookup_table_column();
        let instance = meta.instance_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(r);
        meta.enable_equality(constant);
        meta.enable_equality(instance);

        meta.create_gate("arithmetic gate", |meta| {
            let s = meta.query_selector(selector);
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let q = meta.query_advice(q, Rotation::cur());
            let q_limbs = q_limbs
                .map(|l| meta.query_advice(l, Rotation::cur()))
                .to_vec();
            let q_acc = (0..5).fold(Expression::Constant(F::zero()), |acc, i| {
                acc + q_limbs[i].clone() * Expression::Constant(F::from(1 << (i * 16)))
            });
            let r = meta.query_advice(r, Rotation::cur());
            let r_limbs = r_limbs
                .map(|l| meta.query_advice(l, Rotation::cur()))
                .to_vec();
            let r_acc = (0..4).fold(Expression::Constant(F::zero()), |acc, i| {
                acc + r_limbs[i].clone() * Expression::Constant(F::from(1 << (i * 16)))
            });
            let p = Expression::Constant(F::from(GOLDILOCKS_MODULUS));
            vec![
                s.clone() * (a * b + c - p * q.clone() - r.clone()),
                s.clone() * (q - q_acc),
                s.clone() * (r - r_acc),
            ]
        });
        q_limbs.iter().for_each(|limb| {
            meta.lookup("range chip: limbs range check", |meta| {
                let l = meta.query_advice(*limb, Rotation::cur());
                vec![(l, table)]
            });
        });
        r_limbs.iter().for_each(|limb| {
            meta.lookup("range chip: limbs range check", |meta| {
                let l = meta.query_advice(*limb, Rotation::cur());
                vec![(l, table)]
            });
        });
        OneChipConfig {
            a,
            b,
            c,
            q,
            r,
            q_limbs,
            r_limbs,
            table,
            instance,
            constant,
            selector,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct OneChip<F: FieldExt> {
    config: OneChipConfig<F>,
}

impl<F: FieldExt> OneChip<F> {
    pub fn new(config: &OneChipConfig<F>) -> Self {
        OneChip {
            config: config.clone(),
        }
    }

    pub fn load_table(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        layouter.assign_table(
            || "range table",
            |mut table| {
                for offset in 0..1 << 16 {
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
    use std::{fs::File, io::Write};

    use halo2_proofs::{
        circuit::{floor_planner::V1, Layouter},
        dev::MockProver,
        halo2curves::bn256::{Bn256, Fr},
        plonk::{Circuit, ConstraintSystem, Error},
        poly::kzg::commitment::ParamsKZG,
    };
    use halo2wrong::RegionCtx;
    use snark_verifier::loader::evm::encode_calldata;

    use crate::snark::verifier_api::EvmVerifier;

    use super::OneChipConfig;

    #[derive(Clone, Default)]
    pub struct TestCircuit;

    impl Circuit<Fr> for TestCircuit {
        type Config = OneChipConfig<Fr>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            OneChipConfig::<Fr>::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let one_chip = super::OneChip::new(&config);
            one_chip.load_table(&mut layouter)?;
            layouter.assign_region(
                || "Verify proof",
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);

                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_one_contract() {
        const DEGREE: u32 = 17;

        let circuit = TestCircuit;
        let instance = vec![];
        let mock_prover = MockProver::run(DEGREE, &circuit, vec![instance.clone()]).unwrap();
        mock_prover.assert_satisfied();
        println!("{}", "Mock prover passes");

        // // generates EVM verifier
        let srs: ParamsKZG<Bn256> = EvmVerifier::gen_srs(DEGREE);
        let pk = EvmVerifier::gen_pk(&srs, &circuit);
        let deployment_code =
            EvmVerifier::gen_evm_verifier(&srs, pk.get_vk(), vec![instance.len()]);

        // generates SNARK proof and runs EVM verifier
        println!("{}", "Starting finalization phase");
        let proof = EvmVerifier::gen_proof(&srs, &pk, circuit.clone(), vec![instance.clone()]);
        println!("{}", "SNARK proof generated successfully!");

        let calldata = encode_calldata::<Fr>(&[instance], &proof);
        let deployment_code_hex = "0x".to_string() + &hex::encode(deployment_code);
        let calldata_hex = "0x".to_string() + &hex::encode(calldata);
        let mut file = File::create("deployment_code.txt").unwrap();
        file.write_all(deployment_code_hex.as_bytes()).unwrap();
        let mut file = File::create("calldata.txt").unwrap();
        file.write_all(calldata_hex.as_bytes()).unwrap();
    }
}
