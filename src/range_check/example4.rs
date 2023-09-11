use std::{env, fs::File, io::Write, marker::PhantomData, path::Path};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector,  SingleVerifier, Instance},
    poly::{commitment::Params, Rotation},
    transcript::{Blake2bRead, Blake2bWrite},
};

mod table;
use table::*;

use pasta_curves::{vesta, EqAffine};

use rand_core::OsRng;


/// This helper checks that the value witnessed in a given cell is within a given range.
/// Depending on the range, this helper uses either a range-check expression (for small ranges),
/// or a lookup (for large ranges).
///
///        value     |    q_range_check    |   q_lookup  |  table_value  |
///       ----------------------------------------------------------------
///          v_0     |         1           |      0      |       0       |
///          v_1     |         0           |      1      |       1       |
///

#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the RangeCheckConfig.
struct RangeConstrained<F: FieldExt, const RANGE: usize>(AssignedCell<Assigned<F>, F>);

#[derive(Debug, Clone)]
struct RangeCheckConfig<F: FieldExt, const RANGE: usize, const LOOKUP_RANGE: usize> {
    q_range_check: Selector,
    q_lookup: Selector,
    value: Column<Advice>,
    table: RangeTableConfig<F, LOOKUP_RANGE>,
    instance: Column<Instance>,
}

impl<F: FieldExt, const RANGE: usize, const LOOKUP_RANGE: usize>
    RangeCheckConfig<F, RANGE, LOOKUP_RANGE>
{
    pub fn configure(meta: &mut ConstraintSystem<F>, value: Column<Advice>) -> Self {
        let q_range_check = meta.selector();
        let q_lookup = meta.complex_selector();
        let table = RangeTableConfig::configure(meta);
        let instance = meta.instance_column();

        meta.enable_equality(instance);
      
        meta.create_gate("range check", |meta| {
            //        value     |    q_range_check
            //       ------------------------------
            //          v       |         1

            let q = meta.query_selector(q_range_check);
            let value = meta.query_advice(value, Rotation::cur());

            // Given a range R and a value v, returns the expression
            // (v) * (1 - v) * (2 - v) * ... * (R - 1 - v)
            let range_check = |range: usize, value: Expression<F>| {
                assert!(range > 0);
                (1..range).fold(value.clone(), |expr, i| {
                    expr * (Expression::Constant(F::from(i as u64)) - value.clone())
                })
            };

            Constraints::with_selector(q, [("range check", range_check(RANGE, value))])
        });

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let value = meta.query_advice(value, Rotation::cur());

            vec![(q_lookup * value, table.value)]
        });

        Self {
            q_range_check,
            q_lookup,
            value,
            table,
            instance,
        }
    }

    pub fn assign_simple(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F, RANGE>, Error> {
        layouter.assign_region(
            || "Assign value for simple range check",
            |mut region| {
                let offset = 0;

                // Enable q_range_check
                self.q_range_check.enable(&mut region, offset)?;

                // Assign value
                region
                    .assign_advice(|| "value", self.value, offset, || value)
                    .map(RangeConstrained)
            },
        )
    }

    pub fn assign_lookup(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F, LOOKUP_RANGE>, Error> {
        layouter.assign_region(
            || "Assign value for lookup range check",
            |mut region| {
                let offset = 0;

                // Enable q_lookup
                self.q_lookup.enable(&mut region, offset)?;

                // Assign value
                region
                    .assign_advice(|| "value", self.value, offset, || value)
                    .map(RangeConstrained)
            },
        )
    }



}

use halo2_proofs::{
    circuit::floor_planner::V1,
    dev::{FailureLocation, MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{Any, Circuit, create_proof, keygen_pk, keygen_vk, verify_proof},
    
};


#[derive(Default)]
struct MyCircuit<F: FieldExt, const RANGE: usize, const LOOKUP_RANGE: usize> {
    value: Value<Assigned<F>>,
    lookup_value: Value<Assigned<F>>,
}

impl<F: FieldExt, const RANGE: usize, const LOOKUP_RANGE: usize> Circuit<F>
    for MyCircuit<F, RANGE, LOOKUP_RANGE>
{
    type Config = RangeCheckConfig<F, RANGE, LOOKUP_RANGE>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        RangeCheckConfig::configure(meta, value)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.table.load(&mut layouter)?;

        config.assign_simple(layouter.namespace(|| "Assign simple value"), self.value)?;
        // config.assign_lookup(
        //     layouter.namespace(|| "Assign lookup value"),
        //     self.lookup_value,
        // )?;

        Ok(())
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_range_check_1() {

        let k = 9;
        const RANGE: usize = 16; // 3-bit value
        const LOOKUP_RANGE: usize = 8; // 8-bit value
        let i: u64 = 7;
        let j: u64 = 1;

        // Successful cases
    
        let circuit = MyCircuit::<Fp, RANGE, LOOKUP_RANGE> {
            value: Value::known(Fp::from(i as u64).into()),
            lookup_value: Value::known(Fp::from(j as u64).into()),
        };

        // let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        // prover.assert_satisfied();

        let params: Params<EqAffine> = halo2_proofs::poly::commitment::Params::new(k);
        // Generate verification key.
        println!("Generating Verification Key");
        let vk = keygen_vk(&params, &circuit).unwrap();

        // Generate proving key.
        println!("Generating Proving Key from Verification Key");
        let pk = keygen_pk(&params, vk, &circuit).unwrap();

        let mut transcript = Blake2bWrite::<_, vesta::Affine, _>::init(vec![]);

        // let mut public_input = vec![Fp::from(0)];
        // let mut public_input = vec![out];

        println!("Generating Proof!");
        create_proof(
            &params,
            &pk,
            &[circuit],
            &[&[&[]]],
            &mut OsRng,
            &mut transcript,
        )
        .expect("Failed to create proof!");

        // ANCHOR_END: create-proof
        // ANCHOR: write-proof

        let proof_path = "./proof";
        let proof = transcript.finalize();
        File::create(Path::new(proof_path))
            .expect("Failed to create proof file")
            .write_all(&proof[..])
            .expect("Failed to write proof");
        println!("Proof written to: {}", proof_path);

        // ANCHOR_END: write-proof
        // ANCHOR: verify-proof

        let mut transcript_proof = Blake2bRead::init(&proof[..]);

        // let public_input = vec![Fp::from(0), Fp::from(1), Fp::from(34)];


        // Verify the proof
        println!("Verifying Proof");
        let verified_proof_result = verify_proof(
            &params,
            pk.get_vk(),
            SingleVerifier::new(&params),
            &[&[&[]]],
            &mut transcript_proof,
        );

        // Print "OK(())" if the proof is valid or an error message otherwise.
        if verified_proof_result.is_ok() {
            println!("Proof verified!");
        } else {
            println!(
                "Proof verification failed! {}",
                verified_proof_result.err().unwrap()
            );
        }
    }


}


