use halo2_proofs::{arithmetic::FieldExt, plonk::Error};
use halo2wrong_maingate::{AssignedValue, RegionCtx};
use poseidon::State;

use super::{
    goldilocks_chip::{GoldilocksChip, GoldilocksChipConfig},
    native_chip::{
        poseidon_chip::{PoseidonChip, PoseidonConfig},
        poseidon_constants::{RATE, WIDTH},
    },
};

/// `AssignedState` is composed of `T` sized assigned values
#[derive(Debug, Clone)]
pub struct AssignedState<F: FieldExt>(pub(super) [AssignedValue<F>; WIDTH]);

/// `HasherChip` is basically responsible for contraining permutation part of
/// transcript pipeline
#[derive(Debug, Clone)]
pub struct HasherChip<F: FieldExt> {
    state: AssignedState<F>,
    absorbing: Vec<AssignedValue<F>>,
    output_buffer: Vec<AssignedValue<F>>,
    goldilocks_chip_config: GoldilocksChipConfig<F>,
}

impl<F: FieldExt> HasherChip<F> {
    // Constructs new hasher chip with assigned initial state
    pub fn new(
        // TODO: we can remove initial state assingment in construction
        ctx: &mut RegionCtx<'_, F>,
        goldilocks_chip_config: &GoldilocksChipConfig<F>,
    ) -> Result<Self, Error> {
        let goldilocks_chip = GoldilocksChip::new(goldilocks_chip_config);

        let initial_state = State::<_, WIDTH>::default()
            .words()
            .iter()
            .map(|word| goldilocks_chip.assign_constant(ctx, *word))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;

        Ok(Self {
            state: AssignedState(initial_state.try_into().unwrap()),
            absorbing: vec![],
            output_buffer: vec![],
            goldilocks_chip_config: goldilocks_chip_config.clone(),
        })
    }

    pub fn poseidon_chip(&self) -> PoseidonChip<F> {
        let poseidon_config = PoseidonConfig {
            arithmetic_config: self.goldilocks_chip_config.arithmetic_config.clone(),
            linear_config: self.goldilocks_chip_config.linear_config.clone(),
        };
        PoseidonChip::construct(poseidon_config)
    }

    /// Appends field elements to the absorbation line. It won't perform
    /// permutation here
    pub fn update(
        &mut self,
        _ctx: &mut RegionCtx<'_, F>,
        element: &AssignedValue<F>,
    ) -> Result<(), Error> {
        self.output_buffer.clear();
        self.absorbing.push(element.clone());
        Ok(())
    }

    fn absorb_buffered_inputs(&mut self, ctx: &mut RegionCtx<'_, F>) -> Result<(), Error> {
        if self.absorbing.is_empty() {
            return Ok(());
        }
        let buffered_inputs = self.absorbing.clone();
        for input_chunk in buffered_inputs.chunks(RATE) {
            self.duplexing(ctx, input_chunk)?;
        }
        self.absorbing.clear();
        Ok(())
    }

    pub fn squeeze(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        num_outputs: usize,
    ) -> Result<Vec<AssignedValue<F>>, Error> {
        let mut output = vec![];
        for _i in 0..num_outputs {
            self.absorb_buffered_inputs(ctx)?;

            if self.output_buffer.is_empty() {
                self.permutation(ctx)?;
                self.output_buffer = self.state.0[0..RATE].to_vec();
            }
            output.push(self.output_buffer.pop().unwrap())
        }
        Ok(output)
    }
}

impl<F: FieldExt> HasherChip<F> {
    /// Construct main gate
    pub fn goldilocks_chip(&self) -> GoldilocksChip<F> {
        GoldilocksChip::new(&self.goldilocks_chip_config)
    }
}

impl<F: FieldExt> HasherChip<F> {
    /// Constrains poseidon permutation while mutating the given state
    pub fn permutation(&mut self, ctx: &mut RegionCtx<'_, F>) -> Result<(), Error> {
        let state = self.state.0.clone();
        let permuted = self.poseidon_chip().permute(ctx, state)?;
        self.state = AssignedState(permuted);
        Ok(())
    }

    fn duplexing(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        input: &[AssignedValue<F>],
    ) -> Result<(), Error> {
        for (word, input) in self.state.0.iter_mut().zip(input.iter()) {
            *word = input.clone();
        }
        self.permutation(ctx)?;

        self.output_buffer.clear();
        self.output_buffer.extend_from_slice(&self.state.0[0..RATE]);
        Ok(())
    }

    pub fn hash(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        inputs: Vec<AssignedValue<F>>,
        num_outputs: usize,
    ) -> Result<Vec<AssignedValue<F>>, Error> {
        // Flush the input que
        self.absorbing.clear();

        for chunk in inputs.chunks(RATE) {
            for (word, input) in self.state.0.iter_mut().zip(chunk.iter()) {
                *word = input.clone();
            }
            self.permutation(ctx)?;
        }

        let mut outputs = vec![];
        loop {
            for item in self.state.0.iter().take(RATE) {
                outputs.push(item.clone());
                if outputs.len() == num_outputs {
                    return Ok(outputs);
                }
            }
            self.permutation(ctx)?;
        }
    }

    pub fn permute(
        &mut self,
        ctx: &mut RegionCtx<'_, F>,
        input: Vec<AssignedValue<F>>,
        num_output: usize,
    ) -> Result<Vec<AssignedValue<F>>, Error> {
        for (word, input) in self.state.0.iter_mut().zip(input.iter()) {
            *word = input.clone();
        }
        self.permutation(ctx)?;

        let mut outputs = vec![];
        loop {
            for item in self.state.0.iter().take(RATE) {
                outputs.push(item.clone());
                if outputs.len() == num_output {
                    return Ok(outputs);
                }
            }
            self.permutation(ctx)?;
        }
    }
}
