use cs_derive::*;
use derivative::Derivative;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use advanced_circuit_component::traits::*;
use advanced_circuit_component::franklin_crypto::bellman::bn256::Bn256;
use advanced_circuit_component::franklin_crypto::bellman::{CurveAffine, CurveProjective, Engine, Field, PrimeField, SynthesisError};
use advanced_circuit_component::franklin_crypto::bellman::kate_commitment::{Crs, CrsForMonomialForm};
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::cs::{Circuit, ProvingAssembly, SetupAssembly, TrivialAssembly};
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use advanced_circuit_component::franklin_crypto::bellman::worker::Worker;
use advanced_circuit_component::franklin_crypto::plonk::circuit::bigint::field::RnsParameters;
use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::aux_data::{AuxData, BN256AuxData};
use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::without_flag_unchecked::WrapperUnchecked;
use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::data_structs::IntoLimbedWitness;
use advanced_circuit_component::franklin_crypto::plonk::circuit::Width4WithCustomGates;
use advanced_circuit_component::franklin_crypto::rescue::RescueEngine;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::{
    setup::{Setup as NewSetup, VerificationKey as NewVerificationKey},
    proof::Proof as NewProof
};
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::gates::selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use advanced_circuit_component::franklin_crypto::plonk::circuit::allocated_num::Num;
use advanced_circuit_component::recursion::node_aggregation::{NodeAggregationOutputData, NodeAggregationOutputDataWitness};
use advanced_circuit_component::rescue_poseidon::{GenericSponge, HashParams, PoseidonParams, RescueParams};
use advanced_circuit_component::recursion::transcript::{GenericTranscriptForRNSInFieldOnly, GenericTranscriptGadget};
use serde::{Deserialize, Serialize};
use crate::circuit::{RecursiveAggregationCircuit, ZKLINK_NUM_INPUTS};
use crate::vks_tree::{create_vks_tree, POSEIDON_PARAMETERS, RESCUE_PARAMETERS, RNS_PARAMETERS};

pub type RecursiveAggregationCircuitBn256<'a> = RecursiveAggregationCircuit<
    'a,
    Bn256,
    PlonkCsWidth4WithNextStepParams,
    WrapperUnchecked<'a, Bn256>,
    BN256AuxData,
    RescueTranscriptGadgetForRecursion<Bn256>,
>;
pub type DefaultRescueParams<E> = RescueParams<E, 2, 3>;
pub type DefaultPoseidonParams<E> = PoseidonParams<E, 2, 3>;
pub type RescueTranscriptForRecursion<'a, E> =
    GenericTranscriptForRNSInFieldOnly<'a, E, RescueParams<E, 2, 3>, 2, 3>;
pub type RescueTranscriptGadgetForRecursion<E> =
    GenericTranscriptGadget<E, RescueParams<E, 2, 3>, 2, 3>;

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSVariableLengthEncodable
)]
#[derivative(Clone, Debug)]
pub struct BlockAggregationOutputData<E: Engine> {
    pub vk_root: Num<E>,
    pub final_price_commitment: Num<E>, // previous_price_hash^2 + this_price_hash
    pub blocks_commitments: Vec<Num<E>>,
    pub aggregation_output_data: NodeAggregationOutputData<E>,
}

impl<E: Engine> BlockAggregationOutputDataWitness<E> {
    pub fn new(
        vks_tree_root: E::Fr,
        aggregate: &[E::G1Affine; 2],
        public_input_data: &[BlockPublicInputData<E>],
        rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    ) -> Self {
        let mut accumulated_prices_num = E::Fr::zero();
        let mut final_price_commitment = E::Fr::zero();
        for data in public_input_data.iter() {
            let mut offset = data.prices_base_sum;
            offset.mul_assign(&accumulated_prices_num);
            final_price_commitment.add_assign(&data.price_commitment);
            final_price_commitment.add_assign(&offset);
            accumulated_prices_num.add_assign(&data.prices_num); 
        }

        use advanced_circuit_component::recursion::recursion_tree::NUM_LIMBS;
        let mut pair_with_generator = Vec::new();
        decompose_point_into_limbs(&aggregate[0], &mut pair_with_generator, rns_params);
        assert_eq!(pair_with_generator.len(), NUM_LIMBS * 2);
        let mut pair_with_x = Vec::new();
        decompose_point_into_limbs(&aggregate[1], &mut pair_with_x, rns_params);
        assert_eq!(pair_with_x.len(), NUM_LIMBS * 2);

        let (pair_with_x_x, pair_with_x_y) = pair_with_x.split_at(NUM_LIMBS);
        let (pair_with_generator_x, pair_with_generator_y) = pair_with_generator.split_at(NUM_LIMBS);
        BlockAggregationOutputDataWitness {
            vk_root: vks_tree_root,
            final_price_commitment,
            blocks_commitments: public_input_data.iter().map(|data| data.block_commitment).collect(),
            aggregation_output_data: NodeAggregationOutputDataWitness {
                pair_with_x_x: pair_with_x_x.to_vec().try_into().unwrap(),
                pair_with_x_y: pair_with_x_y.to_vec().try_into().unwrap(),
                pair_with_generator_x: pair_with_generator_x.to_vec().try_into().unwrap(),
                pair_with_generator_y: pair_with_generator_y.to_vec().try_into().unwrap(),
                _marker: Default::default(),
            },
            _marker: Default::default(),
        }
    }

    pub fn calc_commitment(&self) -> E::Fr {
        let params = PoseidonParams::<E, 2, 3>::default();
        let mut input = Vec::new();
        input.push(self.vk_root);
        input.push(self.final_price_commitment);
        for block_commitment in self.blocks_commitments.iter() {
            input.push(*block_commitment);
        }
        input.extend(self.aggregation_output_data.pair_with_x_x);
        input.extend(self.aggregation_output_data.pair_with_x_y);
        input.extend(self.aggregation_output_data.pair_with_generator_x);
        input.extend(self.aggregation_output_data.pair_with_generator_y);

        GenericSponge::hash(&input, &params, None)[0]
    }
}

pub fn make_aggregate<'a, E: RescueEngine, P: OldCSParams<E>>(
    proofs: &[Proof<E, P>],
    vks: &[VerificationKey<E, P>],
    params: &'a DefaultRescueParams<E>,
    rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> Result<[E::G1Affine; 2], SynthesisError> {
    assert_eq!(
        proofs.len(),
        vks.len(),
        "number of proofs is not equal to number of VKs"
    );

    let mut channel = GenericSponge::<E, 2, 3>::new();
    for p in proofs.iter() {
        let as_fe = p.into_witness_for_params(rns_params)?;

        for fe in as_fe.into_iter() {
            channel.absorb(fe, params);
        }
    }
    channel.pad_if_necessary();
    let aggregation_challenge = channel.squeeze(params).unwrap();

    let mut pair_with_generator = <E::G1 as CurveProjective>::zero();
    let mut pair_with_x = <E::G1 as CurveProjective>::zero();

    let mut current = aggregation_challenge;

    use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs::verifier::verify_and_aggregate;
    for (vk, proof) in vks.iter().zip(proofs.iter()) {
        let (is_valid, [for_gen, for_x]) = verify_and_aggregate::<
            _,
            _,
            GenericTranscriptForRNSInFieldOnly<E, DefaultRescueParams<E>, 2, 3>,
        >(proof, vk, Some((params, rns_params)))
        .expect("should verify");

        assert!(is_valid, "individual proof is not valid");

        let contribution = for_gen.mul(current.into_repr());
        CurveProjective::add_assign(&mut pair_with_generator, &contribution);

        let contribution = for_x.mul(current.into_repr());
        CurveProjective::add_assign(&mut pair_with_x, &contribution);

        current.mul_assign(&aggregation_challenge);
    }

    let pair_with_generator = CurveProjective::into_affine(&pair_with_generator);
    let pair_with_x = CurveProjective::into_affine(&pair_with_x);

    assert!(!pair_with_generator.is_zero());
    assert!(!pair_with_x.is_zero());

    Ok([pair_with_generator, pair_with_x])
}

fn decompose_point_into_limbs<E: Engine>(
    src: &E::G1Affine,
    dst: &mut Vec<E::Fr>,
    params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) {
    use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::utils;
    let mut new_params = params.clone();
    new_params.set_prefer_single_limb_allocation(true);
    let params = &new_params;
    utils::add_point(src, dst, params);
}

pub fn create_recursive_circuit_setup<'a>(
    num_proofs_to_check: usize,
    num_inputs: usize,
    vk_tree_depth: usize,
) -> Result<NewSetup<Bn256, RecursiveAggregationCircuitBn256<'a>>, SynthesisError> {
    let mut assembly = SetupAssembly::<
        Bn256,
        Width4WithCustomGates,
        SelectorOptimizedWidth4MainGateWithDNext,
    >::new();

    let recursive_circuit = RecursiveAggregationCircuitBn256 {
        num_proofs_to_check,
        num_inputs,
        vk_tree_depth,
        vk_root: None,
        vk_witnesses: None,
        vk_auth_paths: None,
        proof_ids: None,
        proofs: None,
        rescue_params: &RESCUE_PARAMETERS,
        poseidon_params: &POSEIDON_PARAMETERS,
        rns_params: &RNS_PARAMETERS,
        aux_data: BN256AuxData::new(),
        transcript_params: &RESCUE_PARAMETERS,

        public_input_data: None,
        g2_elements: None,

        input_commitment: None,
        _m: std::marker::PhantomData,
    };

    recursive_circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let worker = Worker::new();
    let setup = assembly.create_setup(&worker)?;

    Ok(setup)
}
type NewVKAndSetUp<'a> = (
    NewVerificationKey<Bn256, RecursiveAggregationCircuitBn256<'a>>,
    NewSetup<Bn256, RecursiveAggregationCircuitBn256<'a>>,
);
pub fn create_recursive_circuit_vk_and_setup<'a>(
    num_proofs_to_check: usize,
    num_inputs: usize,
    vk_tree_depth: usize,
    crs: &Crs<Bn256, CrsForMonomialForm>,
) -> Result<NewVKAndSetUp<'a>, SynthesisError> {
    let worker = Worker::new();

    let setup = create_recursive_circuit_setup(num_proofs_to_check, num_inputs, vk_tree_depth)?;

    let vk = NewVerificationKey::<Bn256, RecursiveAggregationCircuitBn256<'a>>::from_setup(
        &setup, &worker, crs,
    )?;

    Ok((vk, setup))
}

pub struct RecursiveAggregationDataStorage<E: Engine> {
    pub indexes_of_used_proofs: Vec<u8>,
    pub num_inputs: usize,
    pub expected_recursive_input: E::Fr,
    pub output: BlockAggregationOutputDataWitness<E>
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockPublicInputData<E: Engine> {
    pub block_commitment: E::Fr,
    pub price_commitment: E::Fr,
    pub prices_num: E::Fr,
    pub prices_base_sum: E::Fr,
}

impl<E: Engine> BlockPublicInputData<E> {
    pub fn hash<P: HashParams<E, RATE, WIDTH>, const RATE: usize, const WIDTH: usize>(
        &self,
        params: &P,
    ) -> E::Fr {
        GenericSponge::hash(
            &[
                self.block_commitment,
                self.price_commitment,
                self.prices_num,
                self.prices_base_sum,
            ],
            params,
            None,
        )[0]
    }
}

pub fn create_zklink_recursive_aggregate(
    tree_depth: usize,
    num_inputs: usize,
    all_known_vks: &[VerificationKey<Bn256, PlonkCsWidth4WithNextStepParams>],
    proofs: &[Proof<Bn256, PlonkCsWidth4WithNextStepParams>],
    public_input_data: &[BlockPublicInputData<Bn256>],
    vk_indexes: &[usize],
    g2_elements: &[<Bn256 as Engine>::G2Affine; 2],
) -> Result<RecursiveAggregationDataStorage<Bn256>, SynthesisError> {
    assert_eq!(num_inputs, ZKLINK_NUM_INPUTS, "invalid number of inputs");
    assert_eq!(
        proofs.len(),
        public_input_data.len(),
        "The different number of proofs and public_input_data"
    );
    public_input_data
        .iter()
        .zip(proofs.iter())
        .for_each(|(data, proof)| {
            assert_eq!(data.hash(&*POSEIDON_PARAMETERS), proof.input_values[0]);
        });

    let rns_params = &*RNS_PARAMETERS;
    let rescue_params = &*RESCUE_PARAMETERS;

    assert!(tree_depth <= 8, "tree must not be deeper than 8");
    let (max_index, (vks_tree, _)) = create_vks_tree(all_known_vks, tree_depth)?;

    let mut vks_to_aggregate = vec![];
    let mut short_indexes = vec![];
    for &index in vk_indexes.iter() {
        assert!(index <= max_index);
        assert!(
            index < 256,
            "for now tree should not be larger than 256 elements"
        );
        let vk = &all_known_vks[index];
        vks_to_aggregate.push(vk.clone());
        short_indexes.push(index as u8);
    }

    let aggregate = make_aggregate(proofs, &vks_to_aggregate, rescue_params, rns_params)?;
    if Bn256::final_exponentiation(&Bn256::miller_loop(&[
        (&aggregate[0].prepare(), &g2_elements[0].prepare()),
        (&aggregate[1].prepare(), &g2_elements[1].prepare()),
    ]))
        .ok_or(SynthesisError::Unsatisfiable)?
        != <Bn256 as Engine>::Fqk::one() {
        println!("Recursive aggreagete is invalid");
        return Err(SynthesisError::Unsatisfiable);
    }

    let vks_tree_root = vks_tree.get_commitment();

    let output = BlockAggregationOutputDataWitness::new(
        vks_tree_root,
        &aggregate,
        public_input_data,
        rns_params
    );

    let new = RecursiveAggregationDataStorage::<Bn256> {
        indexes_of_used_proofs: short_indexes,
        num_inputs: ZKLINK_NUM_INPUTS,
        expected_recursive_input: output.calc_commitment(),
        output,
    };

    Ok(new)
}

/// Internally uses RescueTranscriptForRNS for Ethereum
#[allow(clippy::too_many_arguments)]
pub fn proof_recursive_aggregate_for_zklink<'a>(
    tree_depth: usize,
    num_inputs: usize,
    all_known_vks: &[VerificationKey<Bn256, PlonkCsWidth4WithNextStepParams>],
    proofs: &[Proof<Bn256, PlonkCsWidth4WithNextStepParams>],
    public_input_data: &[BlockPublicInputData<Bn256>],
    vk_indexes: &[usize],
    recursive_circuit_vk: &NewVerificationKey<Bn256, RecursiveAggregationCircuitBn256<'a>>,
    recursive_circuit_setup: &NewSetup<Bn256, RecursiveAggregationCircuitBn256<'a>>,
    crs: &Crs<Bn256, CrsForMonomialForm>,
    quick_check_if_satisifed: bool,
    worker: &Worker,
) -> Result<NewProof<Bn256, RecursiveAggregationCircuitBn256<'a>>, SynthesisError> {
    assert_eq!(
        proofs.len(),
        public_input_data.len(),
        "The different number of proofs and public_input_data"
    );
    public_input_data
        .iter()
        .zip(proofs.iter())
        .for_each(|(data, proof)| {
            assert_eq!(data.hash(&*POSEIDON_PARAMETERS), proof.input_values[0]);
        });

    let rns_params = &*RNS_PARAMETERS;
    let rescue_params = &*RESCUE_PARAMETERS;

    let num_proofs_to_check = proofs.len();

    assert!(tree_depth <= 8, "tree must not be deeper than 8");
    let (max_index, (vks_tree, tree_witnesses)) = create_vks_tree(all_known_vks, tree_depth)?;

    let mut queries = vec![];

    let proofs_to_aggregate = proofs;
    let mut vks_to_aggregate = vec![];
    for &proof_id in vk_indexes.iter() {
        assert!(proof_id <= max_index);
        assert!(
            proof_id < 256,
            "for now tree should not be larger than 256 elements"
        );

        let vk = &all_known_vks[proof_id];
        vks_to_aggregate.push(vk.clone());

        let leaf_values = vk
            .into_witness_for_params(rns_params)
            .expect("must transform into limbed witness");

        let values_per_leaf = leaf_values.len();
        let intra_leaf_indexes_to_query: Vec<_> =
            ((proof_id * values_per_leaf)..((proof_id + 1) * values_per_leaf)).collect();
        let q = vks_tree.produce_query(intra_leaf_indexes_to_query, &tree_witnesses);

        assert_eq!(q.values(), &leaf_values[..]);

        queries.push(q.path().to_vec());
    }

    let aggregate = make_aggregate(
        proofs_to_aggregate,
        &vks_to_aggregate,
        rescue_params,
        rns_params,
    )?;

    let vks_tree_root = vks_tree.get_commitment();

    println!("Assembling input to recursive circuit");
    let circuit_output = BlockAggregationOutputDataWitness::new(
        vks_tree_root,
        &aggregate,
        public_input_data,
        rns_params,
    );
    let expected_input = circuit_output.calc_commitment();

    assert_eq!(recursive_circuit_setup.num_inputs, 1);
    // assert_eq!(recursive_circuit_vk.total_lookup_entries_length, 0);

    let mut g2_bases = [<<Bn256 as Engine>::G2Affine as CurveAffine>::zero(); 2];
    g2_bases.copy_from_slice(&crs.g2_monomial_bases.as_ref()[..]);

    let aux_data = BN256AuxData::new();

    let recursive_circuit_with_witness = RecursiveAggregationCircuitBn256 {
        num_proofs_to_check,
        num_inputs,
        vk_tree_depth: tree_depth,
        vk_root: Some(vks_tree_root),
        vk_witnesses: Some(vks_to_aggregate),
        vk_auth_paths: Some(queries),
        proof_ids: Some(vk_indexes.to_vec()),
        proofs: Some(proofs_to_aggregate.to_vec()),
        rescue_params,
        poseidon_params: &POSEIDON_PARAMETERS,
        rns_params,
        aux_data,
        transcript_params: rescue_params,

        public_input_data: Some(public_input_data.to_vec()),
        g2_elements: Some(g2_bases),

        input_commitment: Some(expected_input),
        _m: std::marker::PhantomData,
    };

    if quick_check_if_satisifed {
        println!("Checking if satisfied");
        let mut assembly = TrivialAssembly::<
            Bn256,
            Width4WithCustomGates,
            SelectorOptimizedWidth4MainGateWithDNext,
        >::new();
        recursive_circuit_with_witness
            .synthesize(&mut assembly)
            .expect("must synthesize");
        println!(
            "Using {} gates for {} proofs aggregated",
            assembly.n(),
            num_proofs_to_check
        );
        let is_satisfied = assembly.is_satisfied();
        println!("Is satisfied = {}", is_satisfied);

        if !is_satisfied {
            return Err(SynthesisError::Unsatisfiable);
        }
    }

    let mut assembly = ProvingAssembly::<
        Bn256,
        Width4WithCustomGates,
        SelectorOptimizedWidth4MainGateWithDNext,
    >::new();
    recursive_circuit_with_witness
        .synthesize(&mut assembly)
        .expect("must synthesize");
    assembly.finalize();

    let transcript_params = (rescue_params, rns_params);
    let timer = std::time::Instant::now();
    let proof = assembly.create_proof::<_, RescueTranscriptForRecursion<Bn256>>(
        worker,
        recursive_circuit_setup,
        crs,
        Some(transcript_params),
    )?;
    println!(
        "Aggregated {} proofs circuit create proof spend {}",
        num_proofs_to_check,
        timer.elapsed().as_secs()
    );

    assert_eq!(
        proof.inputs[0], expected_input,
        "expected input is not equal to one in a circuit"
    );

    use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;

    let is_valid = verify::<_, _, RescueTranscriptForRecursion<Bn256>>(
        recursive_circuit_vk,
        &proof,
        Some(transcript_params),
    )?;

    if !is_valid {
        println!("Recursive circuit proof is invalid");
        return Err(SynthesisError::Unsatisfiable);
    }

    Ok(proof)
}
