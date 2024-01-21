use cs_derive::*;
use derivative::Derivative;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use advanced_circuit_component::traits::*;
use advanced_circuit_component::franklin_crypto::bellman::bn256::{Bn256, Fr};
use advanced_circuit_component::franklin_crypto::bellman::{CurveAffine, CurveProjective, Engine, Field, PrimeField, PrimeFieldRepr, SynthesisError};
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
        limbed_aggregate: &[E::Fr],
        block_commitment: &[E::Fr],
        final_price_commitment: E::Fr,
    ) -> Self {
        use advanced_circuit_component::recursion::recursion_tree::NUM_LIMBS;
        assert_eq!(limbed_aggregate.len(), NUM_LIMBS * 4);
        let (pair_with_generator_x, left) = limbed_aggregate.split_at(NUM_LIMBS);
        let (pair_with_generator_y, left) = left.split_at(NUM_LIMBS);
        let (pair_with_x_x, left) = left.split_at(NUM_LIMBS);
        let (pair_with_x_y, _left) = left.split_at(NUM_LIMBS);
        BlockAggregationOutputDataWitness {
            vk_root: vks_tree_root,
            final_price_commitment,
            blocks_commitments: block_commitment.to_vec(),
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

pub fn make_public_input_and_limbed_aggregate<E: Engine>(
    vks_root: E::Fr,
    aggregate: &[E::G1Affine; 2],
    final_price_commitment: E::Fr,
    public_input_data: &[BlockPublicInputData<E>],
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> (E::Fr, Vec<E::Fr>) {
    let (input, limbed_aggregate) = make_public_input_as_fr_for_hashing_and_limbed_aggreagated(
        vks_root,
        aggregate,
        final_price_commitment,
        rns_params,
        public_input_data,
    );

    let params = PoseidonParams::<E, 2, 3>::default();
    let hash = GenericSponge::hash(&input, &params, None)[0];
    (hash, limbed_aggregate)
}

fn make_public_input_for_hashing_and_limbed_aggreagated<E: Engine, P: OldCSParams<E>>(
    vks_root: E::Fr,
    proof_indexes: &[usize],
    proofs: &[Proof<E, P>],
    aggregate: &[E::G1Affine; 2],
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> (Vec<u8>, Vec<E::Fr>) {
    let mut result = vec![];

    add_field_element(&vks_root, &mut result);
    for idx in proof_indexes.iter() {
        assert!(*idx < 256);
        result.push(*idx as u8);
    }

    for proof in proofs.iter() {
        for input in proof.input_values.iter() {
            add_field_element(input, &mut result);
        }
    }

    add_point(&aggregate[0], &mut result, rns_params);
    add_point(&aggregate[1], &mut result, rns_params);

    let mut limbed_aggreagate = vec![];
    decompose_point_into_limbs(&aggregate[0], &mut limbed_aggreagate, rns_params);
    decompose_point_into_limbs(&aggregate[1], &mut limbed_aggreagate, rns_params);

    (result, limbed_aggreagate)
}

fn make_public_input_as_fr_for_hashing_and_limbed_aggreagated<E: Engine>(
    vks_root: E::Fr,
    aggregate: &[E::G1Affine; 2],
    final_price_commitment: E::Fr,
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    public_input_data: &[BlockPublicInputData<E>],
) -> (Vec<E::Fr>, Vec<E::Fr>) {
    let mut result = vec![];
    result.push(vks_root);

    result.push(final_price_commitment);
    for input_data in public_input_data.iter() {
        result.push(input_data.block_commitment);
    }

    decompose_point_into_limbs(&aggregate[1], &mut result, rns_params);
    decompose_point_into_limbs(&aggregate[0], &mut result, rns_params);

    let mut limbed_aggreagate = vec![];
    decompose_point_into_limbs(&aggregate[1], &mut limbed_aggreagate, rns_params);
    decompose_point_into_limbs(&aggregate[0], &mut limbed_aggreagate, rns_params);

    (result, limbed_aggreagate)
}

fn add_field_element<F: PrimeField>(src: &F, dst: &mut Vec<u8>) {
    let repr = src.into_repr();

    let mut buffer = [0u8; 32];
    repr.write_be(&mut buffer[..]).expect("must write");

    dst.extend_from_slice(&buffer);
}

fn add_point<E: Engine>(
    src: &E::G1Affine,
    dst: &mut Vec<u8>,
    params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) {
    let mut tmp_dest = vec![];
    decompose_point_into_limbs(src, &mut tmp_dest, params);

    for p in tmp_dest.into_iter() {
        add_field_element(&p, dst);
    }
}

fn decompose_point_into_limbs<E: Engine>(
    src: &E::G1Affine,
    dst: &mut Vec<E::Fr>,
    params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) {
    use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::utils::{
        self,
    };

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
    pub block_commitments: Vec<E::Fr>,
    pub vks_tree_root: E::Fr,
    pub expected_recursive_input: E::Fr,
    pub price_commitment: E::Fr,
    pub limbed_aggregated_g1_elements: Vec<E::Fr>,
}

impl<E: Engine> RecursiveAggregationDataStorage<E> {
    pub fn generate_witness(&self) -> BlockAggregationOutputDataWitness<E> {
        BlockAggregationOutputDataWitness::new(
            self.vks_tree_root,
            &self.limbed_aggregated_g1_elements,
            &self.block_commitments,
            self.price_commitment,
        )
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockPublicInputData<E: Engine> {
    pub block_commitment: E::Fr,
    pub price_commitment: E::Fr,
}

impl<E: Engine> BlockPublicInputData<E> {
    pub fn hash<P: HashParams<E, RATE, WIDTH>, const RATE: usize, const WIDTH: usize>(
        &self,
        params: &P,
    ) -> E::Fr {
        GenericSponge::hash(
            &[self.block_commitment, self.price_commitment],
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
    let block_commitments = public_input_data
        .iter()
        .zip(proofs.iter())
        .map(|(data, proof)| {
            assert_eq!(data.hash(&*POSEIDON_PARAMETERS), proof.input_values[0]);
            data.block_commitment
        })
        .collect::<Vec<_>>();

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

    let valid = Bn256::final_exponentiation(&Bn256::miller_loop(&[
        (&aggregate[0].prepare(), &g2_elements[0].prepare()),
        (&aggregate[1].prepare(), &g2_elements[1].prepare()),
    ]))
    .ok_or(SynthesisError::Unsatisfiable)?
        == <Bn256 as Engine>::Fqk::one();

    if !valid {
        println!("Recursive aggreagete is invalid");
        return Err(SynthesisError::Unsatisfiable);
    }

    let vks_tree_root = vks_tree.get_commitment();

    let price_commitment = public_input_data
        .iter()
        .fold(Default::default(), |mut acc: Fr, el| {
            acc.square();
            acc.add_assign(&el.price_commitment);
            acc
        });
    let (expected_input, limbed_aggreagate) = make_public_input_and_limbed_aggregate(
        vks_tree_root,
        &aggregate,
        price_commitment,
        public_input_data,
        rns_params,
    );

    let new = RecursiveAggregationDataStorage::<Bn256> {
        indexes_of_used_proofs: short_indexes,
        num_inputs: ZKLINK_NUM_INPUTS,
        block_commitments,
        vks_tree_root,
        expected_recursive_input: expected_input,
        price_commitment,
        limbed_aggregated_g1_elements: limbed_aggreagate,
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
    let price_commitment = public_input_data.iter().fold(Fr::zero(), |mut acc, el| {
        acc.square();
        acc.add_assign(&el.price_commitment);
        acc
    });
    let (expected_input, _) = make_public_input_and_limbed_aggregate(
        vks_tree_root,
        &aggregate,
        price_commitment,
        public_input_data,
        rns_params,
    );

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
