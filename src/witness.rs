use franklin_crypto::bellman::bn256::Bn256;
use franklin_crypto::bellman::{CurveAffine, CurveProjective, Engine, Field, PrimeField, PrimeFieldRepr, ScalarEngine, SynthesisError};
use franklin_crypto::bellman::kate_commitment::{Crs, CrsForMonomialForm};
use franklin_crypto::bellman::plonk::better_better_cs::cs::{Circuit, ProvingAssembly, SetupAssembly, TrivialAssembly, Width4MainGateWithDNext};
use franklin_crypto::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams;
use franklin_crypto::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use franklin_crypto::bellman::worker::Worker;
use franklin_crypto::plonk::circuit::bigint::field::RnsParameters;
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::aux_data::{AuxData, BN256AuxData};
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::without_flag_unchecked::WrapperUnchecked;
use franklin_crypto::plonk::circuit::verifier_circuit::channel::RescueChannelGadget;
use franklin_crypto::plonk::circuit::verifier_circuit::data_structs::IntoLimbedWitness;
use franklin_crypto::plonk::circuit::Width4WithCustomGates;
use franklin_crypto::rescue::{RescueEngine, StatefulRescue};
use franklin_crypto::rescue::bn256::Bn256RescueParams;
use franklin_crypto::bellman::plonk::better_better_cs::{
    setup::{Setup as NewSetup, VerificationKey as NewVerificationKey},
    proof::Proof as NewProof
};
use franklin_crypto::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use crate::circuit::{RecursiveAggregationCircuit, ZKLINK_NUM_INPUTS};
use crate::utils::bytes_to_keep;
use crate::vks_tree::{create_vks_tree, RESCUE_PARAMETERS, RNS_PARAMETERS};

pub type RecursiveAggregationCircuitBn256<'a> = RecursiveAggregationCircuit<
    'a,
    Bn256,
    PlonkCsWidth4WithNextStepParams,
    WrapperUnchecked<'a, Bn256>,
    BN256AuxData,
    RescueChannelGadget<Bn256>,
>;

pub fn make_aggregate<'a, E: RescueEngine, P: OldCSParams<E>>(
    proofs: &[Proof<E, P>],
    vks: &[VerificationKey<E, P>],
    params: &'a E::Params,
    rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> Result<[E::G1Affine; 2], SynthesisError> {
    use franklin_crypto::bellman::plonk::better_cs::verifier::verify_and_aggregate;
    use franklin_crypto::rescue::rescue_transcript::RescueTranscriptForRNS;

    assert_eq!(
        proofs.len(),
        vks.len(),
        "number of proofs is not equal to number of VKs"
    );

    let mut channel = StatefulRescue::<E>::new(params);
    for p in proofs.iter() {
        let as_fe = p.into_witness_for_params(rns_params)?;

        for fe in as_fe.into_iter() {
            channel.absorb_single_value(fe);
        }
    }

    channel.pad_if_necessary();

    let aggregation_challenge: E::Fr = channel.squeeze_out_single();

    let mut pair_with_generator = E::G1::zero();
    let mut pair_with_x = E::G1::zero();

    let mut current = aggregation_challenge;

    for (vk, proof) in vks.iter().zip(proofs.iter()) {
        let (is_valid, [for_gen, for_x]) = verify_and_aggregate::<_, _, RescueTranscriptForRNS<E>>(
            proof,
            vk,
            Some((params, rns_params)),
        )
        .expect("should verify");

        assert!(is_valid, "individual proof is not valid");

        let contribution = for_gen.mul(current.into_repr());
        pair_with_generator.add_assign(&contribution);

        let contribution = for_x.mul(current.into_repr());
        pair_with_x.add_assign(&contribution);

        current.mul_assign(&aggregation_challenge);
    }

    let pair_with_generator = pair_with_generator.into_affine();
    let pair_with_x = pair_with_x.into_affine();

    assert!(!pair_with_generator.is_zero());
    assert!(!pair_with_x.is_zero());

    Ok([pair_with_generator, pair_with_x])
}

pub fn make_public_input_and_limbed_aggregate<E: Engine, P: OldCSParams<E>>(
    vks_root: E::Fr,
    proof_indexes: &[usize],
    proofs: &[Proof<E, P>],
    aggregate: &[E::G1Affine; 2],
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> (E::Fr, Vec<E::Fr>) {
    use std::io::Write;

    let (input, limbed_aggregate) = make_public_input_for_hashing_and_limbed_aggreagated(
        vks_root,
        proof_indexes,
        proofs,
        aggregate,
        rns_params,
    );

    let mut hash_output = [0u8; 32];

    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(&input);
    let result = hasher.finalize();

    (&mut hash_output[..])
        .write_all(&result)
        .expect("must write");

    let keep = bytes_to_keep::<E>();
    for output in hash_output.iter_mut().take(32 - keep) {
        *output = 0;
    }

    let mut repr = <E::Fr as PrimeField>::Repr::default();
    repr.read_be(&hash_output[..]).expect("must read BE repr");

    let fe = E::Fr::from_repr(repr).expect("must be valid representation");

    (fe, limbed_aggregate)
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
    use franklin_crypto::plonk::circuit::verifier_circuit::utils::{self};

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
    let mut assembly =
        SetupAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
    let rescue_params = Bn256RescueParams::new_checked_2_into_1();
    let aux_data = BN256AuxData::new();

    // let transcript_params = (&rescue_params, &rns_params);

    let recursive_circuit = RecursiveAggregationCircuitBn256 {
        num_proofs_to_check,
        num_inputs,
        vk_tree_depth,
        vk_root: None,
        vk_witnesses: None,
        vk_auth_paths: None,
        proof_ids: None,
        proofs: None,
        rescue_params: &rescue_params,
        rns_params: &rns_params,
        aux_data,
        transcript_params: &rescue_params,

        g2_elements: None,

        _m: std::marker::PhantomData,
    };

    recursive_circuit.synthesize(&mut assembly)?;

    use franklin_crypto::bellman::worker::*;
    let worker = Worker::new();

    assembly.finalize();
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
    use franklin_crypto::bellman::worker::*;
    let worker = Worker::new();

    let setup = create_recursive_circuit_setup(num_proofs_to_check, num_inputs, vk_tree_depth)?;

    let vk = NewVerificationKey::<Bn256, RecursiveAggregationCircuitBn256<'a>>::from_setup(
        &setup, &worker, crs,
    )?;

    Ok((vk, setup))
}

pub struct RecursiveAggreagationDataStorage<E: Engine> {
    pub indexes_of_used_proofs: Vec<u8>,
    pub num_inputs: usize,
    pub individual_proofs_inputs: Vec<Vec<E::Fr>>,
    pub tree_root: E::Fr,
    pub expected_recursive_input: E::Fr,
    pub limbed_aggregated_g1_elements: Vec<E::Fr>,
}

pub fn create_zklink_recursive_aggregate(
    tree_depth: usize,
    num_inputs: usize,
    all_known_vks: &[VerificationKey<Bn256, PlonkCsWidth4WithNextStepParams>],
    proofs: &[Proof<Bn256, PlonkCsWidth4WithNextStepParams>],
    vk_indexes: &[usize],
    g2_elements: &[<Bn256 as Engine>::G2Affine; 2],
) -> Result<RecursiveAggreagationDataStorage<Bn256>, SynthesisError> {
    assert_eq!(num_inputs, ZKLINK_NUM_INPUTS, "invalid number of inputs");

    let rns_params = &*RNS_PARAMETERS;
    let rescue_params = &*RESCUE_PARAMETERS;

    assert!(tree_depth <= 8, "tree must not be deeper than 8");
    let (max_index, (vks_tree, _)) = create_vks_tree(all_known_vks, tree_depth)?;

    let mut vks_to_aggregate = vec![];
    let mut short_indexes = vec![];
    let mut individual_proofs_inputs = vec![];
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

    for proof in proofs.iter() {
        individual_proofs_inputs.push(proof.input_values.clone());
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

    let (expected_input, limbed_aggreagate) = make_public_input_and_limbed_aggregate(
        vks_tree_root,
        vk_indexes,
        proofs,
        &aggregate,
        rns_params,
    );

    let new = RecursiveAggreagationDataStorage::<Bn256> {
        indexes_of_used_proofs: short_indexes,
        num_inputs: ZKLINK_NUM_INPUTS,
        individual_proofs_inputs,
        tree_root: vks_tree_root,
        expected_recursive_input: expected_input,
        limbed_aggregated_g1_elements: limbed_aggreagate,
    };

    Ok(new)
}

/// Internally uses RollingKeccakTranscript for Ethereum
#[allow(clippy::too_many_arguments)]
pub fn proof_recursive_aggregate_for_zklink<'a>(
    tree_depth: usize,
    num_inputs: usize,
    all_known_vks: &[VerificationKey<Bn256, PlonkCsWidth4WithNextStepParams>],
    proofs: &[Proof<Bn256, PlonkCsWidth4WithNextStepParams>],
    vk_indexes: &[usize],
    recursive_circuit_vk: &NewVerificationKey<Bn256, RecursiveAggregationCircuitBn256<'a>>,
    recursive_circuit_setup: &NewSetup<Bn256, RecursiveAggregationCircuitBn256<'a>>,
    crs: &Crs<Bn256, CrsForMonomialForm>,
    quick_check_if_satisifed: bool,
    worker: &Worker,
) -> Result<NewProof<Bn256, RecursiveAggregationCircuitBn256<'a>>, SynthesisError> {
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

    let (expected_input, _) = make_public_input_and_limbed_aggregate(
        vks_tree_root,
        vk_indexes,
        proofs,
        &aggregate,
        rns_params,
    );

    assert_eq!(recursive_circuit_setup.num_inputs, 1);
    assert_eq!(recursive_circuit_vk.total_lookup_entries_length, 0);

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

        g2_elements: Some(g2_bases),

        _m: std::marker::PhantomData,
    };

    if quick_check_if_satisifed {
        println!("Checking if satisfied");
        let mut assembly =
            TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
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

    use franklin_crypto::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;

    let mut assembly =
        ProvingAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
    recursive_circuit_with_witness
        .synthesize(&mut assembly)
        .expect("must synthesize");
    assembly.finalize();

    let timer = std::time::Instant::now();
    let proof = assembly.create_proof::<_, RollingKeccakTranscript<<Bn256 as ScalarEngine>::Fr>>(
        worker,
        recursive_circuit_setup,
        crs,
        None,
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

    use franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;

    let is_valid = verify::<_, _, RollingKeccakTranscript<<Bn256 as ScalarEngine>::Fr>>(
        recursive_circuit_vk,
        &proof,
        None,
    )?;

    if !is_valid {
        println!("Recursive circuit proof is invalid");
        return Err(SynthesisError::Unsatisfiable);
    }

    Ok(proof)
}
