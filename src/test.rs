use advanced_circuit_component::franklin_crypto::bellman::pairing::bn256::{Bn256, Fr};
use advanced_circuit_component::franklin_crypto::bellman::pairing::ff::Field;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::cs::{Circuit, TrivialAssembly};
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::gates::selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::setup::VerificationKey as NewVerificationKey;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs;
use advanced_circuit_component::franklin_crypto::bellman::PrimeField;
use advanced_circuit_component::franklin_crypto::bellman::worker::*;
use advanced_circuit_component::franklin_crypto::plonk::circuit::*;
use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::test::*;
use crate::{proof_recursive_aggregate_for_zklink, RecursiveAggregationCircuitBn256, RescueTranscriptForRecursion};
use crate::test_utils::*;

use crate::vks_tree::{RESCUE_PARAMETERS, RNS_PARAMETERS};
use crate::witness::create_recursive_circuit_vk_and_setup;

#[test]
fn test_two_proofs() {
    let (recursive_circuit, _aggregation_storage) = create_test_block_aggregation_circuit();

    let mut cs = TrivialAssembly::<
        Bn256,
        Width4WithCustomGates,
        SelectorOptimizedWidth4MainGateWithDNext,
    >::new();
    recursive_circuit
        .synthesize(&mut cs)
        .expect("should synthesize");
    println!("Raw number of gates: {}", cs.n());
    cs.finalize();
    println!("Padded number of gates: {}", cs.n());
    assert!(cs.is_satisfied());
    assert_eq!(cs.num_inputs, 1);
}

#[test]
fn create_vk() {
    let crs = open_crs_for_log2_of_size::<true>(22);
    let (vk, _) = create_recursive_circuit_vk_and_setup(2, 1, 3, &crs).unwrap();
    dbg!(vk);
}

#[test]
fn simulate_zklink_proofs() {
    let a = Fr::one();
    let b = Fr::one();

    let mut circuits = vec![];
    for num_steps in vec![18, 40, 25, 35].into_iter() {
        let circuit = TestCircuitWithOneInput::new(BenchmarkCircuitWithOneInput::<Bn256> {
            num_steps,
            a,
            b,
            output: fibbonacci(&a, &b, num_steps),
            _engine_marker: std::marker::PhantomData,
        });

        circuits.push(circuit);
    }

    let rns_params = RNS_PARAMETERS.clone();
    let rescue_params = RESCUE_PARAMETERS.clone();
    let transcript_params = (&rescue_params, &rns_params);

    let crs = open_crs_for_log2_of_size::<true>(24);

    let mut vks = vec![];
    let mut proofs = vec![];

    for circuit in circuits.into_iter() {
        let (vk, proof) = make_vk_and_proof_for_crs::<Bn256, RescueTranscriptForRecursion<Bn256>>(
            circuit,
            transcript_params,
            &crs,
        );

        let valid = better_cs::verifier::verify::<_, _, RescueTranscriptForRecursion<Bn256>>(
            &proof,
            &vk,
            Some(transcript_params),
        )
        .expect("must verify");
        assert!(valid);

        vks.push(vk);
        proofs.push(proof);
    }

    let num_inputs = 2;
    let num_proofs_to_check = 2;
    let tree_depth = 3;

    let (vk_for_recursive_circut, setup) =
        create_recursive_circuit_vk_and_setup(num_proofs_to_check, num_inputs, tree_depth, &crs)
            .expect("must create recursive circuit verification key");

    let proofs_to_check = vec![2, 3];
    let proofs = vec![proofs[2].clone(), proofs[3].clone()];
    let block_input_data = test_public_input_data(num_proofs_to_check);

    let worker = Worker::new();

    let proof = proof_recursive_aggregate_for_zklink(
        tree_depth,
        num_inputs,
        &vks,
        &proofs,
        &block_input_data,
        &proofs_to_check,
        &vk_for_recursive_circut,
        &setup,
        &crs,
        true,
        &worker,
    )
    .expect("must check if satisfied and make a proof");

    use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;
    let is_valid = verify::<_, _, RescueTranscriptForRecursion<Bn256>>(
        &vk_for_recursive_circut,
        &proof,
        Some(transcript_params),
    )
    .expect("must perform verification");

    assert!(is_valid);

    let path = std::path::Path::new("./vk.key");
    let file = std::fs::File::create(path).unwrap();
    let mut writer = std::io::BufWriter::with_capacity(1 << 24, file);

    vk_for_recursive_circut
        .write(&mut writer)
        .expect("must write");

    let path = std::path::Path::new("./proof.proof");
    let file = std::fs::File::create(path).unwrap();
    let mut writer = std::io::BufWriter::with_capacity(1 << 24, file);

    proof.write(&mut writer).expect("must write");

    let mut tmp = vec![];
    vk_for_recursive_circut.write(&mut tmp).expect("must write");

    let vk_deser = NewVerificationKey::<Bn256, RecursiveAggregationCircuitBn256>::read(&tmp[..])
        .expect("must read");

    assert_eq!(
        vk_for_recursive_circut.permutation_commitments,
        vk_deser.permutation_commitments
    );

    let mut tmp = vec![];
    proof.write(&mut tmp).expect("must write");

    use advanced_circuit_component::franklin_crypto::bellman::plonk::better_better_cs::proof::Proof as NewProof;
    let proof_deser =
        NewProof::<Bn256, RecursiveAggregationCircuitBn256>::read(&tmp[..]).expect("must read");

    assert_eq!(
        proof.quotient_poly_opening_at_z,
        proof_deser.quotient_poly_opening_at_z
    );
}

// #[test]
// fn test_verification_from_binary() {
//     let path = std::path::Path::new("./vk.key");
//     let file = std::fs::File::open(path).unwrap();
//     let reader = std::io::BufReader::with_capacity(1 << 24, file);
//
//     let vk_for_recursive_circut =
//         NewVerificationKey::<Bn256, RecursiveAggregationCircuitBn256>::read(reader)
//             .expect("must read");
//
//     let path = std::path::Path::new("./proof.proof");
//     let file = std::fs::File::open(path).unwrap();
//     let reader = std::io::BufReader::with_capacity(1 << 24, file);
//
//     use franklin_crypto::bellman::plonk::better_better_cs::proof::Proof as NewProof;
//     let proof =
//         NewProof::<Bn256, RecursiveAggregationCircuitBn256>::read(reader).expect("must read");
//
//     let rns_params = RNS_PARAMETERS.clone();
//     let rescue_params = RESCUE_PARAMETERS.clone();
//     let transcript_params = (&rescue_params, &rns_params);
//
//     use franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;
//
//     let is_valid = verify::<_, _, RescueTranscriptForRecursion<Bn256>>(
//         &vk_for_recursive_circut,
//         &proof,
//         Some(transcript_params),
//     )
//     .expect("must perform verification");
//
//     assert!(is_valid);
// }

#[test]
fn simulate_many_proofs() {
    let a = Fr::one();
    let b = Fr::one();

    let mut circuits = vec![];
    for num_steps in vec![18, 40, 25, 35].into_iter() {
        let circuit = TestCircuitWithOneInput::new(BenchmarkCircuitWithOneInput::<Bn256> {
            num_steps,
            a,
            b,
            output: fibbonacci(&a, &b, num_steps),
            _engine_marker: std::marker::PhantomData,
        });

        circuits.push(circuit);
    }

    let rns_params = RNS_PARAMETERS.clone();
    let rescue_params = RESCUE_PARAMETERS.clone();
    let transcript_params = (&rescue_params, &rns_params);

    let crs = open_crs_for_log2_of_size::<true>(24);

    let mut vks = vec![];
    let mut proofs = vec![];

    for circuit in circuits.into_iter() {
        let (vk, proof) = make_vk_and_proof_for_crs::<Bn256, RescueTranscriptForRecursion<Bn256>>(
            circuit,
            transcript_params,
            &crs,
        );

        let valid = better_cs::verifier::verify::<_, _, RescueTranscriptForRecursion<Bn256>>(
            &proof,
            &vk,
            Some(transcript_params),
        )
        .expect("must verify");
        assert!(valid);

        vks.push(vk);
        proofs.push(proof);
    }

    let num_inputs = 2;
    let tree_depth = 3;

    let num_proofs_to_check = 2;

    // this is dummy
    println!("Creating setup and verification key");
    let (vk_for_recursive_circut, setup) =
        create_recursive_circuit_vk_and_setup(num_proofs_to_check, num_inputs, tree_depth, &crs)
            .expect("must create recursive circuit verification key");

    let proofs_indexes_to_check = vec![2, 3];
    assert_eq!(proofs_indexes_to_check.len(), num_proofs_to_check);

    let proofs_to_check = vec![proofs[2].clone(), proofs[3].clone()];
    assert_eq!(proofs_to_check.len(), num_proofs_to_check);

    let worker = Worker::new();

    println!("Creating proof");
    let block_input_data = test_public_input_data(num_proofs_to_check);
    let _ = proof_recursive_aggregate_for_zklink(
        tree_depth,
        num_inputs,
        &vks,
        &proofs_to_check,
        &block_input_data,
        &proofs_indexes_to_check,
        &vk_for_recursive_circut,
        &setup,
        &crs,
        true,
        &worker,
    )
    .expect("must check if satisfied and make a proof");
}

#[test]
fn test_all_aggregated_proofs() {
    const TREE_DEPTH: usize = 3;
    const VK_LEAF_NUM: usize = 2usize.pow((TREE_DEPTH - 1) as u32);

    let mut circuits = vec![];
    let vks_steps = (1..=VK_LEAF_NUM).collect::<Vec<_>>();
    let diff_input_b = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    for &num_steps in &vks_steps {
        for i in diff_input_b {
            let a = Fr::from_str(&i.to_string()).unwrap();
            let b = Fr::one();
            let circuit = TestCircuitWithOneInput::new(BenchmarkCircuitWithOneInput::<Bn256> {
                num_steps,
                a,
                b,
                output: fibbonacci(&a, &b, num_steps),
                _engine_marker: std::marker::PhantomData,
            });

            circuits.push(circuit);
        }
    }

    let rns_params = RNS_PARAMETERS.clone();
    let rescue_params = RESCUE_PARAMETERS.clone();
    let transcript_params = (&rescue_params, &rns_params);

    let crs = open_crs_for_log2_of_size::<true>(20);

    let mut vks = vec![];
    let mut proofs = vec![];

    for (index, circuit) in circuits.into_iter().enumerate() {
        let (vk, proof) = make_vk_and_proof_for_crs::<Bn256, RescueTranscriptForRecursion<Bn256>>(
            circuit,
            transcript_params,
            &crs,
        );

        let valid = better_cs::verifier::verify::<_, _, RescueTranscriptForRecursion<Bn256>>(
            &proof,
            &vk,
            Some(transcript_params),
        )
        .expect("must verify");
        assert!(valid);

        if index % diff_input_b.len() == 0 {
            vks.push(vk)
        };
        proofs.push(proof);
    }

    let num_inputs = 2;
    let num_proofs_to_checks = vec![1, 4, 8, 18, 36];
    let crs_degrees = vec![22, 23, 24, 25, 26];

    for (aggregated_proofs_num, crs_degree) in num_proofs_to_checks.into_iter().zip(crs_degrees) {
        // this is dummy
        println!(
            "Creating [proofs_num:{}, crs_degree:{}] setup and verification key",
            aggregated_proofs_num, crs_degree
        );
        let crs = open_crs_for_log2_of_size::<true>(crs_degree);
        let (vk_for_recursive_circuit, setup) = create_recursive_circuit_vk_and_setup(
            aggregated_proofs_num,
            num_inputs,
            TREE_DEPTH,
            &crs,
        )
        .expect("must create recursive circuit verification key");

        let aggregated_proofs_indexes = (0..aggregated_proofs_num)
            .map(|i| i / diff_input_b.len())
            .collect::<Vec<_>>();
        let aggregated_proofs = &proofs[0..aggregated_proofs_num];

        let worker = Worker::new();
        println!(
            "Creating [proofs_num:{}, crs_degree:{}] proof",
            aggregated_proofs_num, crs_degree
        );
        let block_input_data = test_public_input_data(aggregated_proofs_num);
        let _ = proof_recursive_aggregate_for_zklink(
            TREE_DEPTH,
            num_inputs,
            &vks,
            aggregated_proofs,
            &block_input_data,
            &aggregated_proofs_indexes,
            &vk_for_recursive_circuit,
            &setup,
            &crs,
            true,
            &worker,
        )
        .expect("must check if satisfied and make a proof");
    }
}
