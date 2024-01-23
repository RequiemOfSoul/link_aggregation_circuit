use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::aux_data::{AuxData, BN256AuxData};
use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::without_flag_unchecked::WrapperUnchecked;
use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::test::{BenchmarkCircuit, BenchmarkCircuitWithOneInput, fibbonacci};
use advanced_circuit_component::rescue_poseidon::{GenericSponge, PoseidonParams};
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs::cs::{Circuit as OldCircuit, ConstraintSystem as OldConstraintSystem};
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs::generator::GeneratorAssembly4WithNextStep as OldActualAssembly;
use advanced_circuit_component::franklin_crypto::plonk::circuit::verifier_circuit::data_structs::IntoLimbedWitness;
use advanced_circuit_component::franklin_crypto::bellman::plonk::better_cs::prover::ProverAssembly4WithNextStep as OldActualProver;
use crate::bellman::{CurveAffine, Engine, Field, ScalarEngine, SynthesisError};
use crate::bellman::bn256::{Bn256, Fr};
use crate::bellman::kate_commitment::{Crs, CrsForLagrangeForm, CrsForMonomialForm};
use crate::bellman::plonk::commitments::transcript::{Prng, Transcript};
use crate::bellman::plonk::{Proof, SetupPolynomialsPrecomputations, VerificationKey};
use crate::bellman::plonk::better_cs::verifier::verify_and_aggregate;
use crate::bellman::worker::Worker;
use crate::{BlockPublicInputData, RecursiveAggregationCircuitBn256, RecursiveAggregationDataStorage, RescueTranscriptForRecursion, RescueTranscriptGadgetForRecursion};
use crate::bellman::plonk::fft::cooley_tukey_ntt::{BitReversedOmegas, CTPrecomputations, OmegasInvBitreversed};
use crate::circuit::RecursiveAggregationCircuit;
use crate::vks_tree::{make_vks_tree, POSEIDON_PARAMETERS, RESCUE_PARAMETERS, RNS_PARAMETERS};

pub struct TestCircuitWithOneInput<E: Engine> {
    inner_circuit: BenchmarkCircuitWithOneInput<E>,
    block_commitments: E::Fr,
    price_commitments: E::Fr,
}

impl<E: Engine> TestCircuitWithOneInput<E> {
    pub fn new(circuit: BenchmarkCircuitWithOneInput<E>) -> Self {
        Self {
            inner_circuit: circuit,
            block_commitments: <E as ScalarEngine>::Fr::one(),
            price_commitments: <E as ScalarEngine>::Fr::zero(),
        }
    }
}

impl<E: Engine> OldCircuit<E, OldActualParams> for TestCircuitWithOneInput<E> {
    fn synthesize<CS: OldConstraintSystem<E, OldActualParams>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let params = PoseidonParams::<E, 2, 3>::default();
        // Set public input for test
        cs.alloc_input(|| Ok(GenericSponge::hash(&[self.block_commitments, self.price_commitments], &params, None)[0]))?;
        self.inner_circuit.synthesize(cs)
    }
}

pub struct TestCircuit<E: Engine> {
    inner_circuit: BenchmarkCircuit<E>,
    block_commitments: E::Fr,
    price_commitments: E::Fr,
}

impl<E: Engine> TestCircuit<E> {
    pub fn new(circuit: BenchmarkCircuit<E>) -> Self {
        Self {
            inner_circuit: circuit,
            block_commitments: <E as ScalarEngine>::Fr::one(),
            price_commitments: <E as ScalarEngine>::Fr::zero(),
        }
    }
}

impl<E: Engine> OldCircuit<E, OldActualParams> for TestCircuit<E> {
    fn synthesize<CS: OldConstraintSystem<E, OldActualParams>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let params = PoseidonParams::<E, 2, 3>::default();
        // Set public input for test
        cs.alloc_input(|| Ok(GenericSponge::hash(&[self.block_commitments, self.price_commitments], &params, None)[0]))?;
        self.inner_circuit.synthesize(cs)
    }
}

pub fn make_vk_and_proof_for_crs<E: Engine, T: Transcript<E::Fr>>(
    circuit: TestCircuitWithOneInput<E>,
    transcript_params: <T as Prng<E::Fr>>::InitializationParameters,
    crs: &Crs<E, CrsForMonomialForm>,
) -> (
    VerificationKey<E, OldActualParams>,
    Proof<E, OldActualParams>,
) {
    let worker = Worker::new();
    let mut assembly = OldActualAssembly::<E>::new();
    circuit
        .synthesize(&mut assembly)
        .expect("should synthesize");
    assembly.finalize();
    let setup = assembly.setup(&worker).expect("should setup");

    let verification_key =
        VerificationKey::from_setup(&setup, &worker, crs).expect("should create vk");

    let proof = advanced_circuit_component::franklin_crypto::bellman::plonk::prove_native_by_steps::<E, _, T>(
        &circuit,
        &setup,
        None,
        crs,
        Some(transcript_params.clone()),
    )
        .expect("should create a proof");

    let (is_valid, [_for_gen, _for_x]) =
        verify_and_aggregate::<_, _, T>(&proof, &verification_key, Some(transcript_params))
            .expect("should verify");

    assert!(is_valid);

    (verification_key, proof)
}

pub fn test_public_input_data(agg_block_num: usize) -> Vec<BlockPublicInputData<Bn256>>{
    let data = BlockPublicInputData {
        block_commitment: Fr::one(),
        price_commitment: Fr::zero(),
        prices_num: Fr::zero(),
        prices_base_sum: Fr::zero(),
    };
    let all_block_test_data = vec![data; agg_block_num];
    all_block_test_data
}

pub fn create_test_block_aggregation_circuit() -> (RecursiveAggregationCircuitBn256<'static>, RecursiveAggregationDataStorage<Bn256>) {
    let a = Fr::one();
    let b = Fr::one();

    let num_steps = 40;
    let circuit_0 = TestCircuit::new(BenchmarkCircuit::<Bn256> {
        num_steps,
        a,
        b,
        output: fibbonacci(&a, &b, num_steps),
        _engine_marker: std::marker::PhantomData,
    });

    let num_steps = 18;

    let circuit_1 = TestCircuit::new(BenchmarkCircuit::<Bn256> {
        num_steps,
        a,
        b,
        output: fibbonacci(&a, &b, num_steps),
        _engine_marker: std::marker::PhantomData,
    });

    let transcript_params = (&*RESCUE_PARAMETERS, &*RNS_PARAMETERS);

    let (vk_0, proof_0) =
        make_vk_and_proof::<Bn256, RescueTranscriptForRecursion<Bn256>>(
            circuit_0,
            transcript_params,
        );
    let (vk_1, _proof_1) = make_vk_and_proof::<Bn256, RescueTranscriptForRecursion<Bn256>>(
        circuit_1,
        transcript_params,
    );

    let worker = Worker::new();
    let crs_mons = Crs::<Bn256, CrsForMonomialForm>::crs_42(32, &worker);

    let mut g2_bases = [<<Bn256 as Engine>::G2Affine as CurveAffine>::zero(); 2];
    g2_bases.copy_from_slice(&crs_mons.g2_monomial_bases.as_ref()[..]);

    let aux_data = BN256AuxData::new();

    let vks_in_tree = vec![vk_0.clone(), vk_1.clone()];
    // make in reverse
    let (vks_tree, all_witness_values) =
        make_vks_tree(&vks_in_tree, &*RESCUE_PARAMETERS, &*RNS_PARAMETERS);

    let vks_tree_root = vks_tree.get_commitment();

    let proof_ids = vec![0];

    let mut queries = vec![];
    for &proof_id in proof_ids.iter().take(1) {
        let vk = &vks_in_tree[proof_id];

        let leaf_values = vk
            .into_witness_for_params(&*RNS_PARAMETERS)
            .expect("must transform into limbed witness");

        let values_per_leaf = leaf_values.len();
        let intra_leaf_indexes_to_query: Vec<_> =
            ((proof_id * values_per_leaf)..((proof_id + 1) * values_per_leaf)).collect();
        let q = vks_tree.produce_query(intra_leaf_indexes_to_query, &all_witness_values);

        assert_eq!(q.values(), &leaf_values[..]);

        queries.push(q.path().to_vec());
    }

    let proofs = vec![proof_0];
    let vks = vec![vk_0];

    let block_input_data = test_public_input_data(1);
    let storage = crate::create_zklink_recursive_aggregate(
        1,
        1,
        &vks_in_tree,
        &proofs,
        &block_input_data,
        &proof_ids,
        &g2_bases
    ).unwrap();

    let circuit = RecursiveAggregationCircuit::<
        Bn256,
        OldActualParams,
        WrapperUnchecked<Bn256>,
        _,
        RescueTranscriptGadgetForRecursion<Bn256>,
    > {
        num_proofs_to_check: 1,
        num_inputs: 4,
        vk_tree_depth: 1,
        vk_root: Some(vks_tree_root),
        vk_witnesses: Some(vks),
        vk_auth_paths: Some(queries),
        proof_ids: Some(proof_ids),
        proofs: Some(proofs),
        rescue_params: &*RESCUE_PARAMETERS,
        poseidon_params: &POSEIDON_PARAMETERS,
        rns_params: &*RNS_PARAMETERS,
        aux_data,
        transcript_params: &*RESCUE_PARAMETERS,

        public_input_data: Some(block_input_data),
        g2_elements: Some(g2_bases),

        input_commitment: Some(storage.expected_recursive_input),
        _m: std::marker::PhantomData,
    };
    (circuit, storage)
}

pub fn make_vk_and_proof<E: Engine, T: Transcript<E::Fr>>(
    circuit: TestCircuit<E>,
    transcript_params: <T as Prng<E::Fr>>::InitializationParameters,
) -> (
    VerificationKey<E, OldActualParams>,
    Proof<E, OldActualParams>,
) {
    let worker = Worker::new();
    let mut assembly = OldActualAssembly::<E>::new();
    circuit
        .synthesize(&mut assembly)
        .expect("should synthesize");
    assembly.finalize();
    let setup = assembly.setup(&worker).expect("should setup");

    let crs_mons =
        Crs::<E, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
    let crs_vals =
        Crs::<E, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

    let verification_key =
        VerificationKey::from_setup(&setup, &worker, &crs_mons).expect("should create vk");

    let precomputations = SetupPolynomialsPrecomputations::from_setup(&setup, &worker)
        .expect("should create precomputations");

    let mut prover = OldActualProver::<E>::new();
    circuit.synthesize(&mut prover).expect("should synthesize");
    prover.finalize();

    let size = setup.permutation_polynomials[0].size();

    let omegas_bitreversed =
        BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
    let omegas_inv_bitreversed =
        <OmegasInvBitreversed<E::Fr> as CTPrecomputations<E::Fr>>::new_for_domain_size(
            size.next_power_of_two(),
        );

    println!("BEFORE PROVE");

    let proof = prover
        .prove::<T, _, _>(
            &worker,
            &setup,
            &precomputations,
            &crs_vals,
            &crs_mons,
            &omegas_bitreversed,
            &omegas_inv_bitreversed,
            Some(transcript_params.clone()),
        )
        .expect("should prove");

    println!("DONE");

    let (is_valid, [_for_gen, _for_x]) =
        verify_and_aggregate::<_, _, T>(&proof, &verification_key, Some(transcript_params))
            .expect("should verify");

    assert!(is_valid);

    println!("PROOF IS VALID");

    (verification_key, proof)
}

pub fn open_crs_for_log2_of_size<const ENABLE_TEST: bool>(n: usize) -> Crs<Bn256, CrsForMonomialForm> {
    if ENABLE_TEST {
        let worker = Worker::new();
        Crs::<Bn256, CrsForMonomialForm>::crs_42(2usize.pow(n as u32), &worker)
    } else {
        let base_path_str = std::env::var("RUNTIME_CONFIG_KEY_DIR").unwrap();
        let base_path = std::path::Path::new(&base_path_str);
        let full_path = base_path.join(format!("setup_2^{}.key", n));
        println!("Opening {}", full_path.to_string_lossy());
        let file = std::fs::File::open(full_path).unwrap();
        let reader = std::io::BufReader::with_capacity(1 << n, file);

        Crs::<Bn256, CrsForMonomialForm>::read(reader).unwrap()
    }
}
