#![allow(dead_code)]

use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::{Circuit, Width4MainGateWithDNext};
use franklin_crypto::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use franklin_crypto::bellman::plonk::better_cs::generator::make_non_residues;
use franklin_crypto::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use franklin_crypto::bellman::SynthesisError;
use franklin_crypto::circuit::Assignment;
use franklin_crypto::circuit::sponge::CircuitGenericSponge;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::bigint::field::*;
use franklin_crypto::plonk::circuit::bigint::range_constraint_gate::TwoBitDecompositionRangecheckCustomGate;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::rescue::*;
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::aux_data::*;
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::*;
use franklin_crypto::plonk::circuit::verifier_circuit::channel::*;
use franklin_crypto::plonk::circuit::verifier_circuit::data_structs::*;
use franklin_crypto::plonk::circuit::verifier_circuit::verifying_circuit::aggregate_proof;
use franklin_crypto::poseidon::params::PoseidonParams;
use franklin_crypto::rescue::{RescueEngine, RescueHashParams};

use crate::utils::bytes_to_keep;

pub const ZKLINK_NUM_INPUTS: usize = 1;
pub const ALLIGN_FIELD_ELEMENTS_TO_BITS: usize = 256;

#[derive(Clone, Debug)]
pub struct RecursiveAggregationCircuit<
    'a,
    E: RescueEngine,
    P: OldCSParams<E>,
    WP: WrappedAffinePoint<'a, E>,
    AD: AuxData<E>,
    T: ChannelGadget<E>,
> {
    pub num_proofs_to_check: usize,
    pub num_inputs: usize,
    pub vk_tree_depth: usize,
    pub vk_root: Option<E::Fr>,
    pub vk_witnesses: Option<Vec<VerificationKey<E, P>>>,
    pub vk_auth_paths: Option<Vec<Vec<E::Fr>>>,
    pub proof_ids: Option<Vec<usize>>,
    pub proofs: Option<Vec<Proof<E, P>>>,
    pub rescue_params: &'a E::Params,
    pub rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    pub aux_data: AD,
    pub transcript_params: &'a T::Params,

    pub g2_elements: Option<[E::G2Affine; 2]>,

    pub _m: std::marker::PhantomData<WP>,
}

impl<'a, E, P, WP, AD, T> Circuit<E> for RecursiveAggregationCircuit<'a, E, P, WP, AD, T>
where
    E: RescueEngine,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
    P: OldCSParams<E>,
    WP: WrappedAffinePoint<'a, E>,
    AD: AuxData<E>,
    T: ChannelGadget<E>,
{
    type MainGate = Width4MainGateWithDNext;

    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let num_bits_in_proof_id = self.vk_tree_depth;

        let non_residues = make_non_residues::<E::Fr>(P::STATE_WIDTH - 1);

        if let Some(proofs) = self.proofs.as_ref() {
            assert_eq!(self.num_proofs_to_check, proofs.len());
        }
        if let Some(proof_ids) = self.proof_ids.as_ref() {
            assert_eq!(self.num_proofs_to_check, proof_ids.len());
        }
        if let Some(vk_witnesses) = self.vk_witnesses.as_ref() {
            assert_eq!(self.num_proofs_to_check, vk_witnesses.len());
        }
        if let Some(vk_auth_paths) = self.vk_auth_paths.as_ref() {
            assert_eq!(self.num_proofs_to_check, vk_auth_paths.len());
        }

        // Allocate everything, get fs scalar for aggregation

        let mut proof_witnesses = vec![];

        let mut fs_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let proof_witness = self.proofs.as_ref().map(|el| el[proof_index].clone());

            if let Some(proof) = proof_witness.as_ref() {
                assert_eq!(
                    proof.input_values.len(),
                    self.num_inputs,
                    "proof has too many inputs"
                );
                // assert!(proof.input_values.len() <= self.num_inputs, "proof has too many inputs");
            }

            let allocated_proof = ProofGadget::<E, WP>::alloc_from_witness(
                cs,
                self.num_inputs,
                &proof_witness,
                self.rns_params,
                &self.aux_data,
            )?;

            let as_num_witness = allocated_proof.into_witness(cs)?;
            fs_witnesses.extend(as_num_witness);

            proof_witnesses.push(allocated_proof);
        }

        let mut vk_witnesses = vec![];

        let mut vk_leaf_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let vk_witness = self.vk_witnesses.as_ref().map(|el| {
                el[proof_index]
                    .into_witness_for_params(self.rns_params)
                    .expect("must transform into limbed witness")
            });

            let mut allocated = vec![];

            let expected_witness_size =
                VerificationKey::<E, P>::witness_size_for_params(self.rns_params);

            if let Some(vk_witness) = vk_witness.as_ref() {
                assert_eq!(
                    vk_witness.len(),
                    expected_witness_size,
                    "witness size is not sufficient to create verification key"
                );
            }

            for idx in 0..expected_witness_size {
                let wit = vk_witness.as_ref().map(|el| el[idx]);
                let num = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

                allocated.push(num);
            }

            let domain_size = &allocated[0];
            let omega = &allocated[1];
            let key = &allocated[2..];

            let allocated_vk = VerificationKeyGagdet::<E, WP>::alloc_from_limbs_witness::<_, P, AD>(
                cs,
                self.num_inputs,
                domain_size,
                omega,
                key,
                self.rns_params,
                non_residues.clone(),
                &self.aux_data,
            )?;

            vk_witnesses.push(allocated_vk);

            vk_leaf_witnesses.push(allocated);
        }

        // proofs and verification keys are allocated, not proceed with aggregation

        // first get that FS scalar

        let mut sponge = StatefulRescueGadget::<E>::new(self.rescue_params);

        for w in fs_witnesses.into_iter() {
            sponge.absorb_single_value(cs, w, self.rescue_params)?;
        }

        sponge.pad_if_necessary(self.rescue_params)?;

        let aggregation_challenge = sponge
            .squeeze_out_single(cs, self.rescue_params)?
            .into_allocated_num(cs)?;

        // then perform individual aggregation

        let mut pairs_for_generator = vec![];
        let mut pairs_for_x = vec![];

        for proof_idx in 0..self.num_proofs_to_check {
            let proof = &proof_witnesses[proof_idx];
            let vk = &vk_witnesses[proof_idx];

            let [pair_with_generator, pair_with_x] = aggregate_proof::<_, _, T, CS::Params, P, _, _>(
                cs,
                self.transcript_params,
                &proof.input_values,
                vk,
                proof,
                &self.aux_data,
                self.rns_params,
            )?;

            pairs_for_generator.push(pair_with_generator);
            pairs_for_x.push(pair_with_x);
        }

        // now make scalars for separation

        let mut scalars = vec![];
        scalars.push(aggregation_challenge);

        let mut current = aggregation_challenge;
        for _ in 1..self.num_proofs_to_check {
            let new = current.mul(cs, &aggregation_challenge)?;
            scalars.push(new);

            current = new;
        }

        // perform final aggregation

        let pair_with_generator = WP::multiexp(
            cs,
            &scalars,
            &pairs_for_generator,
            None,
            self.rns_params,
            &self.aux_data,
        )?;
        let pair_with_x = WP::multiexp(
            cs,
            &scalars,
            &pairs_for_x,
            None,
            self.rns_params,
            &self.aux_data,
        )?;

        if let (Some(with_gen), Some(with_x), Some(g2_elements)) = (
            pair_with_generator.get_point().get_value(),
            pair_with_x.get_point().get_value(),
            self.g2_elements,
        ) {
            let valid = E::final_exponentiation(&E::miller_loop(&[
                (&with_gen.prepare(), &g2_elements[0].prepare()),
                (&with_x.prepare(), &g2_elements[1].prepare()),
            ]))
            .unwrap()
                == E::Fqk::one();

            dbg!(valid);
        }

        // allocate vk ids

        let mut key_ids = vec![];
        let vk_root = AllocatedNum::alloc(cs, || Ok(*self.vk_root.get()?))?;

        {
            for proof_index in 0..self.num_proofs_to_check {
                let vk_witness = &vk_leaf_witnesses[proof_index];
                let path_witness = self
                    .proof_ids
                    .as_ref()
                    .map(|el| E::Fr::from_str(&el[proof_index].to_string()).unwrap());
                let path_allocated = AllocatedNum::alloc(cs, || Ok(*path_witness.get()?))?;
                key_ids.push(path_allocated.clone());

                let path_bits = path_allocated.into_bits_le(cs, Some(num_bits_in_proof_id))?;

                let mut auth_path = vec![];
                for path_idx in 0..self.vk_tree_depth {
                    let auth_witness = self
                        .vk_auth_paths
                        .as_ref()
                        .map(|el| el[proof_index][path_idx]);
                    let auth_allocated = AllocatedNum::alloc(cs, || Ok(*auth_witness.get()?))?;

                    auth_path.push(auth_allocated);
                }

                assert_eq!(auth_path.len(), path_bits.len());

                let leaf_hash = rescue_leaf_hash(cs, vk_witness, self.rescue_params)?;

                let mut current = leaf_hash;

                for (path_bit, auth_path) in path_bits.into_iter().zip(auth_path.into_iter()) {
                    let left =
                        AllocatedNum::conditionally_select(cs, &auth_path, &current, &path_bit)?;
                    let right =
                        AllocatedNum::conditionally_select(cs, &current, &auth_path, &path_bit)?;

                    let node_hash = rescue_node_hash(cs, left, right, self.rescue_params)?;

                    current = node_hash;
                }

                current.enforce_equal(cs, &vk_root)?;
            }
        }

        let mut hash_to_public_inputs = vec![];
        // VKs tree
        hash_to_public_inputs.push(vk_root);

        // first aggregate proof ids into u8
        for key_id in key_ids.into_iter().take(self.num_proofs_to_check) {
            hash_to_public_inputs.push(key_id);
        }

        // now aggregate original public inputs
        for allocated_proof in proof_witnesses.iter().take(self.num_proofs_to_check) {
            for input_idx in 0..self.num_inputs {
                let input = allocated_proof.input_values[input_idx];
                hash_to_public_inputs.push(input);
            }
        }

        hash_to_public_inputs.extend(point_into_num(cs, &pair_with_generator)?);
        hash_to_public_inputs.extend(point_into_num(cs, &pair_with_x)?);

        let keep = bytes_to_keep::<E>();
        assert!(keep <= 32);

        let params = PoseidonParams::<E, 2, 3>::default();
        let inputs = hash_to_public_inputs
            .into_iter()
            .map(|n| Num::Variable(n))
            .collect::<Vec<_>>();
        let input_commitment = CircuitGenericSponge::hash_num(cs, &inputs, &params, None)?[0];
        input_commitment.get_variable().inputize(cs)?;

        Ok(())
    }
    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(vec![
            Self::MainGate::default().into_internal(),
            TwoBitDecompositionRangecheckCustomGate::default().into_internal(),
        ])
    }
}

fn allocated_num_to_alligned_big_endian<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = el.into_bits_le(cs, None)?;

    assert!(bits.len() < ALLIGN_FIELD_ELEMENTS_TO_BITS);

    bits.resize(ALLIGN_FIELD_ELEMENTS_TO_BITS, Boolean::constant(false));

    bits.reverse();

    Ok(bits)
}

fn allocated_num_to_big_endian_of_fixed_width<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
    limit: usize,
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = el.into_bits_le(cs, Some(limit))?;
    bits.reverse();

    Ok(bits)
}

fn serialize_point_into_big_endian<
    'a,
    E: Engine,
    CS: ConstraintSystem<E>,
    WP: WrappedAffinePoint<'a, E>,
>(
    cs: &mut CS,
    point: &WP,
) -> Result<Vec<Boolean>, SynthesisError> {
    let raw_point = point.get_point();

    let x = raw_point
        .get_x()
        .force_reduce_into_field(cs)?
        .enforce_is_normalized(cs)?;
    let y = raw_point
        .get_y()
        .force_reduce_into_field(cs)?
        .enforce_is_normalized(cs)?;

    let mut serialized = vec![];

    for coord in vec![x, y].into_iter() {
        for limb in coord.into_limbs().into_iter() {
            let as_num = limb.into_variable(); // this checks coeff and constant term internally
            serialized.extend(allocated_num_to_alligned_big_endian(cs, &as_num)?);
        }
    }

    Ok(serialized)
}

fn point_into_num<
    'a,
    E: Engine,
    CS: ConstraintSystem<E>,
    WP: WrappedAffinePoint<'a, E>,
>(
    cs: &mut CS,
    point: &WP,
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    let raw_point = point.get_point();

    let x = raw_point
        .get_x()
        .force_reduce_into_field(cs)?
        .enforce_is_normalized(cs)?;
    let y = raw_point
        .get_y()
        .force_reduce_into_field(cs)?
        .enforce_is_normalized(cs)?;

    let mut nums = vec![];
    for coord in vec![x, y].into_iter() {
        for limb in coord.into_limbs().into_iter() {
            let num = limb.into_variable(); // this checks coeff and constant term internally
            nums.push(num);
        }
    }

    Ok(nums)
}

fn rescue_leaf_hash<E: RescueEngine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    leaf: &[AllocatedNum<E>],
    params: &E::Params,
) -> Result<AllocatedNum<E>, SynthesisError>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    let mut rescue_gadget = StatefulRescueGadget::<E>::new(params);

    rescue_gadget.specizalize(leaf.len() as u8);
    rescue_gadget.absorb(cs, leaf, params)?;

    let output = rescue_gadget.squeeze_out_single(cs, params)?;

    let as_num = output.into_allocated_num(cs)?;

    Ok(as_num)
}

fn rescue_node_hash<E: RescueEngine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    left: AllocatedNum<E>,
    right: AllocatedNum<E>,
    params: &E::Params,
) -> Result<AllocatedNum<E>, SynthesisError>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    let mut rescue_gadget = StatefulRescueGadget::<E>::new(params);

    rescue_gadget.specizalize(2);
    rescue_gadget.absorb(cs, &[left, right], params)?;

    let output = rescue_gadget.squeeze_out_single(cs, params)?;

    let as_num = output.into_allocated_num(cs)?;

    Ok(as_num)
}
