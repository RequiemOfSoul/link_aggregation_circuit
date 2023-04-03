use franklin_crypto::bellman::bn256::Bn256;
use franklin_crypto::bellman::plonk::better_better_cs::trees::binary_tree::{
    BinaryTree, BinaryTreeParams,
};
use franklin_crypto::bellman::plonk::better_better_cs::trees::tree_hash::BinaryTreeHasher;
use franklin_crypto::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use franklin_crypto::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;
use franklin_crypto::bellman::plonk::better_cs::keys::VerificationKey;
use franklin_crypto::bellman::{CurveAffine, Engine, Field, ScalarEngine, SynthesisError};
use franklin_crypto::plonk::circuit::bigint::field::RnsParameters;
use franklin_crypto::plonk::circuit::verifier_circuit::data_structs::IntoLimbedWitness;
use franklin_crypto::rescue::bn256::Bn256RescueParams;
use franklin_crypto::rescue::{rescue_hash, RescueEngine, RescueHashParams};
use once_cell::sync::Lazy;

pub static RNS_PARAMETERS: Lazy<RnsParameters<Bn256, <Bn256 as Engine>::Fq>> =
    Lazy::new(|| RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4));
pub static RESCUE_PARAMETERS: Lazy<Bn256RescueParams> =
    Lazy::new(Bn256RescueParams::new_checked_2_into_1);

pub struct StaticRescueBinaryTreeHasher<E: RescueEngine> {
    params: E::Params,
}

impl<E: RescueEngine> StaticRescueBinaryTreeHasher<E> {
    pub fn new(params: &E::Params) -> Self {
        assert_eq!(params.rate(), 2u32);
        assert_eq!(params.output_len(), 1u32);
        Self {
            params: params.clone(),
        }
    }
}

impl<E: RescueEngine> Clone for StaticRescueBinaryTreeHasher<E> {
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }
}

impl<E: RescueEngine> BinaryTreeHasher<E::Fr> for StaticRescueBinaryTreeHasher<E> {
    type Output = E::Fr;

    #[inline]
    fn placeholder_output() -> Self::Output {
        E::Fr::zero()
    }

    fn leaf_hash(&self, input: &[E::Fr]) -> Self::Output {
        let mut as_vec = rescue_hash::<E>(&self.params, input);

        as_vec.pop().unwrap()
    }

    fn node_hash(&self, input: &[Self::Output; 2], _level: usize) -> Self::Output {
        let mut as_vec = rescue_hash::<E>(&self.params, &input[..]);

        as_vec.pop().unwrap()
    }
}

pub fn make_vks_tree<'a, E: RescueEngine, P: OldCSParams<E>>(
    vks: &[VerificationKey<E, P>],
    params: &'a E::Params,
    rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> (BinaryTree<E, StaticRescueBinaryTreeHasher<E>>, Vec<E::Fr>) {
    let mut leaf_combinations: Vec<Vec<&[E::Fr]>> = vec![vec![]; vks.len()];

    let hasher = StaticRescueBinaryTreeHasher::new(params);
    let mut tmp = vec![];

    for vk in vks.iter() {
        let witness = vk
            .into_witness_for_params(rns_params)
            .expect("must transform into limbed witness");
        tmp.push(witness);
    }

    for idx in 0..vks.len() {
        leaf_combinations[idx].push(&tmp[idx][..]);
    }

    let tree_params = BinaryTreeParams {
        values_per_leaf: VerificationKey::<E, P>::witness_size_for_params(rns_params),
    };

    let tree = BinaryTree::<E, _>::create_from_combined_leafs(
        &leaf_combinations[..],
        1,
        hasher,
        &tree_params,
    );

    let mut all_values = vec![];
    for w in tmp.into_iter() {
        all_values.extend(w);
    }

    (tree, all_values)
}

type VksTreeAndWitness = BinaryTree<Bn256, StaticRescueBinaryTreeHasher<Bn256>>;
type VksWitness = Vec<<Bn256 as ScalarEngine>::Fr>;

pub fn create_vks_tree(
    vks: &[VerificationKey<Bn256, OldActualParams>],
    tree_depth: usize,
) -> Result<(usize, (VksTreeAndWitness,VksWitness)), SynthesisError> {
    assert!(!vks.is_empty());
    let max_size = 1 << tree_depth;
    assert!(vks.len() <= max_size);

    let max_valid_idx = vks.len() - 1;

    let mut padded = vks.to_vec();
    padded.resize(max_size, vks.last().unwrap().clone());

    let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
    let rescue_params = Bn256RescueParams::new_checked_2_into_1();

    let (tree, witness) = make_vks_tree(&padded, &rescue_params, &rns_params);

    Ok((max_valid_idx, (tree, witness)))
}
