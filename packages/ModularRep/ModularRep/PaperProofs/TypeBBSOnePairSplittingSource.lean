import ModularRep.PaperProofs.TypeBCriterionEmbeddedPairBinding
import ModularRep.PaperProofs.TypeBCommonConjugateGlobalExtensions
import ModularRep.PaperProofs.TypeBWeightCoveringSplittingSource
import ModularRep.PaperProofs.TypeBModularLinearCharacterLift
import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.SpathNavarroSourceAdapter

/-!
# The centreless, abelian-actor one-pair implication of Brough--Spaeth

This is the generic one-way source statement of Lemma 4.6, with the full
natural automorphism image and the all-block family. The ordinary field is
the prescribed splitting field of one modular system. Its sufficient-root
guard is for the entire semidirect ambient group, and its residue field
retains the published algebraicity metadata.

The inputs are the independent structural, extension, inertia, covering,
common quotient-twist and specified upper-block clauses. The output is the
fixed complete block-triple witness for some inverse left-factor conjugate
of the Brauer character and the ORIGINAL raw weight. No witness, matching,
combined criterion domain, or caller-selected relation is an input.

The interpretation uses BS Lemma 4.6 -> Spaeth 2017 Definitions 3.1--3.2 ->
the projective description of SV 2016 Theorem 3.1 and MRR Section 3. The
all-intermediate tensor rule, scalar condition and defect/block clauses
are retained. No reverse implication to the older Navarro--Spaeth relation
is used. There is no inhabitant of the source certificate in this file.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBBSOnePairSplittingSource

open ModularRep FDRepSimpleClassKZero OrdinaryIrreducibleCharacter
open TypeBCriterionHypotheses EvenFieldFLZSourceConditions
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelTripleCarriers TypeBLocalReductionInstantiation
open TypeBModularGroupRootBinding TypeBModularLinearCharacterLift

local instance groupFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

section Splitting

variable {K M E : Type} [Field K] [Group M] [Finite M] [Group E] [Finite E]
  (field : E →* MulAut M)
  [HasEnoughRootsOfUnity K (Nat.card (Ambient field))]

/-- The left factor inherits sufficient ordinary roots from the whole ambient. -/
def ambientOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card M) :=
  HasEnoughRootsOfUnity.of_dvd K (by
    change Nat.card M ∣ Nat.card (M ⋊[field] E)
    rw [SemidirectProduct.card]
    exact dvd_mul_right (Nat.card M) (Nat.card E))

/-- The original base inherits the same coefficient field and splitting scope. -/
def baseOrdinaryRoots (G : Subgroup M) : HasEnoughRootsOfUnity K (Nat.card G) := by
  letI := ambientOrdinaryRoots (K := K) field
  exact HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card G)

/-- The literal embedded base has the same order as the original base. -/
def embeddedOrdinaryRoots (G : Subgroup M) :
    HasEnoughRootsOfUnity K (Nat.card (embeddedG G field)) := by
  letI := baseOrdinaryRoots (K := K) field G
  exact TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) G field

end Splitting

/-- Exact generic BS Lemma 4.6 in the centreless, abelian-E specialization.

The original phi-inertias are fixed before all M-conjugates. The ordinary
extensions are on the raw normalizer inertia quotients, not on a larger
unrestricted normalizer. One upper character and raw weight are fixed
before all field actors. For each actor the SAME quotient Brauer character
and its selected ordinary prime-to-p lift occur in the two twist equations.

The all-E twist clause is a sufficient strengthening of BS's E_phi clause.
The full natural automorphism image specializes its block-family scope to
all blocks. Neither cyclicity of M/G nor outer abelianness is added as a
separate structural premise.
-/
structure Theorem46SplittingCertificate : Prop where
  someConjugate : ∀ {p : ℕ} {K O k M E : Type}
      [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
      [ordinaryCharacteristic : CharZero K]
      [residueCharacteristic : CharP k p] [residueClosure : IsAlgClosed k]
      [Group M] [finiteOvergroup : Finite M]
      [Group E] [finiteActors : Finite E]
      (G : Subgroup M) [normalBase : G.Normal] (field : E →* MulAut M)
      (action : NaturalAction G field)
      (Msys : ModularSystem p K O k)
      [ambientRoots : HasEnoughRootsOfUnity K (Nat.card (Ambient field))]
      (fieldScope : SpathCoefficientField p k Msys.prime)
      (cover : EllPrimeCoverSource p G)
      (prime_divides : p ∣ Nat.card cover.S)
      (centreless : Subgroup.center G = ⊥)
      (derived : commutator M = G)
      (acting_abelian : IsMulCommutative E)
      (centralizer : Subgroup.centralizer (embeddedG G field : Set (Ambient field)) =
        embeddedCenter field)
      (natural_kernel : action.hom.ker = embeddedCenter field)
      (natural_surjective : Function.Surjective action.hom)
      (iotaG : PrimeRegularRootEmbedding p k K G)
      (iotaM : PrimeRegularRootEmbedding p k K M)
      (baseCalibration : RootResidueCompatible Msys iotaG)
      (upperCalibration : RootResidueCompatible Msys iotaM),
    letI := ambientOrdinaryRoots (K := K) field
    letI := baseOrdinaryRoots (K := K) field G
    ∀ (dgn : TypeBWeightCoveringSplittingSource.DGNSource G Msys)
      (navarro : ∀ (X : Type) [Group X] [Finite X]
        [HasEnoughRootsOfUnity K (Nat.card X)]
        (iota : PrimeRegularRootEmbedding p k K X)
        (compatible : RootResidueCompatible Msys iota),
          ScopedDefectZeroReductionSource Msys iota compatible)
      (phi : IBr iotaG) (W : CharacterWeight p K G)
      (brauer_factorization : BrauerFactorization G field action iotaG phi)
      (commutator_inertia :
        ⁅brauerInertia G field action iotaG phi, embeddedM field⁆ ≤
          brauerInertia G field action iotaG phi ⊓ embeddedM field)
      (brauer_extensions_M : ∀ m : M,
        Nonempty (BrauerExtensionIn G field iotaG
          (IrreducibleBrauerCharacter.twist iotaG phi
            (MulAut.conjNormal (H := G) m⁻¹))
          (brauerInertia G field action iotaG phi ⊓ embeddedM field)))
      (brauer_extensions_GE : ∀ m : M,
        Nonempty (BrauerExtensionIn G field iotaG
          (IrreducibleBrauerCharacter.twist iotaG phi
            (MulAut.conjNormal (H := G) m⁻¹))
          (embeddedG G field ⊔
            (brauerInertia G field action iotaG phi ⊓ embeddedE field))))
      (weight_factorization : WeightClassFactorization G field action W)
      (ordinary_extension_M : Nonempty (LocalOrdinaryExtension G field W
        (rawNormalizerInertia G field action W ⊓ embeddedM field)))
      (ordinary_extension_GE : Nonempty (LocalOrdinaryExtension G field W
        (rawNormalizerInertia G field action W ⊓ baseFieldGroup G field)))
      (same_inertia : brauerInertia G field action iotaG phi =
        weightClassInertia G field action (TypeBWeightCoveringSource.rawClass W))
      (Phi : IBr iotaM) (V : CharacterWeight p K M)
      (occurrence : NavarroCoveringBrauerExtension.BrauerOccursInRestriction
        G iotaM iotaG Phi phi)
      (covering : TypeBWeightCoveringSplittingSource.CoversClass G dgn
        (TypeBWeightCoveringSource.rawClass V) (TypeBWeightCoveringSource.rawClass W))
      (twists : ∀ e : E,
        ∃ (mu : IBr (groupRoot Msys (M ⧸ G))) (nu : M ⧸ G →* kˣ)
          (lambda : TypeCWeightTensorFieldAction.RadicalTensorCharacter
            (p := p) (K := K) (G := M)),
          mu.val = (groupRoot Msys (M ⧸ G)).liftedLinearCharacter nu ∧
          lambda.val = quotientLift iotaM G
            ((LinearCharactersTrivialOn.quotientMulEquiv (k := k) G).symm nu) ∧
          (IrreducibleBrauerCharacter.twist iotaM Phi (field e)).val =
            PrimeRegularClassFunction.pointwiseMul
              (PrimeRegularClassFunction.pullback (QuotientGroup.mk' G) mu.val) Phi.val ∧
          TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
              lambda (TypeBWeightCoveringSource.rawClass V) =
            CharacterWeight.rightTwistConjugacyClass (field e)
              (TypeBWeightCoveringSource.rawClass V))
      (upperBlocks : PhysicalBlocks k M)
      (normalizerBlocks : PhysicalBlocks k (Subgroup.normalizer (V.subgroup : Set M))),
    letI := upperBlocks.blockFintype
    letI := normalizerBlocks.blockFintype
    letI : HasEnoughRootsOfUnity K
        (Nat.card (Subgroup.normalizer (V.subgroup : Set M))) :=
      HasEnoughRootsOfUnity.of_dvd K
        (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (V.subgroup : Set M)))
    ∀ (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys
      (groupRoot Msys (Subgroup.normalizer (V.subgroup : Set M)))
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      normalizerBlocks.decomposition),
      BlockInducesTo (Subgroup.normalizer (V.subgroup : Set M))
        normalizerBlocks.catalogue upperBlocks.catalogue
        (ordinary.physical.ordinaryBlock
          (inflateAlong
            (QuotientGroup.mk'
              (V.subgroup.subgroupOf (Subgroup.normalizer (V.subgroup : Set M))))
            (QuotientGroup.mk'_surjective _) V.localCharacter))
        ((characterData iotaM upperBlocks).block Phi) →
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
    letI := embeddedOrdinaryRoots (K := K) field G
    let rootHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot G field iotaG
    let calibrationHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue
      G field Msys iotaG baseCalibration
    let thetaHat := TypeBCriterionEmbeddedPairBinding.brauerEquiv G field iotaG phi
    let weightHat := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv G field W
    let thetaM : M → IBr rootHat := fun m =>
      IrreducibleBrauerCharacter.twist rootHat thetaHat
        (MulAut.conjNormal (H := embeddedG G field)
          ((SemidirectProduct.inl m : Ambient field)⁻¹))
    ∀ (catalogues : ∀ (m : M)
      (hUT : TypeBCentralKernelInertia.U (embeddedG G field) weightHat ≤
        TypeBCentralKernelInertia.T (embeddedG G field) rootHat (thetaM m)),
      PhysicalBlockFamily (k := k)
        (inside (embeddedG G field)
          (TypeBCentralKernelInertia.T (embeddedG G field) rootHat (thetaM m)))
        (inside (TypeBCentralKernelInertia.U (embeddedG G field) weightHat)
          (TypeBCentralKernelInertia.T (embeddedG G field) rootHat (thetaM m)))),
      ∃ (m : M)
        (hUT : TypeBCentralKernelInertia.U (embeddedG G field) weightHat ≤
          TypeBCentralKernelInertia.T (embeddedG G field) rootHat (thetaM m)),
        Nonempty (TypeBCentralKernelPairSplittingBinding.PairWitness
          Msys (embeddedG G field) rootHat calibrationHat (thetaM m) weightHat hUT
          navarro (catalogues m hUT))

end ModularRep.PaperProofs.TypeBBSOnePairSplittingSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
