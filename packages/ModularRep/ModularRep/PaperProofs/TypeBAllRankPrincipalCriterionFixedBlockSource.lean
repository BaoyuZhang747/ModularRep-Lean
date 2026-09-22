import ModularRep.PaperProofs.TypeBCriterionHypotheses
import ModularRep.PaperProofs.TypeBWeightCoveringSplittingSource
import ModularRep.PaperProofs.TypeBModularLinearCharacterLift
import ModularRep.PaperProofs.TypeBQ3AssemblyCriterionData
import ModularRep.PaperProofs.TypeBQ3FaithfulRadicalCovariance

/-!
# One specified block in the Brough--Spaeth criterion

The source below is the singleton-block, abelian-actor specialization of
Brough--Spaeth, Theorem 4.5, with all four extension clauses retained.
Feng--Malle, Theorem 3.3, uses its cyclic specialization. The overgroup
correspondence is an INPUT, as in the published theorem; the downstairs
correspondence and all of its matched extension data are OUTPUTS.

The singleton is invariant under the full actual automorphism group. Its
upper covering union is one specified block, identified by actual
restriction constituents and calibrated DGN covering, not by block labels.
The J equality concerns only constituent/covered pairs of that SAME upper
map. It does not compare unrelated singleton and double fibres.

This is a generic source boundary at the prime two, the prime in the
independently defined `CompleteClauses`. No Type B group, rank, principal
selector, completed downstairs map, or all-block family occurs in its
domain. Ordinary algebraic closure and cyclicity are not imposed: the
displayed splitting roots and the original extension hypotheses suffice.

The E2 direction is BS Theorem 4.5 and its proof via Lemma 4.6, followed
by Definition 4.3 and Remark 4.4. Lemma 4.6 chooses SOME overgroup-conjugate
before constructing the downstairs map; it is not read as a theorem for
an independently prescribed downstairs match. The literal coefficient,
root, local-block and complete-character interpretation remains U. The
certificate has no inhabitant here. Its output keeps normalized roots on
the same existential packets, including every intermediate group. The
separate full-cover character-triple interpretation is not asserted here.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionFixedBlockSource

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCriterionHypotheses EvenFieldFLZSourceConditions
open TypeBLocalReductionInstantiation TypeBLocalPhysicalBlockBinding
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalRadicalDecoding
open TypeBQ3PrincipalCriterionData
open NavarroCoveringBrauerExtension

local instance finiteFintype (X : Type) [Finite X] : Fintype X := Fintype.ofFinite X
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

section Output

variable {k K O Y : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K] [Group Y] [Finite Y]
  (Msys : ModularSystem 2 K O k)
  {root : PrimeRegularRootEmbedding 2 k K Y}

/-- These are the roots of the SAME packet and its stored intermediate data. -/
def RootNormalized {phi : IBr root} {W : CharacterWeight 2 K Y}
    (C : PrincipalClauseIII root phi W) : Prop := by
  letI := C.groupA
  letI := C.finiteA
  exact RootResidueCompatible Msys C.globalRoot ∧
    RootResidueCompatible Msys C.localRoot ∧
    ∀ (J : Subgroup C.A) (hJ : C.base ≤ J),
      RootResidueCompatible Msys (C.intermediate J hJ).globalRoot ∧
      RootResidueCompatible Msys (C.intermediate J hJ).localRoot

/-- BS Definition 4.3 on the displayed specified fibres, retaining the
normalized extension witness for each raw representative of the same match.
The radical partition and local character equivalences are computed below. -/
structure NormalizedBlockWitness
    (root : PrimeRegularRootEmbedding 2 k K Y)
    (R : CoverWeightSource (k := k) (K := K) Y)
    (b : LiteralPrimitiveBlock k Y) where
  omega : BrauerFibre root b ≃ CoverWeight R b
  equivariant : ∀ (alpha : (MulAut Y)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
    psi.val = alpha • phi.val → (omega psi).val = alpha • (omega phi).val
  packets : ∀ (phi : BrauerFibre root b) (W : CharacterWeight 2 K Y),
    TypeBWeightCoveringSource.rawClass W = (omega phi).val →
    Nonempty {C : PrincipalClauseIII root phi.val W // RootNormalized Msys C}

variable {Msys}
  {R : CoverWeightSource (k := k) (K := K) Y}
  {b : LiteralPrimitiveBlock k Y}
  (D : NormalizedBlockWitness Msys root R b)

/-- The same normalized packet at the canonical local character selected
from this matching, with no second choice of a downstairs correspondence. -/
theorem normalized_local_packet
    (Q : RadicalSubgroup (p := 2) (G := Y)) (phi : BrauerAtRadical D.omega Q) :
    Nonempty {C : PrincipalClauseIII root phi.val.val
      (characterWeightAt Nat.prime_two Q (localMap D.omega Q phi).val) //
      RootNormalized Msys C} :=
  D.packets phi.val _ (localMap_class D.omega Q phi)

/-- Independent fixed-block clauses follow by the existing radical and
local-character decoding. Every packet comes from the normalized output. -/
theorem completeClauses :
    TypeBQ3AssemblyCriterionData.CompleteClauses root R b D.omega := by
  refine ⟨D.equivariant, ?_,
    ⟨partitionEquiv D.omega, partitionEquiv_part D.omega,
      partitionEquiv_character D.omega⟩,
    (fun Q => localMap D.omega Q), localMap_class D.omega, ?_, ?_⟩
  · intro alpha phi psi values
    exact TypeBQ3FaithfulRadicalCovariance.part_of_class_transport
      D.omega alpha phi psi (D.equivariant alpha phi psi values)
  · intro alpha Q phi psi values
    have graph := D.equivariant alpha phi.val psi.val values
    exact ⟨TypeBQ3FaithfulRadicalCovariance.localMap_of_class_transport
      D.omega alpha Q phi psi graph,
      TypeBQ3FaithfulRadicalCovariance.localMap_raw_of_class_transport
        D.omega alpha Q phi psi graph⟩
  · intro Q phi
    obtain ⟨C⟩ := normalized_local_packet D Q phi
    exact ⟨C.val⟩

end Output

section PhysicalWeights

variable {k K O Y : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K] [Group Y] [Finite Y]
  (Msys : ModularSystem 2 K O k)
  [HasEnoughRootsOfUnity K (Nat.card Y)]
  (root : PrimeRegularRootEmbedding 2 k K Y)
  (R : CoverWeightSource (k := k) (K := K) Y)
  (b : LiteralPrimitiveBlock k Y)

/-- Specified interpretation only for weights in this fixed block. The
ordinary block is determined by the same stable-reduction modular system.
No extension, matching or intermediate block equation is an input here. -/
structure PhysicalWeightCalibration where
  literal : ∀ c, R.operations.ambientBlockData.blockIdempotent c = c.val
  normalizer_reduction : ∀ (W : CharacterWeight 2 K Y),
    R.operations.induceToAmbient W = b →
    ∀ (rootN : PrimeRegularRootEmbedding 2 k K
        (Subgroup.normalizer (W.subgroup : Set Y))) (phiN : IBr rootN),
      TypeBFixedRootDefinitionFamily.NormalizerRootAgreement root W.subgroup rootN →
      ModularRep.CharacterWeight.NormalizerInflatedReduction
        W.subgroup W.localCharacter rootN phiN →
      NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          R.operations W.subgroup rootN phiN =
        R.operations.inflateToNormalizer W.subgroup
          (R.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)
  ordinary : ∀ (W : CharacterWeight 2 K Y), R.operations.induceToAmbient W = b →
    NormalizerOrdinarySource Msys R.operations W.subgroup
  inflation : ∀ (W : CharacterWeight 2 K Y) (hW : R.operations.induceToAmbient W = b),
    ordinaryNormalizerBlock Msys R.operations W.subgroup (ordinary W hW)
      (inflatedOrdinary W.subgroup W.localCharacter) =
        R.operations.inflateToNormalizer W.subgroup
          (R.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

end PhysicalWeights

section Antecedents

variable {k K O M E : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group M] [Finite M] [Group E] [Finite E]
  (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
  (action : NaturalAction G field)
  (Msys : ModularSystem 2 K O k)
  [HasEnoughRootsOfUnity K (Nat.card M)]
  (root : PrimeRegularRootEmbedding 2 k K G)
  (rootM : PrimeRegularRootEmbedding 2 k K M)
  (R : CoverWeightSource (k := k) (K := K) G)
  (SH : CoverWeightSource (k := k) (K := K) M)
  (b : LiteralPrimitiveBlock k G) (bH : LiteralPrimitiveBlock k M)

/-- The subgroup inherits the ordinary splitting scope; no ordinary
algebraic closure is inserted to use older generic providers. -/
def baseOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card G) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card G)

/-- The exact positive field and quotient-linear actions on the upper
specified fibre. The selected ordinary lift is pinned pointwise to the
existing modular-root lift, rather than chosen as an unrelated action. -/
structure UpperCorrespondence
    (radicalLift : linearCharactersTrivialOn (k := k) G →
      TypeCWeightTensorFieldAction.RadicalTensorCharacter (p := 2) (K := K) (G := M)) where
  lift_value : ∀ lambda, (radicalLift lambda).val =
    TypeBModularLinearCharacterLift.quotientLift rootM G lambda
  omega : BrauerFibre rootM bH ≃ CoverWeight SH bH
  field_supported : ∀ (e : E) (Phi : BrauerFibre rootM bH),
    Supported rootM bH (IrreducibleBrauerCharacter.twist rootM Phi.val (field e))
  field_covariant : ∀ (e : E) (Phi Psi : BrauerFibre rootM bH),
    Psi.val = IrreducibleBrauerCharacter.twist rootM Phi.val (field e) →
      (omega Psi).val = CharacterWeight.rightTwistConjugacyClass
        (field e) (omega Phi).val
  linear_supported : ∀ (lambda : linearCharactersTrivialOn (k := k) G)
      (Phi : BrauerFibre rootM bH),
    ∃ Psi : BrauerFibre rootM bH, Psi.val.val =
      PrimeRegularClassFunction.pointwiseMul (rootM.liftedLinearCharacter lambda.val) Phi.val.val
  linear_covariant : ∀ (lambda : linearCharactersTrivialOn (k := k) G)
      (Phi Psi : BrauerFibre rootM bH),
    Psi.val.val =
      PrimeRegularClassFunction.pointwiseMul (rootM.liftedLinearCharacter lambda.val) Phi.val.val →
      (omega Psi).val =
        TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
          (radicalLift lambda) (omega Phi).val

/-- The original Brauer selector, with extensions of ALL M-conjugates
to their own actual stabilizers in G E, restricted to the upper block. -/
def CharacterSelector : Prop :=
  ∀ Phi : BrauerFibre rootM bH, ∃ phi : BrauerFibre root b,
    BrauerOccursInRestriction G rootM root Phi.val phi.val ∧
    BrauerFactorization G field action root phi.val ∧
    ∀ m : M,
      let phi' := IrreducibleBrauerCharacter.twist root phi.val
        (MulAut.conjNormal (H := G) m⁻¹)
      Nonempty (BrauerExtensionIn G field root phi'
        (brauerInertia G field action root phi' ⊓ baseFieldGroup G field))

/-- One raw representative in each actual M-orbit of block weight
classes. Inner conjugation is retained; class fixation is not raw fixation. -/
def WeightSelector : Prop :=
  ∀ w : CoverWeight R b, ∃ (m : M) (W : CharacterWeight 2 K G),
    TypeBWeightCoveringSource.rawClass W =
      CharacterWeight.rightTwistConjugacyClass
        ((action.hom (SemidirectProduct.inl m))⁻¹) w.val ∧
    WeightClassFactorization G field action W ∧
    Nonempty (LocalOrdinaryExtension G field W
      (rawNormalizerInertia G field action W ⊓ baseFieldGroup G field))

/-- All literal published antecedents for one invariant block with one
specified upper covering block. The group-theoretic specialization is the
abelian-E alternative of BS 4.5. Full Out(G) abelianness is precisely its
orbit alternative when this one block is invariant under all automorphisms.

The two union equations bind the source's covering union to actual
supported characters and calibrated DGN weights. The upper map is computed
by the caller. Neither a downstairs map nor one-pair output occurs here. -/
structure FixedBlockHypotheses
    (dgn : TypeBWeightCoveringSplittingSource.DGNSource G Msys)
    (radicalLift : linearCharactersTrivialOn (k := k) G →
      TypeCWeightTensorFieldAction.RadicalTensorCharacter (p := 2) (K := K) (G := M)) where
  coefficient : SpathCoefficientField 2 k Nat.prime_two
  cover : EllPrimeCoverSource 2 G
  divides_simple_order : 2 ∣ Nat.card cover.S
  centralFaithful : ∀ phi : BrauerFibre root b,
    Subgroup.center G ⊓
      (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation root phi.val).ρ.ker = ⊥
  block_invariant : ∀ alpha : (MulAut G)ᵐᵒᵖ, alpha • b = b
  derived : commutator M = G
  acting_abelian : IsMulCommutative E
  centralizer : Subgroup.centralizer (embeddedG G field : Set (Ambient field)) =
    embeddedCenter field
  natural_kernel : action.hom.ker = embeddedCenter field
  natural_surjective : Function.Surjective action.hom
  outer_abelian : IsMulCommutative (OuterAutomorphism G)
  base_calibration : RootResidueCompatible Msys root
  upper_calibration : RootResidueCompatible Msys rootM
  roots_agree : TypeBCriterionHypotheses.RootAgreement G rootM root
  lower_physical : letI := baseOrdinaryRoots (K := K) G
    PhysicalWeightCalibration Msys root R b
  upper_physical : PhysicalWeightCalibration Msys rootM SH bH
  character_union : ∀ Phi : IBr rootM,
    Supported rootM bH Phi ↔ ∃ phi : BrauerFibre root b,
      BrauerOccursInRestriction G rootM root Phi phi.val
  weight_union : ∀ V : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := M),
    SH.weightBlock V = bH ↔ ∃ w : CoverWeight R b,
      TypeBWeightCoveringSplittingSource.CoversClass G dgn V w.val
  upper : UpperCorrespondence G field rootM SH bH radicalLift
  hall : HallData G 2
  JG : ∀ (Phi : BrauerFibre rootM bH) (phi : BrauerFibre root b)
      (w : CoverWeight R b),
    BrauerOccursInRestriction G rootM root Phi.val phi.val →
    TypeBWeightCoveringSplittingSource.CoversClass G dgn (upper.omega Phi).val w.val →
      (brauerMInertia G field action root phi.val : Set M) * (hall.preimage : Set M) =
        (weightMInertia G field action w.val : Set M) * (hall.preimage : Set M)
  brauer_M : ∀ phi : BrauerFibre root b,
    Nonempty (BrauerExtensionIn G field root phi.val
      (brauerInertia G field action root phi.val ⊓ embeddedM field))
  ordinary_M : ∀ (W : CharacterWeight 2 K G), R.operations.induceToAmbient W = b →
    Nonempty (LocalOrdinaryExtension G field W
      (rawNormalizerInertia G field action W ⊓ embeddedM field))
  character_selector : CharacterSelector G field action root rootM b bH
  weight_selector : WeightSelector G field action R b

end Antecedents

/-- Exact one-way fixed-block source, uniformly over arbitrary finite
groups and the displayed specified data. There is deliberately no inhabitant.
The normalization is on the same extension data, not a later unrelated
choice from an erased `CompleteClauses` proposition. -/
structure Theorem45FixedBlockCertificate : Prop where
  fixedBlock : ∀ {k K O M E : Type}
      [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
      [CharP k 2] [IsAlgClosed k] [CharZero K]
      [Group M] [Finite M] [Group E] [Finite E]
      (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
      (action : NaturalAction G field)
      (Msys : ModularSystem 2 K O k)
      [HasEnoughRootsOfUnity K (Nat.card M)]
      (root : PrimeRegularRootEmbedding 2 k K G)
      (rootM : PrimeRegularRootEmbedding 2 k K M)
      (R : CoverWeightSource (k := k) (K := K) G)
      (SH : CoverWeightSource (k := k) (K := K) M)
      (b : LiteralPrimitiveBlock k G) (bH : LiteralPrimitiveBlock k M)
      (dgn : TypeBWeightCoveringSplittingSource.DGNSource G Msys)
      (radicalLift : linearCharactersTrivialOn (k := k) G →
        TypeCWeightTensorFieldAction.RadicalTensorCharacter (p := 2) (K := K) (G := M))
      (hypotheses : FixedBlockHypotheses G field action Msys root rootM
        R SH b bH dgn radicalLift),
    Nonempty (NormalizedBlockWitness Msys root R b)

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionFixedBlockSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
