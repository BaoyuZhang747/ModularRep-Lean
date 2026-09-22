import ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates
import ModularRep.PaperProofs.OddTwoGroupEquivOwnReduction
import ModularRep.PaperProofs.EvenFieldPhysicalBlockFibreReindexing

/-!
# Actual group coordinates to independently selected whole weight pairs

Equality in the actual ambient class supplies an inner correction. The
corrected group equivalence maps the entire OWN character pair, not just
its radical. Canonical normalizer/quotient maps and a chosen own reduction
then transport through this proved equality. The specified fibre consumer
derives the class premise from the two independent sources.

These are K constructions. No tuple relation or independent root equality
is asserted. The ambient root of a transported packet uses the corrected
group map; comparison to a separately fixed ambient root is still required.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCSelectedPairGroupEquivCoordinates

open ModularRep CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37ActualBlockFibres
open CyclicOuterLemma37LiteralLocalExtension OddTwoActualLocalBlockSupport
open OddTwoSelectedWeightAutomorphismCoordinates OddTwoActualStabilizerTriple
open OddTwoGroupEquivOwnReduction
open OddTwoActualCentralInflationPacket

universe u

section Pair

variable {p : ℕ} {K G H : Type u} [Field K] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

/-- The actual group map retains the inner conjugator produced by the
quotient equality. -/
def correctedEquiv (e : G ≃* H) (g : H) : G ≃* H := e.trans (MulAut.conj g)

@[simp] theorem correctedEquiv_apply (e : G ≃* H) (g : H) (x : G) :
    correctedEquiv e g x = g * e x * g⁻¹ := rfl

/-- The equality compares the whole selected pair, including its own
ordinary character. No equivariant representative selection is assumed. -/
theorem exists_corrected_pair (W : CharacterWeight p K G)
    (V : CharacterWeight p K H) (e : G ≃* H)
    (hclass : weightClass V = weightClass (W.mapGroupEquiv e)) :
    ∃ g : H, W.mapGroupEquiv (correctedEquiv e g) = V := by
  have hid : weightClass V =
      rightTwistConjugacyClass (1 : MulAut H)⁻¹ (weightClass (W.mapGroupEquiv e)) := by
    simpa using hclass
  obtain ⟨g, hg⟩ := exists_coordinate_of_class_eq (W.mapGroupEquiv e) V 1 hid
  refine ⟨g, ?_⟩
  rw [correctedEquiv, ← mapGroupEquiv_trans]
  have hm := mapGroupEquiv_mulAut_symm (W.mapGroupEquiv e) (MulAut.conj g)⁻¹
  simpa [coordinateAutomorphism] using hm.trans hg

/-- Normalizer restriction through a proved whole-pair equality. -/
def pairNormalizerEquiv (W : CharacterWeight p K G) (V : CharacterWeight p K H)
    (e : G ≃* H) (hpair : W.mapGroupEquiv e = V) :
    Subgroup.normalizer (W.subgroup : Set G) ≃*
      Subgroup.normalizer (V.subgroup : Set H) := by
  subst V
  exact normalizerEquiv e W.subgroup

@[simp] theorem pairNormalizerEquiv_coe (W : CharacterWeight p K G)
    (V : CharacterWeight p K H) (e : G ≃* H) (hpair : W.mapGroupEquiv e = V)
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    (pairNormalizerEquiv W V e hpair x : H) = e (x : G) := by
  subst V
  rfl

/-- The quotient restriction uses the same canonical normalizer map. -/
def pairQuotientEquiv (W : CharacterWeight p K G) (V : CharacterWeight p K H)
    (e : G ≃* H) (hpair : W.mapGroupEquiv e = V) :
    NormalizerQuotient W.subgroup ≃* NormalizerQuotient V.subgroup := by
  subst V
  exact normalizerQuotientEquiv e W.subgroup

theorem pairQuotientEquiv_mk (W : CharacterWeight p K G)
    (V : CharacterWeight p K H) (e : G ≃* H) (hpair : W.mapGroupEquiv e = V)
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    pairQuotientEquiv W V e hpair (QuotientGroup.mk x) =
      QuotientGroup.mk (pairNormalizerEquiv W V e hpair x) := by
  subst V
  rfl

theorem pairQuotientEquiv_ownValues (W : CharacterWeight p K G)
    (V : CharacterWeight p K H) (e : G ≃* H) (hpair : W.mapGroupEquiv e = V)
    (x : NormalizerQuotient W.subgroup) :
    V.localCharacter (pairQuotientEquiv W V e hpair x) = W.localCharacter x := by
  subst V
  exact mapGroupEquiv_localCharacter_image W e x

end Pair

section Reduction

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

local instance selectedSubgroupFintype {A : Type u} [Group A] [Finite A]
    (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

/-- Transport the chosen own reduction to the actual selected whole pair. -/
def pairOwnReduction (W : CharacterWeight p K G) (V : CharacterWeight p K H)
    (e : G ≃* H) (hpair : W.mapGroupEquiv e = V)
    (R : OwnNormalizerReduction (k := k) W) : OwnNormalizerReduction (k := k) V := by
  subst V
  exact mapOwnReduction W e R

theorem pairOwnReduction_horizontal (W : CharacterWeight p K G)
    (V : CharacterWeight p K H) (e : G ≃* H) (hpair : W.mapGroupEquiv e = V)
    (R : OwnNormalizerReduction (k := k) W) :
    RootCompatibleAlong (ownReductionRoot V (pairOwnReduction W V e hpair R))
      (ownReductionRoot W R) (pairNormalizerEquiv W V e hpair).toMonoidHom := by
  subst V
  exact mapOwnReduction_horizontal W e R

theorem pairOwnReduction_ambientCompatible (W : CharacterWeight p K G)
    (V : CharacterWeight p K H) (e : G ≃* H) (hpair : W.mapGroupEquiv e = V)
    (R : OwnNormalizerReduction (k := k) W) (iota : PrimeRegularRootEmbedding p k K G)
    (compatible : RootCompatibleAlong iota (ownReductionRoot W R)
      (Subgroup.normalizer (W.subgroup : Set G)).subtype) :
    RootCompatibleAlong (iota.alongMulEquiv e)
      (ownReductionRoot V (pairOwnReduction W V e hpair R))
      (Subgroup.normalizer (V.subgroup : Set H)).subtype := by
  subst V
  exact mapOwnReduction_ambientCompatible W e R iota compatible

end Reduction

section PhysicalFibre

open scoped MonoidAlgebra
open EvenFieldPhysicalBlockFibreReindexing OddTwoGroupEquivWeightBlocks

variable {p : ℕ} {k K G H B C : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H] [Fintype B] [Fintype C]
variable [MulAction (MulAut G)ᵐᵒᵖ B] [MulAction (MulAut H)ᵐᵒᵖ C]
variable {bG : B → k[G]} {bH : C → k[H]}
variable (DG : BlockIdempotentDecomposition bG) (DH : BlockIdempotentDecomposition bH)
variable (e : G ≃* H)
variable (SG : LocalBlockInductionSource (p := p) (k := k) (K := K) (G := G) (Block := B))
variable (SH : LocalBlockInductionSource (p := p) (k := k) (K := K) (G := H) (Block := C))
variable (ambientG : ∀ b, SG.operations.ambientBlockData.blockIdempotent b = bG b)
variable (ambientH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = bH c)
variable (ownPrimitive : ∀ W : CharacterWeight p K G,
  MonoidAlgebra.domCongr k k (normalizerEquiv e W.subgroup)
    (ownNormalizerBlock SG.operations W).1 =
      (ownNormalizerBlock SH.operations (W.mapGroupEquiv e)).1)

/-- The computed specified fibre map itself supplies the class equality.
The resulting group map reaches the independently selected TARGET pair. -/
theorem exists_physical_selected_pair (b : B) (w : SG.Fibre b) :
    ∃ g : H,
      (selectedCharacterWeight SG b w).mapGroupEquiv (correctedEquiv e g) =
        selectedCharacterWeight SH (blockLabelEquiv DG DH e b)
          (weightEquiv DG DH e SG SH ambientG ambientH ownPrimitive b w) := by
  apply exists_corrected_pair
  rw [show weightClass (selectedCharacterWeight SH (blockLabelEquiv DG DH e b)
      (weightEquiv DG DH e SG SH ambientG ambientH ownPrimitive b w)) =
      (weightEquiv DG DH e SG SH ambientG ambientH ownPrimitive b w).1 from
    selectedCharacterWeight_spec SH _ _]
  change conjugacyClassGroupEquiv e w.1 =
    conjugacyClassGroupEquiv e (weightClass (selectedCharacterWeight SG b w))
  rw [show weightClass (selectedCharacterWeight SG b w) = w.1 from
    selectedCharacterWeight_spec SG b w]

end PhysicalFibre

end ModularRep.PaperProofs.TypeCSelectedPairGroupEquivCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
