import ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
import ModularRep.PaperProofs.OddTwoGroupEquivOwnReduction
import ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport

/-!
# Selected quotient reduction from the fixed routed family

The inverse of the COMPUTED weight fibre equivalence selects the family
weight. Its fixed family.localReduction supplies the quotient root and
Brauer character. Equality of actual weight classes gives an inner
correction of the WHOLE own-character pair. The corrected normalizer and
quotient maps transport that exact reduction to the intrinsic selection.

No equivariant representative selection, reduction-existence source,
independent-root equality, common-table convention, or relation is added.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilySelectedReduction

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates
open ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport

universe u

section CorrectedCoordinates

variable {p : ℕ} {K G H : Type u}
variable [Field K] [CharZero K] [Group G] [Fintype G] [Group H] [Fintype H]
variable (W : CharacterWeight p K G) (V : CharacterWeight p K H) (e : G ≃* H)
variable (hclass : weightClass V = weightClass (W.mapGroupEquiv e))

include hclass in
/-- Class equality yields a whole own-character pair correction. -/
theorem exists_inner_correction :
    ∃ g : H, (W.mapGroupEquiv e).rightTwist (MulAut.conj g)⁻¹ = V := by
  obtain ⟨g, hg⟩ := exists_coordinate_of_class_eq (W.mapGroupEquiv e) V 1
    (by simpa only [inv_one, rightTwistConjugacyClass_one] using hclass)
  exact ⟨g, by simpa only [coordinateAutomorphism, mul_one] using hg⟩

/-- Choice uses the proved two-quotient equality, not subgroup conjugacy. -/
def correctionElement : H := Classical.choose (exists_inner_correction W V e hclass)

theorem correctionElement_spec :
    (W.mapGroupEquiv e).rightTwist (MulAut.conj (correctionElement W V e hclass))⁻¹ = V :=
  Classical.choose_spec (exists_inner_correction W V e hclass)

/-- The corrected ambient coordinate is exactly e followed by conjugation. -/
def correctedGroupEquiv : G ≃* H :=
  e.trans (MulAut.conj (correctionElement W V e hclass))

@[simp] theorem correctedGroupEquiv_apply (x : G) :
    correctedGroupEquiv W V e hclass x =
      correctionElement W V e hclass * e x * (correctionElement W V e hclass)⁻¹ := rfl

/-- Compose the canonical normalizer map with the computed whole-pair map. -/
def correctedNormalizerEquiv :
    Subgroup.normalizer (W.subgroup : Set G) ≃*
      Subgroup.normalizer (V.subgroup : Set H) :=
  (normalizerEquiv e W.subgroup).trans
    (ownNormalizerEquiv (W.mapGroupEquiv e) V
      (MulAut.conj (correctionElement W V e hclass))
      (correctionElement_spec W V e hclass))

/-- The quotient map uses exactly the same two coordinate steps. -/
def correctedQuotientEquiv : NormalizerQuotient W.subgroup ≃* NormalizerQuotient V.subgroup :=
  (normalizerQuotientEquiv e W.subgroup).trans
    (ownNormalizerQuotientEquiv (W.mapGroupEquiv e) V
      (MulAut.conj (correctionElement W V e hclass))
      (correctionElement_spec W V e hclass))

theorem correctedNormalizerEquiv_coe
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    (correctedNormalizerEquiv W V e hclass x : H) =
      correctedGroupEquiv W V e hclass (x : G) := by
  exact ownNormalizerEquiv_coe (W.mapGroupEquiv e) V
    (MulAut.conj (correctionElement W V e hclass))
    (correctionElement_spec W V e hclass) (normalizerEquiv e W.subgroup x)

/-- The exact ambient inclusion square retains the original group e and g. -/
theorem correctedNormalizerEquiv_inclusion :
    (correctedGroupEquiv W V e hclass).toMonoidHom.comp
        (Subgroup.normalizer (W.subgroup : Set G)).subtype =
      (Subgroup.normalizer (V.subgroup : Set H)).subtype.comp
        (correctedNormalizerEquiv W V e hclass).toMonoidHom := by
  ext x
  exact (correctedNormalizerEquiv_coe W V e hclass x).symm

/-- Actual quotient generators commute with the corrected normalizer map. -/
theorem correctedQuotientEquiv_mk
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    correctedQuotientEquiv W V e hclass (QuotientGroup.mk x) =
      QuotientGroup.mk (correctedNormalizerEquiv W V e hclass x) := by
  exact ownNormalizerQuotientEquiv_mk (W.mapGroupEquiv e) V
    (MulAut.conj (correctionElement W V e hclass))
    (correctionElement_spec W V e hclass) (normalizerEquiv e W.subgroup x)

/-- The OWN character, not only the radical subgroup, travels through etaQ. -/
theorem correctedQuotientEquiv_own_values (x : NormalizerQuotient W.subgroup) :
    V.localCharacter (correctedQuotientEquiv W V e hclass x) = W.localCharacter x := by
  exact (ownOrdinary_character_values (W.mapGroupEquiv e) V
    (MulAut.conj (correctionElement W V e hclass))
    (correctionElement_spec W V e hclass) (normalizerQuotientEquiv e W.subgroup x)).trans
      (mapGroupEquiv_localCharacter_image W e x)

theorem correctedQuotientEquiv_own_inverse_values (x : NormalizerQuotient V.subgroup) :
    V.localCharacter x =
      W.localCharacter ((correctedQuotientEquiv W V e hclass).symm x) := by
  have h := correctedQuotientEquiv_own_values W V e hclass
    ((correctedQuotientEquiv W V e hclass).symm x)
  have cancel := congrArg V.localCharacter
    ((correctedQuotientEquiv W V e hclass).apply_symm_apply x)
  exact cancel.symm.trans h

end CorrectedCoordinates

section FamilySelection

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)
variable (input : TypeAInputSemantics family)
variable (OH : LocalBlockInductionOperations
  (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block))
variable (dictionary : PrimitiveDictionary family.blockSource.operations OH
  (groupEquiv family block carrier))

local instance selectedFamilySpFintype : Fintype (Sp rank F) := Fintype.ofFinite _

/-- The exact intrinsic principal fibre with its constructed block action. -/
abbrev IntrinsicWeight :=
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  (data family block carrier input OH dictionary).PrincipalWeight

variable (w : IntrinsicWeight family block carrier input OH dictionary)

/-- Inverse image under the computed fibre equivalence, with no new map. -/
def familyWeight : Definition35Weight (family.problem block) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact (weightEquiv family block carrier input OH dictionary).symm w

/-- The fixed family selection at that inverse image. -/
def familyPair : CharacterWeight 2 family.K family.H :=
  selectedCharacterWeight family.blockSource block
    (familyWeight family block carrier input OH dictionary w)

/-- The actual raw image before correcting to the intrinsic selection. -/
def imagePair : CharacterWeight 2 family.K (Sp rank F) :=
  (familyPair family block carrier input OH dictionary w).mapGroupEquiv
    (groupEquiv family block carrier)

/-- The existing intrinsic choice of a whole own-character representative. -/
def intrinsicPair : CharacterWeight 2 family.K (Sp rank F) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact weightRepresentative (data family block carrier input OH dictionary) w

/-- Both actual selection specifications and the computed fibre equivalence
give class equality. Selection itself is never asserted equivariant. -/
theorem selected_class_eq :
    weightClass (intrinsicPair family block carrier input OH dictionary w) =
      weightClass (imagePair family block carrier input OH dictionary w) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  have sourceSpec := selectedCharacterWeight_spec family.blockSource block
    (familyWeight family block carrier input OH dictionary w)
  have targetSpec := selectedCharacterWeight_spec
    (data family block carrier input OH dictionary).blockSource
    (data family block carrier input OH dictionary).principalBlock w
  have imageSpec := weightEquiv_class family block carrier input OH dictionary
    (familyWeight family block carrier input OH dictionary w)
  have inverseSpec := congrArg Subtype.val
    ((weightEquiv family block carrier input OH dictionary).apply_symm_apply w)
  have mappedSourceSpec :=
    congrArg (CharacterWeight.conjugacyClassGroupEquiv (groupEquiv family block carrier))
      sourceSpec.symm
  have targetEquality :
      weightClass (intrinsicPair family block carrier input OH dictionary w) = w.1 := targetSpec
  exact targetEquality.trans (inverseSpec.symm.trans (imageSpec.trans mappedSourceSpec))

/-- The selected inner correction depends only on this actual weight. -/
def selectedCorrection : Sp rank F :=
  correctionElement (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)

theorem selectedCorrection_spec :
    (imagePair family block carrier input OH dictionary w).rightTwist
        (MulAut.conj (selectedCorrection family block carrier input OH dictionary w))⁻¹ =
      intrinsicPair family block carrier input OH dictionary w :=
  correctionElement_spec (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)

/-- The actual corrected ambient map etaH. -/
def selectedGroupEquiv : family.H ≃* Sp rank F :=
  correctedGroupEquiv (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)

/-- The actual corrected own-normalizer map etaN. -/
def selectedNormalizerEquiv :
    Subgroup.normalizer ((familyPair family block carrier input OH dictionary w).subgroup :
      Set family.H) ≃*
    Subgroup.normalizer ((intrinsicPair family block carrier input OH dictionary w).subgroup :
      Set (Sp rank F)) :=
  correctedNormalizerEquiv (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)

/-- The computed etaQ binds the fixed family pair to the intrinsic pair. -/
def selectedQuotientEquiv :
    NormalizerQuotient (familyPair family block carrier input OH dictionary w).subgroup ≃*
      NormalizerQuotient (intrinsicPair family block carrier input OH dictionary w).subgroup :=
  correctedQuotientEquiv
    (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)

theorem selectedNormalizerEquiv_coe
    (x : Subgroup.normalizer
      ((familyPair family block carrier input OH dictionary w).subgroup : Set family.H)) :
    (selectedNormalizerEquiv family block carrier input OH dictionary w x : Sp rank F) =
      selectedGroupEquiv family block carrier input OH dictionary w (x : family.H) :=
  correctedNormalizerEquiv_coe (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w) x

theorem selectedQuotientEquiv_mk
    (x : Subgroup.normalizer
      ((familyPair family block carrier input OH dictionary w).subgroup : Set family.H)) :
    selectedQuotientEquiv family block carrier input OH dictionary w (QuotientGroup.mk x) =
      QuotientGroup.mk (selectedNormalizerEquiv family block carrier input OH dictionary w x) :=
  correctedQuotientEquiv_mk (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w) x

theorem selectedQuotientEquiv_own_values
    (x : NormalizerQuotient (familyPair family block carrier input OH dictionary w).subgroup) :
    (intrinsicPair family block carrier input OH dictionary w).localCharacter
        (selectedQuotientEquiv family block carrier input OH dictionary w x) =
      (familyPair family block carrier input OH dictionary w).localCharacter x :=
  correctedQuotientEquiv_own_values (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w) x

/-- The fixed family reduction is used verbatim at the computed inverse. -/
def fixedFamilyReduction : SelectedLocalReductionSource family.blockSource block
    (familyWeight family block carrier input OH dictionary w) :=
  family.localReduction block (familyWeight family block carrier input OH dictionary w)

/-- The quotient root is the fixed family root transported through etaQ. -/
def selectedRoot : PrimeRegularRootEmbedding 2 family.k family.K
    (NormalizerQuotient (intrinsicPair family block carrier input OH dictionary w).subgroup) :=
  (fixedFamilyReduction family block carrier input OH dictionary w).iota.alongMulEquiv
    (selectedQuotientEquiv family block carrier input OH dictionary w)

/-- The actual quotient IBr is computed from the fixed family IBr. -/
def selectedBrauer : IBr (selectedRoot family block carrier input OH dictionary w) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv
    (fixedFamilyReduction family block carrier input OH dictionary w).iota
    (selectedQuotientEquiv family block carrier input OH dictionary w)
    (fixedFamilyReduction family block carrier input OH dictionary w).brauer

theorem selectedBrauer_values
    (x : PrimeRegularElement (G := NormalizerQuotient
      (intrinsicPair family block carrier input OH dictionary w).subgroup) 2) :
    (selectedBrauer family block carrier input OH dictionary w).1 x =
      (fixedFamilyReduction family block carrier input OH dictionary w).brauer.1
        (PrimeRegularElement.map
          (selectedQuotientEquiv family block carrier input OH dictionary w).symm.toMonoidHom x) := rfl

/-- Package the derived reduction on the EXACT intrinsic selected pair. -/
def selectedReduction :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    SelectedLocalReductionSource (data family block carrier input OH dictionary).blockSource
      (data family block carrier input OH dictionary).principalBlock w := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  refine
    { iota := selectedRoot family block carrier input OH dictionary w
      brauer := selectedBrauer family block carrier input OH dictionary w
      reduction := ?_ }
  intro x
  exact (correctedQuotientEquiv_own_inverse_values
    (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w) x.1).trans
      ((fixedFamilyReduction family block carrier input OH dictionary w).reduction
        (PrimeRegularElement.map
          (selectedQuotientEquiv family block carrier input OH dictionary w).symm.toMonoidHom x))

/-- The exact Definition 3.5 problem stores this computed reduction verbatim. -/
theorem problem_localReduction :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    ((data family block carrier input OH dictionary).problem
      (selectedReduction family block carrier input OH dictionary)).localReduction w =
      selectedReduction family block carrier input OH dictionary w := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  rfl

end FamilySelection

end ModularRep.PaperProofs.OddTwoPrincipalFamilySelectedReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
