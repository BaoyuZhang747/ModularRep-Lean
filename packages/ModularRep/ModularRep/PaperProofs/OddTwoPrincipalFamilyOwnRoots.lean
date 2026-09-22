import ModularRep.PaperProofs.OddTwoPrincipalFamilySelectedReduction
import ModularRep.PaperProofs.OddTwoCommonRootGroupEquiv

/-!
# Every admissible intrinsic own-root packet on the fixed family

Pull the actual intrinsic own reduction back through the computed selected
normalizer equivalence. Its ordinary character is the fixed family pair's
OWN character. Both admissibility squares return to the family ambient
root and its EXACT stored quotient root through the actual coordinate
squares and literal lift identities. No canonical-root convention or
relation interpretation is an input to this construction.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilyOwnRoots

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
open ModularRep.PaperProofs.OddTwoPrincipalFamilySelectedReduction
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoCommonRootGroupEquiv
open ModularRep.PaperProofs.OddTwoGroupEquivOwnReduction
open ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

universe u

local instance familyOwnRootsSubgroupFintype {A : Type u}
    [Group A] [Finite A] (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

section CorrectedPullback

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]
variable (W : CharacterWeight p K G) (V : CharacterWeight p K H) (e : G ≃* H)
variable (hclass : weightClass V = weightClass (W.mapGroupEquiv e))
variable (R : OwnNormalizerReduction (k := k) V)

/-- The arbitrary target convention is pulled back through the SAME etaN. -/
def pulledRoot : PrimeRegularRootEmbedding p k K
    (Subgroup.normalizer (W.subgroup : Set G)) :=
  (ownReductionRoot V R).alongMulEquiv (correctedNormalizerEquiv W V e hclass).symm

/-- The actual target IBr determines the family normalizer IBr. -/
def pulledBrauer : IBr (pulledRoot W V e hclass R) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (ownReductionRoot V R)
    (correctedNormalizerEquiv W V e hclass).symm (ownReductionBrauer V R)

theorem pulledBrauer_values
    (x : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set G)) p) :
    (pulledBrauer W V e hclass R).1 x =
      (ownReductionBrauer V R).1 (PrimeRegularElement.map
        (correctedNormalizerEquiv W V e hclass).toMonoidHom x) := rfl

/-- Both the actual mk square and the whole-pair character identity are used. -/
theorem pulledBrauer_ownReduction :
    NormalizerInflatedReduction W.subgroup W.localCharacter
      (pulledRoot W V e hclass R) (pulledBrauer W V e hclass R) := by
  intro x
  have values := correctedQuotientEquiv_own_values W V e hclass (QuotientGroup.mk x.1)
  have square := congrArg V.localCharacter (correctedQuotientEquiv_mk W V e hclass x.1)
  exact (values.symm.trans square).trans (ownReductionValues V R
    (PrimeRegularElement.map (correctedNormalizerEquiv W V e hclass).toMonoidHom x))

/-- No new own-character reduction is chosen or assumed. -/
def pullbackOwnReduction : OwnNormalizerReduction (k := k) W where
  root := pulledRoot W V e hclass R
  brauer := pulledBrauer W V e hclass R
  own_reduction := pulledBrauer_ownReduction W V e hclass R

@[simp] theorem pullbackOwnReduction_root :
    ownReductionRoot W (pullbackOwnReduction W V e hclass R) =
      (ownReductionRoot V R).alongMulEquiv
        (correctedNormalizerEquiv W V e hclass).symm := rfl

theorem pullbackOwnReduction_lift (z : k) :
    (ownReductionRoot W (pullbackOwnReduction W V e hclass R)).lift z =
      (ownReductionRoot V R).lift z :=
  (ownReductionRoot V R).alongMulEquiv_lift
    (correctedNormalizerEquiv W V e hclass).symm z

/-- The inverse ambient square is derived from the computed forward square. -/
theorem correctedNormalizerEquiv_inverse_coe
    (x : Subgroup.normalizer (V.subgroup : Set H)) :
    ((correctedNormalizerEquiv W V e hclass).symm x : G) =
      (correctedGroupEquiv W V e hclass).symm (x : H) := by
  apply (correctedGroupEquiv W V e hclass).injective
  have square := correctedNormalizerEquiv_coe W V e hclass
    ((correctedNormalizerEquiv W V e hclass).symm x)
  have cancel := congrArg (fun y : Subgroup.normalizer (V.subgroup : Set H) => (y : H))
    ((correctedNormalizerEquiv W V e hclass).apply_symm_apply x)
  exact (square.symm.trans cancel).trans
    ((correctedGroupEquiv W V e hclass).apply_symm_apply (x : H)).symm

/-- The inverse quotient square retains the original quotient generators. -/
theorem correctedQuotientEquiv_inverse_mk
    (x : Subgroup.normalizer (V.subgroup : Set H)) :
    QuotientGroup.mk ((correctedNormalizerEquiv W V e hclass).symm x) =
      (correctedQuotientEquiv W V e hclass).symm (QuotientGroup.mk x) := by
  apply (correctedQuotientEquiv W V e hclass).injective
  have square := correctedQuotientEquiv_mk W V e hclass
    ((correctedNormalizerEquiv W V e hclass).symm x)
  have cancel := congrArg (fun y : Subgroup.normalizer (V.subgroup : Set H) =>
      (QuotientGroup.mk y : NormalizerQuotient V.subgroup))
    ((correctedNormalizerEquiv W V e hclass).apply_symm_apply x)
  exact (square.trans cancel).trans
    ((correctedQuotientEquiv W V e hclass).apply_symm_apply (QuotientGroup.mk x)).symm

/-- Transport the existing ambient square backwards, then replace only the
literally unchanged lift by that of the fixed original ambient root. -/
theorem pullbackOwnReduction_ambientCompatible
    (iota : PrimeRegularRootEmbedding p k K G)
    (compatible : RootCompatibleAlong (iota.alongMulEquiv e) (ownReductionRoot V R)
      (Subgroup.normalizer (V.subgroup : Set H)).subtype) :
    RootCompatibleAlong iota (ownReductionRoot W (pullbackOwnReduction W V e hclass R))
      (Subgroup.normalizer (W.subgroup : Set G)).subtype := by
  have transported := rootCompatibleAlong_transport (ownReductionRoot V R)
    (iota.alongMulEquiv e) (Subgroup.normalizer (V.subgroup : Set H)).subtype
    (correctedNormalizerEquiv W V e hclass).symm
    (correctedGroupEquiv W V e hclass).symm
    (Subgroup.normalizer (W.subgroup : Set G)).subtype
    (correctedNormalizerEquiv_inverse_coe W V e hclass) compatible
  apply compatible_replace_target_lift
    ((iota.alongMulEquiv e).alongMulEquiv (correctedGroupEquiv W V e hclass).symm)
    iota (ownReductionRoot W (pullbackOwnReduction W V e hclass R))
    (Subgroup.normalizer (W.subgroup : Set G)).subtype _ transported
  funext z
  exact ((iota.alongMulEquiv e).alongMulEquiv_lift
    (correctedGroupEquiv W V e hclass).symm z).trans (iota.alongMulEquiv_lift e z)

/-- The target quotient root is the actual transport of the FIXED source
root. Backward transport therefore recovers its exact compatibility square. -/
theorem pullbackOwnReduction_quotientCompatible
    (rootQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (compatible : RootCompatibleAlong
      (rootQ.alongMulEquiv (correctedQuotientEquiv W V e hclass)) (ownReductionRoot V R)
      (normalizerProjection V.subgroup)) :
    RootCompatibleAlong rootQ (ownReductionRoot W (pullbackOwnReduction W V e hclass R))
      (normalizerProjection W.subgroup) := by
  have transported := rootCompatibleAlong_transport (ownReductionRoot V R)
    (rootQ.alongMulEquiv (correctedQuotientEquiv W V e hclass))
    (normalizerProjection V.subgroup)
    (correctedNormalizerEquiv W V e hclass).symm
    (correctedQuotientEquiv W V e hclass).symm
    (normalizerProjection W.subgroup)
    (correctedQuotientEquiv_inverse_mk W V e hclass) compatible
  exact compatible_replace_target_lift
    ((rootQ.alongMulEquiv (correctedQuotientEquiv W V e hclass)).alongMulEquiv
      (correctedQuotientEquiv W V e hclass).symm)
    rootQ (ownReductionRoot W (pullbackOwnReduction W V e hclass R))
    (normalizerProjection W.subgroup)
    (alongMulEquiv_inverse_lift rootQ (correctedQuotientEquiv W V e hclass)) transported

/-- The exact forward etaN square is automatic for this computed pullback. -/
theorem pullbackOwnReduction_horizontal :
    RootCompatibleAlong (ownReductionRoot V R)
      (ownReductionRoot W (pullbackOwnReduction W V e hclass R))
      (correctedNormalizerEquiv W V e hclass).toMonoidHom :=
  backwardRoot_horizontal (ownReductionRoot V R) (correctedNormalizerEquiv W V e hclass)

/-- After mapping the family packet forward through e, its lift and the
original arbitrary target lift agree along the actual inner correction. -/
theorem pullbackOwnReduction_innerHorizontal :
    RootCompatibleAlong (ownReductionRoot V R)
      (ownReductionRoot (W.mapGroupEquiv e)
        (mapOwnReduction W e (pullbackOwnReduction W V e hclass R)))
      (ownNormalizerEquiv (W.mapGroupEquiv e) V
        (MulAut.conj (correctionElement W V e hclass))
        (correctionElement_spec W V e hclass)).toMonoidHom := by
  intro A x a
  exact ((ownReductionRoot W (pullbackOwnReduction W V e hclass R)).alongMulEquiv_lift
    (normalizerEquiv e W.subgroup) a.1).trans
      (pullbackOwnReduction_lift W V e hclass R a.1)

end CorrectedPullback

section Family

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)
variable (input : TypeAInputSemantics family)
variable (OH : LocalBlockInductionOperations
  (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block))
variable (dictionary : PrimitiveDictionary family.blockSource.operations OH
  (groupEquiv family block carrier))

local instance familyOwnRootsSpFintype : Fintype (Sp rank F) := Fintype.ofFinite _

variable (w : IntrinsicWeight family block carrier input OH dictionary)

/-- EVERY packet on the exact constructed D and exact selected reduction. -/
abbrev AdmissibleRoots :=
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  SelectedNormalizerRoots (data family block carrier input OH dictionary)
    (selectedReduction family block carrier input OH dictionary) w

variable (roots : AdmissibleRoots family block carrier input OH dictionary w)

/-- Preserve the original intrinsic packet and its computed own IBr. -/
def intrinsicOwnReduction :
    OwnNormalizerReduction (k := family.k)
      (intrinsicPair family block carrier input OH dictionary w) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact ownReduction (data family block carrier input OH dictionary)
    (selectedReduction family block carrier input OH dictionary) w roots

/-- Pull back the original arbitrary packet to the SAME fixed family pair. -/
def familyOwnReduction :
    OwnNormalizerReduction (k := family.k)
      (familyPair family block carrier input OH dictionary w) :=
  pullbackOwnReduction (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)
    (intrinsicOwnReduction family block carrier input OH dictionary w roots)

@[simp] theorem familyOwnReduction_root :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    ownReductionRoot (familyPair family block carrier input OH dictionary w)
        (familyOwnReduction family block carrier input OH dictionary w roots) =
      roots.root.alongMulEquiv
        (selectedNormalizerEquiv family block carrier input OH dictionary w).symm := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  rfl

theorem familyOwnReduction_lift (z : family.k) :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    (ownReductionRoot (familyPair family block carrier input OH dictionary w)
      (familyOwnReduction family block carrier input OH dictionary w roots)).lift z =
      roots.root.lift z := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact pullbackOwnReduction_lift (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)
    (intrinsicOwnReduction family block carrier input OH dictionary w roots) z

/-- Explicit own-normalizer values retain the original intrinsic reduction. -/
theorem familyOwnReduction_values
    (x : PrimeRegularElement (G := Subgroup.normalizer
      ((familyPair family block carrier input OH dictionary w).subgroup : Set family.H)) 2) :
    (ownReductionBrauer (familyPair family block carrier input OH dictionary w)
      (familyOwnReduction family block carrier input OH dictionary w roots)).1 x =
      (ownReductionBrauer (intrinsicPair family block carrier input OH dictionary w)
        (intrinsicOwnReduction family block carrier input OH dictionary w roots)).1
        (PrimeRegularElement.map
          (selectedNormalizerEquiv family block carrier input OH dictionary w).toMonoidHom x) := rfl

/-- First exact RelativeRootsCompatible square, on the fixed family ambient root. -/
theorem familyOwnReduction_ambientCompatible :
    RootCompatibleAlong family.iota
      (ownReductionRoot (familyPair family block carrier input OH dictionary w)
        (familyOwnReduction family block carrier input OH dictionary w roots))
      (Subgroup.normalizer
        ((familyPair family block carrier input OH dictionary w).subgroup : Set family.H)).subtype := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact pullbackOwnReduction_ambientCompatible
    (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)
    (intrinsicOwnReduction family block carrier input OH dictionary w roots)
    family.iota roots.ambientCompatible

/-- Second exact square, on family.localReduction at the computed inverse w. -/
theorem familyOwnReduction_quotientCompatible :
    RootCompatibleAlong
      (family.localReduction block (familyWeight family block carrier input OH dictionary w)).iota
      (ownReductionRoot (familyPair family block carrier input OH dictionary w)
        (familyOwnReduction family block carrier input OH dictionary w roots))
      (normalizerProjection (familyPair family block carrier input OH dictionary w).subgroup) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact pullbackOwnReduction_quotientCompatible
    (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)
    (intrinsicOwnReduction family block carrier input OH dictionary w roots)
    (fixedFamilyReduction family block carrier input OH dictionary w).iota
    roots.quotientCompatible

/-- The exact selected normalizer map supplies the forward horizontal square. -/
theorem familyOwnReduction_horizontal :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    RootCompatibleAlong roots.root
      (ownReductionRoot (familyPair family block carrier input OH dictionary w)
        (familyOwnReduction family block carrier input OH dictionary w roots))
      (selectedNormalizerEquiv family block carrier input OH dictionary w).toMonoidHom := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact pullbackOwnReduction_horizontal
    (familyPair family block carrier input OH dictionary w)
    (intrinsicPair family block carrier input OH dictionary w)
    (groupEquiv family block carrier)
    (selected_class_eq family block carrier input OH dictionary w)
    (intrinsicOwnReduction family block carrier input OH dictionary w roots)

end Family

end ModularRep.PaperProofs.OddTwoPrincipalFamilyOwnRoots


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
