import ModularRep.PaperProofs.OddTwoPrincipalFamilySelectedReduction
import ModularRep.PaperProofs.OddTwoCommonRootGroupEquiv

/-!
# The fixed family's one-table convention on the computed intrinsic selection

The sole E1 record binds EVERY fixed family selected quotient root to a
restriction of the same transported ambient table. It contains no inner
correction, normalizer root, compatibility, character, relation or seed.
The actual selected quotient transport carries that binding to the
intrinsic engine in K. The downstairs root is chosen as the corresponding
restriction, so its required binding is reflexive.

This convention is separate from transport of arbitrary own-root packets.
It does not assert equality of independently prescribed root conventions.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilyCommonRoots

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
open ModularRep.PaperProofs.OddTwoPrincipalFamilySelectedReduction
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions
open ModularRep.PaperProofs.OddTwoCommonRootGroupEquiv

universe u

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)

local instance familyCommonSpFintype : Fintype (Sp rank F) := Fintype.ofFinite _

include carrier in
/-- The bound uses the actual family normalizer quotient and actual e. -/
theorem familyQuotient_exponent_dvd (v : Definition35Weight (family.problem block)) :
    primeRegularExponent 2
        (NormalizerQuotient (selectedCharacterWeight family.blockSource block v).subgroup) ∣
      primeRegularExponent 2 (Sp rank F) := by
  have quotientBound :=
    ((selectedCharacterWeight family.blockSource block v).subgroup.subgroupOf
      (Subgroup.normalizer
        ((selectedCharacterWeight family.blockSource block v).subgroup :
          Set family.H))).card_quotient_dvd_card
  have normalizerBound := Subgroup.card_subgroup_dvd_card
    (Subgroup.normalizer
      ((selectedCharacterWeight family.blockSource block v).subgroup : Set family.H))
  have orderBound := quotientBound.trans normalizerBound
  have actualOrder := Nat.card_congr (groupEquiv family block carrier).toEquiv
  exact exponent_dvd_of_card_dvd (actualOrder ▸ orderBound)

/-- Narrow E1 bookkeeping on the FIXED selected quotient tables. The
ambient table is computed from family.iota and the routed group map.
No favourable reduction may be selected after a matched pair is known. -/
structure FamilyCommonRootConvention : Prop where
  selected_root : ∀ v : Definition35Weight (family.problem block),
    (family.localReduction block v).iota =
      PrimeRegularRootEmbedding.ofCommonRoot
        (symplecticRoot family block carrier).prime
        (symplecticRoot family block carrier).toMulEquiv
        (familyQuotient_exponent_dvd family block carrier v)

variable (input : TypeAInputSemantics family)
variable (OH : LocalBlockInductionOperations
  (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block))
variable (dictionary : PrimitiveDictionary family.blockSource.operations OH
  (groupEquiv family block carrier))
variable (C : FamilyCommonRootConvention family block carrier)

include C in
/-- The computed etaQ transports the exact fixed-table binding. This is
the selected-root clause required by the intrinsic canonical engine. -/
theorem intrinsic_selected_root
    (w : IntrinsicWeight family block carrier input OH dictionary) :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    (selectedQuotientReduction (data family block carrier input OH dictionary)
      (selectedReduction family block carrier input OH dictionary) w).iota =
      rootAt (data family block carrier input OH dictionary)
        (NormalizerQuotient
          (weightRepresentative (data family block carrier input OH dictionary) w).subgroup)
        (upQuotient_exponent_dvd (data family block carrier input OH dictionary) w) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  have binding := C.selected_root (familyWeight family block carrier input OH dictionary w)
  have transported := congrArg
    (fun root : PrimeRegularRootEmbedding 2 family.k family.K
        (NormalizerQuotient (familyPair family block carrier input OH dictionary w).subgroup) =>
      root.alongMulEquiv (selectedQuotientEquiv family block carrier input OH dictionary w))
    binding
  exact transported.trans
    (ofCommonRoot_alongMulEquiv (symplecticRoot family block carrier).prime
      (symplecticRoot family block carrier).toMulEquiv
      (familyQuotient_exponent_dvd family block carrier
        (familyWeight family block carrier input OH dictionary w))
      (upQuotient_exponent_dvd (data family block carrier input OH dictionary) w)
      (selectedQuotientEquiv family block carrier input OH dictionary w))

variable (cover : OddSymplecticFullCoverSource rank F)

/-- Choose the downstairs root from the same table, using the actual
full-cover exponent bound. No independent downstairs-root equality is inferred. -/
def canonicalDownRoot : PrimeRegularRootEmbedding 2 family.k family.K (LiteralPSp rank F) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact rootAt (data family block carrier input OH dictionary)
    (LiteralPSp rank F) (projective_exponent_dvd cover)

/-- K construction of the intrinsic convention from the fixed family table
binding and the computed selected reduction. The PSp binding is reflexive. -/
def toCommonRootConvention :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    CommonRootConvention (data family block carrier input OH dictionary)
      (selectedReduction family block carrier input OH dictionary) cover
      (canonicalDownRoot family block carrier input OH dictionary cover) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact
    { downRoot_eq := rfl
      selectedRoot_eq := intrinsic_selected_root family block carrier input OH dictionary C }

end ModularRep.PaperProofs.OddTwoPrincipalFamilyCommonRoots


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
