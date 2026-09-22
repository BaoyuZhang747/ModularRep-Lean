import ModularRep.PaperProofs.EvenFieldP38ChosenHighRankApplication

/-!
# The guarded strict-block playlist with an actual high-rank caller

Every branch has the same published source type as the semisimple router.
In particular, type A uses the actual SL/SU cover-free supplier, with the
same family, actions, coefficients and Definition 3.5 relations. Only the
high-rank application input is replaced here: the exact classified
P38 inputs precede the computed carrier, action and chosen-packet transport.
The target Fintype is transported through the actual family-to-concrete map.

The K consumer constructs the old guarded playlist. It neither assumes its
high-rank fibre/forward-relation fields nor strengthens the other named
external sources. The semisimple predicate still lives on the same algebraic
dual carrier and is used only for the selected label.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldChosenStrictBlockPlaylist

open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open EvenFieldFLZFullHG EvenFieldProposition39FullHGStrictBlocks
open EvenFieldProposition39HighRankU0 EvenFieldProposition39OutsideOrder
open EvenFieldProposition39Relative EvenFieldProposition39SplitLowRank
open EvenFieldProposition39Sp6CyclicFiveSeven EvenFieldProposition39Sp6Three
open EvenFieldProposition39Suzuki EvenFieldProposition39TypeA
open EvenFieldProposition39SemisimpleRouting

/-- The semisimple source playlist, with the cover-free actual type A
supplier and construction inputs for the high-rank classified family. -/
structure SourceInputs {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (strictData : PairStrictBlockSource strictSource pair)
    (labels : SemisimpleLabelSource strictData) where
  outsideOrder : ¬ ell ∣ Nat.card (coverage.presentation pair).family.H →
    ∀ block, strictSource.predicate pair block →
      OutsideOrderSource (coverage.presentation pair).family block
        (blockSource.automorphisms pair block)
        (blockSource.source pair block)
  typeA : classification.structuralCase coverage pair = .typeA →
    CoverFreeTypeAApplication (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  bonnafeIdentity : ∀ {form : TypeCForm} {s : strictData.Dual},
    classification.structuralCase coverage pair = .typeC form →
      labels.isSemisimple s →
      NotContainedInProperLevi (Subgroup.centralizer {s} : Set strictData.Dual)
        strictData.IsProperLevi →
      s = 1
  highRank :
    ∀ (parameter : HighRankParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.rankAtLeastFour parameter)),
      Σ model : HighRankPairConcreteModelU0 classification pair parameter hcase,
        letI := Fintype.ofEquiv (coverage.presentation pair).family.H
          (model.familyToConcrete (coverage.presentation pair)).toEquiv
        ∀ block, strictSource.predicate pair block →
          strictData.label block = 1 →
          EvenFieldP38ChosenHighRankApplication.ClassifiedInputs
            blockSource classification pair parameter hcase model block
  splitLowRank : ∀ (parameter : SplitLowRankParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.splitLowRank parameter)),
    SchaefferFrySplitLowRankFamilySource classification pair parameter hcase
      (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtThree : classification.structuralCase coverage pair =
      .typeC (.splitSp6Two .three) →
    Sp6TwoThreeSource (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtFive : classification.structuralCase coverage pair =
      .typeC (.splitSp6Two .five) →
    Sp6TwoCyclicFiveSevenSource .five (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtSeven : classification.structuralCase coverage pair =
      .typeC (.splitSp6Two .seven) →
    Sp6TwoCyclicFiveSevenSource .seven (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  suzuki : ∀ (parameter : SuzukiParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.simpleSuzuki parameter)),
    SpathSuzukiFamilySource classification pair parameter hcase
      (blockSource.automorphisms pair) (blockSource.source pair)

variable {ell : ℕ} {scope : FLZFullHGUniverse 2 ell}
variable {coverage : FullHGDefinition35Coverage scope}
variable {blockSource : FullHGBlockSource coverage}
variable {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
variable {classification : FullHGTypeCClassificationSource scope}
variable {pair : FullHG scope} {strictData : PairStrictBlockSource strictSource pair}
variable {labels : SemisimpleLabelSource strictData}

/-- Compute the old high-rank carrier/action/relation application fields
using the actual chosen-packet caller; all other branches are unchanged. -/
def SourceInputs.toGuarded
    (source : SourceInputs blockSource strictSource classification pair strictData labels) :
    GuardedPairSourceInputs blockSource strictSource classification pair strictData labels where
  outsideOrder := source.outsideOrder
  typeA := source.typeA
  bonnafeIdentity := source.bonnafeIdentity
  highRankP38To318 parameter hcase := by
    obtain ⟨model, data⟩ := source.highRank parameter hcase
    letI := Fintype.ofEquiv (coverage.presentation pair).family.H
      (model.familyToConcrete (coverage.presentation pair)).toEquiv
    refine ⟨model, ?_⟩
    intro block hstrict hlabel
    exact EvenFieldP38ChosenHighRankApplication.toHighRankSource
      blockSource classification pair parameter hcase model block
      (data block hstrict hlabel)
  splitLowRank := source.splitLowRank
  sp6AtThree := source.sp6AtThree
  sp6AtFive := source.sp6AtFive
  sp6AtSeven := source.sp6AtSeven
  suzuki := source.suzuki

end ModularRep.PaperProofs.EvenFieldChosenStrictBlockPlaylist


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
