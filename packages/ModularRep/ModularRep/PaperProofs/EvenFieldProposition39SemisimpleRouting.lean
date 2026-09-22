import ModularRep.PaperProofs.EvenFieldProposition39HighRankU0

/-!
# Semisimple-guarded strict-block routing in even characteristic

This additive route replaces only the unguarded Bonnafe input in the old
`PairSourceInputsU0`. Bonnafe, Section 1.C and Example 4.8, concern the
semisimple element fixed in a maximal torus. The source label in FLZ,
Section 4.3 and Hypothesis 5.5, is semisimple. Neither statement supplies an
identity theorem for arbitrary elements of the full dual group.

The dual group and all three centralizers remain those of the existing
`PairStrictBlockSource`. Its intended ambient carrier is the algebraic dual
point group, containing the rational finite-dual label and finite centralizer
as well as the connected algebraic centralizer. It is not replaced by a
nongroup semisimple subtype, and no finiteness of that ambient carrier is
imposed. The semisimple predicate and the evidence for selected labels are
explicit E1 definition-interpretation data.

The type A input uses the cover-free actual SL/SU source, including its
finite-splitting and nondefining-prime applicability. The remaining branch
inputs retain their existing indexed source types. The new
router derives the identity only for a selected strict-block label, then
returns the same fixed cover-free Definition 3.5 output for every member of
`FullHG`. It does not construct the old unguarded source, alter a relation,
apply Theorem 5.7, or assert BAW-goodness or the original iBAW condition.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39SemisimpleRouting

open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks
open ModularRep.PaperProofs.EvenFieldProposition39HighRankU0
open ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder
open ModularRep.PaperProofs.EvenFieldProposition39Relative
open ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank
open ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven
open ModularRep.PaperProofs.EvenFieldProposition39Sp6Three
open ModularRep.PaperProofs.EvenFieldProposition39Suzuki
open ModularRep.PaperProofs.EvenFieldProposition39TypeA

/-- E1 interpretation of semisimplicity on the same dual carrier, with the
source's semisimple-label property for each strict block. This contains no
identity-label or block-bijection conclusion. -/
structure SemisimpleLabelSource {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    {pair : FullHG scope}
    (strictData : PairStrictBlockSource strictSource pair) where
  isSemisimple : strictData.Dual → Prop
  label_semisimple : ∀ block : PairBlock coverage pair,
    strictSource.predicate pair block →
      isSemisimple (strictData.label block)

/-- The existing branch playlist with the Bonnafe law restricted to its
published semisimple domain. Type A uses its cover-free source on the same
actual family. Automorphism adapters, relations and classifier indices are
unchanged, as are the cover requirements of the other branches. -/
structure GuardedPairSourceInputs {ell : ℕ}
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
  highRankP38To318 :
    ∀ (parameter : HighRankParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.rankAtLeastFour parameter)),
      Σ model : HighRankPairConcreteModelU0 classification pair parameter hcase,
        ∀ block, strictSource.predicate pair block →
          strictData.label block = 1 →
          HighRankP38To318SourceU0 blockSource classification pair parameter
            hcase model block
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

/-- Apply Bonnafe only to the selected semisimple label, after the existing
K inclusion from strict to ordinary quasi-isolation. -/
theorem label_eq_one_of_typeC {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {blockSource : FullHGBlockSource coverage}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    {classification : FullHGTypeCClassificationSource scope}
    {pair : FullHG scope}
    {strictData : PairStrictBlockSource strictSource pair}
    {labels : SemisimpleLabelSource strictData}
    (source : GuardedPairSourceInputs blockSource strictSource classification
      pair strictData labels)
    {form : TypeCForm}
    (hcase : classification.structuralCase coverage pair = .typeC form)
    (block : PairBlock coverage pair)
    (hstrict : strictSource.predicate pair block) :
    strictData.label block = 1 := by
  exact source.bonnafeIdentity hcase (labels.label_semisimple block hstrict)
    (quasiIsolated_of_strictlyQuasiIsolated
      (strictData.finiteCentralizer_le (strictData.label block))
      (strictData.connectedCentralizer_le (strictData.label block))
      (strictData.strictLabel block hstrict))

/-- Exhaustive routing on the same fixed Definition 3.5 carriers. The
outside-order case is still decided by literal divisibility; no semisimple
identity law is used in that arm or the type A arm. -/
theorem strictBlock_semisimple {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (strictData : PairStrictBlockSource strictSource pair)
    (labels : SemisimpleLabelSource strictData)
    (source : GuardedPairSourceInputs blockSource strictSource classification
      pair strictData labels) :
    ∀ block, strictSource.predicate pair block →
      HasDefinition35IBAW blockSource pair block := by
  intro block hstrict
  cases hcase : classification.structuralCase coverage pair with
  | primeOutsideOrder =>
      have hnotDvd :
          ¬ ell ∣ Nat.card (coverage.presentation pair).family.H :=
        (classification.structuralCase_eq_primeOutsideOrder_iff
          coverage pair).mp hcase
      exact
        (source.outsideOrder hnotDvd block hstrict).hasDefinition35IBAWBijection
  | typeA =>
      exact (source.typeA hcase).blockWitness scope.definingPrime scope.distinctPrimes block
  | typeC form =>
      have hlabel : strictData.label block = 1 :=
        label_eq_one_of_typeC source hcase block hstrict
      cases form with
      | rankAtLeastFour parameter =>
          obtain ⟨model, highRankSource⟩ :=
            source.highRankP38To318 parameter hcase
          exact (highRankSource block hstrict hlabel).toDefinition35
      | splitLowRank parameter =>
          exact (source.splitLowRank parameter hcase).blockWitness block
      | splitSp6Two prime =>
          cases prime with
          | three => exact (source.sp6AtThree hcase).blockWitness block
          | five => exact (source.sp6AtFive hcase).blockWitness block
          | seven => exact (source.sp6AtSeven hcase).blockWitness block
      | simpleSuzuki parameter =>
          exact (source.suzuki parameter hcase).blockWitness
            scope.distinctPrimes block

/-- Supply the full relative Hypothesis 5.5(b) without constructing or
assuming the old unguarded Bonnafe source. Every represented pair and every
strict block is retained, with the same fixed block-source relations. -/
theorem fullHG_strictBlocks_of_proposition39_semisimple {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (strictData : ∀ pair : FullHG scope,
      PairStrictBlockSource strictSource pair)
    (labels : ∀ pair : FullHG scope,
      SemisimpleLabelSource (strictData pair))
    (source : ∀ pair : FullHG scope,
      GuardedPairSourceInputs blockSource strictSource classification pair
        (strictData pair) (labels pair)) :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource where
  iBAWBijection pair block hstrict :=
    strictBlock_semisimple blockSource strictSource classification pair
      (strictData pair) (labels pair) (source pair) block hstrict

end ModularRep.PaperProofs.EvenFieldProposition39SemisimpleRouting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
