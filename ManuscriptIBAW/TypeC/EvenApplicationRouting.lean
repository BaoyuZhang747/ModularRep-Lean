import ManuscriptIBAW.TypeC.EvenApplicationHighRank
import ManuscriptIBAW.TypeC.EvenApplicationSp6Two
import ManuscriptIBAW.TypeC.EvenApplicationSuzuki

/-! Proposition 3.9 on the full relative class. In higher rank, the proof
constructs the unipotent bijection and applies the cyclic criterion. Every
Sp6(2) case uses Schaeffer Fry's theorem for all odd primes and the stated
cover descent. The deduction for the semisimple identity label uses the same
full H_G class. -/

noncomputable section

namespace ManuscriptIBAW.TypeC.EvenApplicationRouting

open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks
open ModularRep.PaperProofs.EvenFieldProposition39HighRankU0
open ManuscriptIBAW.TypeC.EvenApplication
open ManuscriptIBAW.TypeC.EvenApplicationSp6Two
open ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder
open ModularRep.PaperProofs.EvenFieldProposition39Relative
open ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank
open ModularRep.PaperProofs.EvenFieldProposition39Suzuki
open ModularRep.PaperProofs.EvenFieldProposition39TypeA

/-- The source interpretation of semisimplicity on the specified dual group,
including the semisimple label of each strict block. Principality and block
bijections are separate conclusions. -/
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

/-- The stated assumptions with the Bonnafé statement restricted to its
published semisimple domain. Type A uses the source statement without a
choice of cover on the same actual family. Identifications of the
automorphism actions, relations and classifier indices are fixed, as are the
cover requirements of the other branches. -/
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
          HighRankSource blockSource classification pair parameter
            hcase model block
  splitLowRank : ∀ (parameter : SplitLowRankParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.splitLowRank parameter)),
    SchaefferFrySplitLowRankFamilySource classification pair parameter hcase
      (blockSource.automorphisms pair) (blockSource.source pair)
  sp6Two : ∀ (prime : Sp6PrimeCase),
    classification.structuralCase coverage pair = .typeC (.splitSp6Two prime) →
    Sp6TwoOddSource (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  suzuki : ∀ (parameter : SuzukiParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.simpleSuzuki parameter)),
    SuzukiSource classification pair parameter hcase
      (blockSource.automorphisms pair) (blockSource.source pair)

/-- Apply Bonnafé's theorem to the selected semisimple label after proving that
strict quasi-isolation implies quasi-isolation. -/
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

/-- The exhaustive case distinction for the fixed relations in Definition 3.5.
The case where the prime does not divide the group order is decided by
divisibility. It and the Type A case do not use the semisimple identity
assertion. -/
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
          exact (source.sp6Two prime hcase).blockWitness block
      | simpleSuzuki parameter =>
          exact (source.suzuki parameter hcase).blockWitness
            scope.distinctPrimes block

/-- Obtain the full relative Hypothesis 5.5(b), retaining every represented pair
and strict block with its specified relation. Bonnafé's theorem is used only
on its stated semisimple domain. -/
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

end ManuscriptIBAW.TypeC.EvenApplicationRouting



/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
