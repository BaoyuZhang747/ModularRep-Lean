import ModularRep.PaperProofs.EvenFieldFLZ57BAWGoodPassage
import ModularRep.PaperProofs.EvenFieldProposition39HighRankU0

/-!
# Universe-zero Proposition 3.9 input for the FLZ 5.7 gate

This module connects the universe-zero Proposition 3.9 dispatcher to the
BAW-good conclusion of Feng--Li--Zhang, Theorem 5.7, and then to the separate
passage from BAW-goodness to Definition 3.5.
For each represented pair, `CoherentPairStrictSourceU0` stores the one
`PairStrictBlockSource` used by the dispatcher and identifies its literal
centraliser formula with the fixed strict-block predicate.  The strictness
audit and the strict-block witness are derived from that same data.

The final theorem keeps one coverage, block source, strict source,
classification, coherent strict-source family, and cited branch family
throughout.  It neither introduces an equation-(3.17) witness nor passes
through the legacy Proposition 3.9 router or construction.
The formal parameter attached to a classified high rank pair is preserved
throughout that branch.  Lean does not identify it with the ambient parameters
`r` and `a` used by the final Theorem 5.7 gate.  That comparison remains part
of the E1/U source match.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZ57Proposition39AssemblyU0

open scoped Pointwise
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.EvenFieldAssumption53Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks
open ModularRep.PaperProofs.EvenFieldProposition39HighRankU0

/-- A single strict-block source for one universe-zero represented pair,
together with the reverse implication needed by the source audit.

The predicate-to-literal implication is already the `strictLabel` field of
`strictData`.  We retain only the missing reverse implication and derive the
equivalence below. -/
structure CoherentPairStrictSourceU0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (pair : FullHG scope) where
  strictData : PairStrictBlockSource strictSource pair
  literalStrict_to_predicate : ∀ block : PairBlock coverage pair,
    NotContainedInProperLevi
      (((strictData.finiteCentralizer (strictData.label block) :
          Set strictData.Dual) *
        (strictData.connectedCentralizer (strictData.label block) :
          Set strictData.Dual)))
      strictData.IsProperLevi →
        strictSource.predicate pair block

/-- View the exact dual labels and centralisers stored in `strictData` as the
literal source model required by the FLZ 5.7 strictness audit. -/
def CoherentPairStrictSourceU0.toSourceStrictBlockModel {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    {pair : FullHG scope}
    (source : CoherentPairStrictSourceU0 strictSource pair) :
    SourceStrictBlockModel (PairBlock coverage pair) where
  Dual := source.strictData.Dual
  groupDual := source.strictData.groupDual
  label := source.strictData.label
  finiteCentralizer := source.strictData.finiteCentralizer
  connectedCentralizer := source.strictData.connectedCentralizer
  IsProperLevi := source.strictData.IsProperLevi

/-- The audit predicate agrees with the literal centraliser condition.  One
direction is already required by the Proposition 3.9 strict-block source. -/
theorem CoherentPairStrictSourceU0.strict_iff {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    {pair : FullHG scope}
    (source : CoherentPairStrictSourceU0 strictSource pair)
    (block : PairBlock coverage pair) :
    (source.toSourceStrictBlockModel).IsStrict block ↔
      strictSource.predicate pair block := by
  constructor
  · intro h
    exact source.literalStrict_to_predicate block h
  · intro h
    exact source.strictData.strictLabel block h

/-- Construct the FLZ strictness audit from the same strict-block sources
that are passed to the universe-zero Proposition 3.9 dispatcher. -/
def fullHGStrictSourceAuditU0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    (coherent : ∀ pair : FullHG scope,
      CoherentPairStrictSourceU0 strictSource pair) :
    FullHGStrictSourceAudit scope coverage strictSource where
  strictModel := fun pair ↦ (coherent pair).toSourceStrictBlockModel
  strict_iff := fun pair block ↦ (coherent pair).strict_iff block

/-- Derive Hypothesis 5.5(b) only through the universe-zero Proposition 3.9
dispatcher, using the strict data fixed by `coherent`. -/
theorem fullHGStrictBlocksU0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (coherent : ∀ pair : FullHG scope,
      CoherentPairStrictSourceU0 strictSource pair)
    (cited : ∀ pair : FullHG scope,
      PairSourceInputsU0 blockSource strictSource classification pair
        (coherent pair).strictData) :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource :=
  fullHG_strictBlocks_of_proposition39_u0 blockSource strictSource
    classification (fun pair ↦ (coherent pair).strictData) cited

/-- Combine the exact Theorem 5.7 hypotheses, with no caller-selected cover,
from one coherent universe-zero Proposition 3.9 source family. -/
def flz57ExplicitHypotheses_of_proposition39_u0
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C]
    [Field Fq] [Finite Fq] [CharP Fq 2]
    (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (conformal : ConformalStructuralSource r a ha C Fq)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (rankAtLeastFour : 4 ≤ r)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius)
    (assumption53 : FamilyAssumption53Transport ha scope coverage model
      conformal)
    (coherent : ∀ pair : FullHG scope,
      CoherentPairStrictSourceU0 strictSource pair)
  (cited : ∀ pair : FullHG scope,
      PairSourceInputsU0 blockSource strictSource classification pair
        (coherent pair).strictData) :
    FLZ57ExplicitHypotheses ha scope coverage model frobenius conformal
      blockSource strictSource identification where
  rankAtLeastFour := rankAtLeastFour
  assumption53 := assumption53
  strictnessAudit := fullHGStrictSourceAuditU0 coherent
  strictBlocks := fullHGStrictBlocksU0 blockSource strictSource classification
    coherent cited

/-- Apply Theorem 5.7 to the hypotheses derived from the universe-zero
Proposition 3.9 source family and expose its fixed-semantics matched-pair
output. -/
theorem matchedPairOutput_of_theorem57_of_proposition39_u0
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C]
    [Field Fq] [Finite Fq] [CharP Fq 2]
    (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (conformal : ConformalStructuralSource r a ha C Fq)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (rankAtLeastFour : 4 ≤ r)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius)
    (assumption53 : FamilyAssumption53Transport ha scope coverage model
      conformal)
    (coherent : ∀ pair : FullHG scope,
      CoherentPairStrictSourceU0 strictSource pair)
    (cited : ∀ pair : FullHG scope,
      PairSourceInputsU0 blockSource strictSource classification pair
        (coherent pair).strictData)
    {semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification}
    (theorem57 : FLZ57MatchedPairSource ha scope coverage model frobenius
      conformal blockSource strictSource identification semantics) :
    Nonempty (FLZ57MatchedPairOutput scope coverage model frobenius blockSource
      identification semantics) :=
  matchedPairOutput_consequence_of_theorem57 ha scope coverage model
    frobenius conformal blockSource strictSource identification theorem57
    (flz57ExplicitHypotheses_of_proposition39_u0 ha scope coverage model
      frobenius conformal blockSource strictSource classification
      rankAtLeastFour identification assumption53 coherent cited)

/-- Compose the fixed-semantics matched-pair output with the separately graded
passage from the BAW matched-pair condition to Definition 3.5. -/
theorem definition35IBAWFamily_of_theorem57_of_proposition39_u0
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C]
    [Field Fq] [Finite Fq] [CharP Fq 2]
    (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (conformal : ConformalStructuralSource r a ha C Fq)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (rankAtLeastFour : 4 ≤ r)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius)
    (assumption53 : FamilyAssumption53Transport ha scope coverage model
      conformal)
    (coherent : ∀ pair : FullHG scope,
      CoherentPairStrictSourceU0 strictSource pair)
    (cited : ∀ pair : FullHG scope,
      PairSourceInputsU0 blockSource strictSource classification pair
        (coherent pair).strictData)
    {semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification}
    (theorem57 : FLZ57MatchedPairSource ha scope coverage model frobenius
      conformal blockSource strictSource identification semantics)
    (passage : FLZ57BAWGoodPassageSource scope coverage model frobenius
      blockSource identification semantics) :
    Nonempty (AmbientDefinition35IBAWFamilyWitness scope coverage blockSource) :=
  definition35IBAWFamily_of_matchedPairOutput passage
    (matchedPairOutput_of_theorem57_of_proposition39_u0 ha scope coverage model
      frobenius conformal blockSource strictSource classification
      rankAtLeastFour identification assumption53 coherent cited theorem57)

end ModularRep.PaperProofs.EvenFieldFLZ57Proposition39AssemblyU0


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
