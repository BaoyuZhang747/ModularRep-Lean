import ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
import ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks

/-!
# Coherent Proposition 3.9 input for the centreless FLZ 5.7 gate

This module performs the missing checked construction between the full-`H_G`
Proposition 3.9 case split and `FLZ57ExplicitHypotheses`.  For each
`pair : FullHG scope`, `CoherentPairStrictSource` stores one and only one
`SourceStrictBlockModel`.  Its `strict_iff` field identifies the already fixed
`strictSource.predicate` with the literal product of the finite and connected
centralisers of that model's label.  Both consumers are then derived from
that same stored model:

* `toPairStrictBlockSource` supplies the centraliser argument used by
  `fullHG_strictBlocks_of_proposition39`;
* `fullHGStrictSourceAudit` supplies the strictness audit required by the
  centreless FLZ 5.7 gate.

Consequently the construction theorem has no independently supplied
`FullHGStrictSourceAudit`, no independently supplied
`FullHGRelativeHypothesis55StrictBlocks`, and no second label, centraliser, or
Levi presentation.  The Proposition 3.9 branch inputs remain the explicit
pair indexed `PairSourceInputs` argument.

This is a coherent source-boundary construction, not a construction of the
source objects themselves.  The exact algebraic-group, Frobenius, ambient
finite group, Assumption 5.3, Definition 3.5, classification, dual-label,
centraliser, and proper-Levi identifications remain explicit E1/U or E2/U
inputs.  The external branch mathematics remains E1/U or E2/U.  In type A it
is no longer one conclusion: the BAW-good theorem source and the fixed
relation passage are separate, while Lean supplies `scope.distinctPrimes`,
converts in K, and projects in L.  No theorem below proves Feng--Li--Zhang
Theorem 5.7, BAW-goodness, or iBAW.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZ57Proposition39Assembly

open scoped Pointwise
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.EvenFieldAssumption53Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks

universe u

/-- One source-shaped strictness presentation for one represented pair.

The literal model is stored once.  The iff is deliberately stronger than
the forward implication consumed by Proposition 3.9: it prevents the
adapter predicate from omitting a block for which the displayed
centraliser-product formula holds. -/
structure CoherentPairStrictSource {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (pair : FullHG scope) where
  strictModel : SourceStrictBlockModel (PairBlock coverage pair)
  finiteCentralizer_le : ∀ s : strictModel.Dual,
    strictModel.finiteCentralizer s ≤ Subgroup.centralizer {s}
  connectedCentralizer_le : ∀ s : strictModel.Dual,
    strictModel.connectedCentralizer s ≤ Subgroup.centralizer {s}
  strict_iff : ∀ block : PairBlock coverage pair,
    strictModel.IsStrict block ↔ strictSource.predicate pair block

/-- Forget only the reverse half of the coherence iff and expose the exact
interface consumed by the checked Proposition 3.9 case split. -/
def CoherentPairStrictSource.toPairStrictBlockSource {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    {pair : FullHG scope}
    (source : CoherentPairStrictSource strictSource pair) :
    PairStrictBlockSource strictSource pair where
  Dual := source.strictModel.Dual
  groupDual := source.strictModel.groupDual
  label := source.strictModel.label
  finiteCentralizer := source.strictModel.finiteCentralizer
  connectedCentralizer := source.strictModel.connectedCentralizer
  IsProperLevi := source.strictModel.IsProperLevi
  finiteCentralizer_le := source.finiteCentralizer_le
  connectedCentralizer_le := source.connectedCentralizer_le
  strictLabel := fun block hstrict ↦ (source.strict_iff block).mpr hstrict

/-- Combine the FLZ strictness audit from the same pair models used by
`toPairStrictBlockSource`. -/
def fullHGStrictSourceAudit {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    (source : ∀ pair : FullHG scope,
      CoherentPairStrictSource strictSource pair) :
    FullHGStrictSourceAudit scope coverage strictSource where
  strictModel := fun pair ↦ (source pair).strictModel
  strict_iff := fun pair block ↦ (source pair).strict_iff block

/-- Derive the second arm of FLZ Hypothesis 5.5 by applying the checked
Proposition 3.9 construction to every represented pair. -/
theorem fullHGStrictBlocks {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (coherent : ∀ pair : FullHG scope,
      CoherentPairStrictSource strictSource pair)
    (cited : ∀ pair : FullHG scope,
      PairSourceInputs blockSource strictSource classification pair
        ((coherent pair).toPairStrictBlockSource)) :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource :=
  fullHG_strictBlocks_of_proposition39 blockSource strictSource classification
    (fun pair ↦ (coherent pair).toPairStrictBlockSource) cited

/-- Build the exact hypothesis package consumed by the centreless FLZ 5.7
gate.

The ambient source identification and Assumption 5.3 transport remain
explicit.  The strictness audit and strict-block arm cannot be supplied by a
caller: Lean constructs both from `coherent`, and constructs the latter by
invoking `fullHG_strictBlocks_of_proposition39` with the eleven cited branch
inputs in `cited`. -/
def flz57ExplicitHypotheses_of_proposition39
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
      CoherentPairStrictSource strictSource pair)
  (cited : ∀ pair : FullHG scope,
      PairSourceInputs blockSource strictSource classification pair
        ((coherent pair).toPairStrictBlockSource)) :
    FLZ57ExplicitHypotheses ha scope coverage model frobenius conformal
      blockSource strictSource identification where
  rankAtLeastFour := rankAtLeastFour
  assumption53 := assumption53
  strictnessAudit := fullHGStrictSourceAudit coherent
  strictBlocks := fullHGStrictBlocks blockSource strictSource classification
    coherent cited

end ModularRep.PaperProofs.EvenFieldFLZ57Proposition39Assembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
