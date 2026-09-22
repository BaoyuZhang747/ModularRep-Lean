import ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate

/-!
# The separate passage from BAW-goodness to Definition 3.5

Feng--Li--Zhang, Theorem 5.7, supplies BAW-goodness.  The fixed source below
represents the cited composite from the published BAW matched-pair condition,
through Späth [2017, Theorem 4.4] as recalled before equation (3.17), and
then through the implication following equation (3.17), to the
modular-character-triple relation in Definition 3.5.  This module keeps that
composite separate from Theorem 5.7.  It does not construct an equation-(3.17)
witness in the kernel.

The BAW-good family used here is the blockwise Section 3.5 family obtained
from the matched-pair output.  Neither that family nor this relation conversion
is a full Spath Definition 4.1 packet.

The passage source owns only the pointwise implication between the two fixed
relations.  It cannot replace the BAW-good equivalence or equivariance data,
and it cannot choose another universal prime-to-`ell` cover.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate

open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- The fixed Definition 3.5 iBAW-bijection family on the sole ambient
presentation. -/
abbrev AmbientDefinition35IBAWFamilyWitness {ell : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (blockSource : FullHGBlockSource coverage) :=
  Definition35IBAWFamilyWitness
    (AmbientFamily scope coverage)
    (fun block ↦ blockSource.automorphisms scope.ambientPair block)
    (fun block ↦ blockSource.source scope.ambientPair block)

/-- The E2 source for the one-way implication from the fixed BAW matched-pair
relation to the fixed Definition 3.5 modular-character-triple relation. -/
structure FLZ57BAWGoodPassageSource
    {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (blockSource : FullHGBlockSource coverage)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius)
    (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification) : Prop where
  relation_implication : ∀
      (block : (AmbientFamily scope coverage).Block)
      (psi : Definition35Brauer ((AmbientFamily scope coverage).problem block))
      (weight : Definition35Weight
        ((AmbientFamily scope coverage).problem block)),
    (semantics.relation block).bawGoodBlockIsomorphic psi weight →
      (blockSource.source scope.ambientPair block).definition35BlockIsomorphic
        psi weight

/-- Reuse the BAW-good equivalence and equivariance data, changing only the
relation proof through the separately supplied one-way passage. -/
def FLZ57BAWGoodPassageSource.toDefinition35Family
    {ell r a : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {model : CentrelessTypeCAmbientModel (r := r) (a := a) scope}
    {frobenius : AmbientFrobeniusFieldMatch scope model}
    {blockSource : FullHGBlockSource coverage}
    {identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius}
    {semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification}
    (passage : FLZ57BAWGoodPassageSource scope coverage model frobenius
      blockSource identification semantics)
    (good : AmbientFLZBAWGoodFamilyWitness scope coverage model frobenius
      blockSource identification semantics) :
    AmbientDefinition35IBAWFamilyWitness scope coverage blockSource where
  blockWitness block :=
    { omega := (good.blockWitness block).omega
      equivariant := (good.blockWitness block).equivariant
      blockIsomorphism := fun psi ↦
        passage.relation_implication block psi
          ((good.blockWitness block).omega psi)
          ((good.blockWitness block).blockIsomorphism psi) }

/-- Pass the explicit matched-pair output through its kernel BAW-good
construction and then through the independently graded Definition 3.5 passage. -/
def FLZ57MatchedPairOutput.toDefinition35Family
    {ell r a : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {model : CentrelessTypeCAmbientModel (r := r) (a := a) scope}
    {frobenius : AmbientFrobeniusFieldMatch scope model}
    {blockSource : FullHGBlockSource coverage}
    {identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius}
    {semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification}
    (output : FLZ57MatchedPairOutput scope coverage model frobenius blockSource
      identification semantics)
    (passage : FLZ57BAWGoodPassageSource scope coverage model frobenius
      blockSource identification semantics) :
    AmbientDefinition35IBAWFamilyWitness scope coverage blockSource :=
  passage.toDefinition35Family output.toBAWGoodFamilyWitness

/-- Map a nonempty fixed-semantics matched-pair output through the separate
BAW-to-Definition-3.5 passage. -/
theorem definition35IBAWFamily_of_matchedPairOutput
    {ell r a : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {model : CentrelessTypeCAmbientModel (r := r) (a := a) scope}
    {frobenius : AmbientFrobeniusFieldMatch scope model}
    {blockSource : FullHGBlockSource coverage}
    {identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius}
    {semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification}
    (passage : FLZ57BAWGoodPassageSource scope coverage model frobenius
      blockSource identification semantics)
    (output : Nonempty (FLZ57MatchedPairOutput scope coverage model frobenius
      blockSource identification semantics)) :
    Nonempty (AmbientDefinition35IBAWFamilyWitness scope coverage blockSource) :=
  Nonempty.map (fun value ↦ value.toDefinition35Family passage) output

end ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
