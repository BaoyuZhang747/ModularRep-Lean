import ModularRep.PaperProofs.EvenFieldFamilyAssumption53Actual
import ModularRep.PaperProofs.EvenFieldProposition39SemisimpleRouting
import ModularRep.PaperProofs.EvenFieldFLZ57Proposition39AssemblyU0

/-!
# Guarded Proposition 3.9 inputs with the stronger FLZ 5.7 output

Construct the existing explicit hypothesis packet from the computed family
Assumption 5.3 and the accepted semisimple-guarded full-HG router. The old
unguarded Bonnafe input and its construction are never constructed or invoked.
The old construction import is used only for its coherent strict-source model
and the K audit obtained from that same data.

The existing exact FLZ 5.7 source then returns its matched-pair output on the
canonical identity prime-to-ell cover. Its SAME certificate supplies the
BAW-good family. No weaker Definition 3.5 family is used backwards.

The authentic interpretations of full-HG and the branch sources remain
required. In particular this module does not authenticate the old high-rank
free carrier equivalences or relation implication. That own-pair/action/root
application join and the independent complete-target passage remain pending.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZ57SemisimpleApplication

open ModularRep
open ModularRep.PaperProofs.EvenFieldAssumption53Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
open ModularRep.PaperProofs.EvenFieldFLZ57Proposition39AssemblyU0
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFamilyAssumption53Actual
open ModularRep.PaperProofs.EvenFieldProposition39SemisimpleRouting

variable {ell r a : ℕ} {C Fq : Type}
variable [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
variable (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
variable [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
variable (scope : FLZFullHGUniverse 2 ell)
variable (coverage : FullHGDefinition35Coverage scope)
variable (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
variable (frobenius : AmbientFrobeniusFieldMatch scope model)
variable (conformal : ConformalStructuralSource r a ha C Fq)
variable (blockSource : FullHGBlockSource coverage)
variable (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
variable (classification : FullHGTypeCClassificationSource scope)
variable (rankAtLeastFour : 4 ≤ r)
variable (identification : CentrelessTypeCSourceIdentification scope coverage model frobenius)
variable (coherent : ∀ pair : FullHG scope, CoherentPairStrictSourceU0 strictSource pair)
variable (labels : ∀ pair : FullHG scope, SemisimpleLabelSource (coherent pair).strictData)
variable (cited : ∀ pair : FullHG scope,
  GuardedPairSourceInputs blockSource strictSource classification pair
    (coherent pair).strictData (labels pair))
variable (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
  ell (AmbientFamily scope coverage).k)

/-- Both arms of Hypothesis 5.5 are supplied by their actual consumers:
computed family Assumption 5.3 and the selected-semisimple-label router. -/
def explicitHypotheses :
    FLZ57ExplicitHypotheses ha scope coverage model frobenius conformal
      blockSource strictSource identification where
  rankAtLeastFour := rankAtLeastFour
  assumption53 := familyAssumption53Transport ha scope coverage model conformal principle
  strictnessAudit := fullHGStrictSourceAuditU0 coherent
  strictBlocks := fullHG_strictBlocks_of_proposition39_semisimple
    blockSource strictSource classification (fun pair => (coherent pair).strictData)
    labels cited

variable {semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
  blockSource identification}
variable (theorem57 : FLZ57MatchedPairSource ha scope coverage model frobenius
  conformal blockSource strictSource identification semantics)

include classification rankAtLeastFour coherent labels cited principle theorem57 in
/-- Apply the named FLZ theorem to the constructed explicit packet. Keep
its stronger matched-pair certificate and fixed BAW relation together. -/
theorem matchedPairOutput :
    Nonempty (FLZ57MatchedPairOutput scope coverage model frobenius
      blockSource identification semantics) :=
  matchedPairOutput_consequence_of_theorem57 ha scope coverage model frobenius
    conformal blockSource strictSource identification theorem57
    (explicitHypotheses ha scope coverage model frobenius conformal blockSource
      strictSource classification rankAtLeastFour identification coherent labels
      cited principle)

/-- Use the SAME selected matched-pair certificate to construct the
stronger BAW-good family, retaining its canonical cover and source relation. -/
def bawGoodFamily :
    AmbientFLZBAWGoodFamilyWitness scope coverage model frobenius blockSource
      identification semantics :=
  (Classical.choice (matchedPairOutput ha scope coverage model frobenius
    conformal blockSource strictSource classification rankAtLeastFour identification
    coherent labels cited principle theorem57)).toBAWGoodFamilyWitness

end ModularRep.PaperProofs.EvenFieldFLZ57SemisimpleApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
