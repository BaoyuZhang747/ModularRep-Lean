import ManuscriptIBAW.TypeC.EvenApplicationRouting
import ManuscriptIBAW.Jordan.TypeCEvenLocalized
import ModularRep.PaperProofs.EvenFieldFLZ57Proposition39AssemblyU0

/-! Propositions 3.7–3.8 followed by Jordan reduction for each label. Both
relative hypotheses are proved on the same full H_G class. -/
noncomputable section
namespace ManuscriptIBAW.TypeC.EvenApplication
open ModularRep ModularRep.PaperProofs
open EvenFieldAssumption53Actual EvenFieldConcreteTypeC EvenFieldFLZ57CentrelessGate
open EvenFieldFLZ57Proposition39AssemblyU0 EvenFieldFLZFullHG
open EvenFieldFamilyAssumption53Actual
open ManuscriptIBAW.Jordan
open ManuscriptIBAW.TypeC.EvenApplicationRouting

variable {ell r a : ℕ} {C Fq : Type}
  [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
  (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
  [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
  (scope : FLZFullHGUniverse 2 ell)
  (coverage : FullHGDefinition35Coverage scope)
  (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
  (conformal : ConformalStructuralSource r a ha C Fq)
  {Label : Type}
  (context : GeometricContext (ell := ell) (k := (AmbientFamily scope coverage).k)
    (S := Label) (familyConformalAction scope coverage model conformal)
    (familyFieldAction scope coverage model ha))
  (geometry : GeometricSelection (familyConformalAction scope coverage model conformal)
    (familyFieldAction scope coverage model ha) context)
  (frobenius : AmbientFrobeniusFieldMatch scope model)
  (blockSource : FullHGBlockSource coverage)
  (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
  (classification : FullHGTypeCClassificationSource scope)
  (rankAtLeastFour : 4 ≤ r)
  (identification : CentrelessTypeCSourceIdentification scope coverage model frobenius)
  (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
    blockSource identification)
  (coherent : ∀ pair : FullHG scope, CoherentPairStrictSourceU0 strictSource pair)
  (seriesBinding : SeriesBinding (AmbientFamily scope coverage) context
    ((fullHGStrictSourceAuditU0 coherent).strictModel scope.ambientPair).label)
  (labels : ∀ pair : FullHG scope, SemisimpleLabelSource (coherent pair).strictData)
  (cited : ∀ pair : FullHG scope,
    GuardedPairSourceInputs blockSource strictSource classification pair
      (coherent pair).strictData (labels pair))
  (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
    ell (AmbientFamily scope coverage).k)
  (theorem57 : TypeCEvenLocalized.FLZ57PerLabelMatchedPairSource ha scope coverage
    model conformal context frobenius blockSource strictSource identification semantics)

/-- The target is the specified BAW-good family on its canonical cover with the
fixed relation. Its hypothesis on strict blocks follows from the constructed
bijection, the criterion and the stated sources for covers in small rank. -/
def bawGoodFamily :
    AmbientFLZBAWGoodFamilyWitness scope coverage model frobenius blockSource
      identification semantics :=
  TypeCEvenLocalized.bawGoodFamily ha scope coverage model conformal context geometry
    frobenius blockSource strictSource identification semantics rankAtLeastFour
    (fullHGStrictSourceAuditU0 coherent)
    seriesBinding
    (fullHG_strictBlocks_of_proposition39_semisimple blockSource strictSource classification
      (fun pair => (coherent pair).strictData) labels cited)
    principle theorem57

end ManuscriptIBAW.TypeC.EvenApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
