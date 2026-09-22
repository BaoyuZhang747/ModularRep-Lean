import ManuscriptIBAW.TypeC.EvenApplication
import ModularRep.PaperProofs.EvenFieldFLZ57ChosenRootMetadata
import ModularRep.PaperProofs.EvenFieldStrongFLZCompleteApplication

/-! Choose the output of Feng–Li–Zhang for each label together with its
coefficient fields and root convention. These same choices are used to
obtain the complete block witnesses. -/
noncomputable section
namespace ManuscriptIBAW.TypeC.EvenApplication
open ModularRep ModularRep.PaperProofs
open EvenFieldAssumption53Actual EvenFieldConcreteTypeC EvenFieldFLZ57CentrelessGate
open EvenFieldFLZ57Proposition39AssemblyU0 EvenFieldFLZFullHG
open EvenFieldFamilyAssumption53Actual EvenFieldFLZ57ChosenRootMetadata
open TypeCCoherentFiniteRootConvention
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

  (convention : Convention ell (AmbientFamily scope coverage).k (AmbientFamily scope coverage).K)
  (admissible : FamilyRootAdmissibility (AmbientFamily scope coverage) convention)

/-- The output of Feng–Li–Zhang, Theorem 5.7 (E2), and its interpretation in one
specified standard modular system. The hypothesis for each label is
established first. The coefficient and root equations concern the same
chosen output. -/
structure JointPerLabelSource
    (admissible : FamilyRootAdmissibility (AmbientFamily scope coverage) convention) : Prop where
  applyTheorem57AndUnpack :
    4 ≤ r →
    GeneralPerLabelHypothesis (familyConformalAction scope coverage model conformal)
      (familyFieldAction scope coverage model ha) (AmbientFamily scope coverage).iota context →
    ∀ strictnessAudit : FullHGStrictSourceAudit scope coverage strictSource,
    SeriesBinding (AmbientFamily scope coverage) context
      (strictnessAudit.strictModel scope.ambientPair).label →
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource →
    (¬ ell ∣ frobenius.sourceFieldSize) →
    Nonempty {output : FLZ57MatchedPairOutput scope coverage model frobenius
        blockSource identification semantics //
      ChosenRootMetadata scope coverage model frobenius blockSource identification
        semantics convention output}

variable (joint : JointPerLabelSource ha scope coverage model conformal context frobenius
  blockSource strictSource identification semantics convention admissible)

/-- After proving both hypotheses on the full class, choose the data supplied by
the theorem. -/
def chosenOutput :
    {output : FLZ57MatchedPairOutput scope coverage model frobenius blockSource
        identification semantics //
      ChosenRootMetadata scope coverage model frobenius blockSource identification
        semantics convention output} :=
  Classical.choice (joint.applyTheorem57AndUnpack rankAtLeastFour
    (TypeCEvenLocalized.generalPerLabel ha scope coverage model conformal context geometry principle)
    (fullHGStrictSourceAuditU0 coherent)
    seriesBinding
    (fullHG_strictBlocks_of_proposition39_semisimple blockSource strictSource classification
      (fun pair => (coherent pair).strictData) labels cited)
    (coefficientPrime_not_dvd_sourceFieldSize scope coverage model frobenius))

include ha conformal context geometry blockSource strictSource classification
  rankAtLeastFour semantics coherent seriesBinding labels cited principle admissible joint in
/-- Obtain the complete block data from the chosen theorem conclusion and the
same scalar data, using the conversion proved above. -/
theorem completeBlocks
    (physical : EvenFieldStrongFLZCompleteApplication.PhysicalInputs
      (AmbientFamily scope coverage) identification.identityEllPrimeCover
      identification.centerless convention) :
    ∀ b : (AmbientFamily scope coverage).Block,
      Nonempty (TypeBFullBlockCondition.BlockWitness (AmbientFamily scope coverage)
        identification.identityEllPrimeCover b) :=
  EvenFieldStrongFLZCompleteApplication.allBlocks scope coverage model frobenius blockSource
    identification semantics convention admissible
    (chosenOutput ha scope coverage model conformal context geometry frobenius blockSource
      strictSource classification rankAtLeastFour identification semantics coherent seriesBinding labels
      cited principle convention admissible joint) physical

end ManuscriptIBAW.TypeC.EvenApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
