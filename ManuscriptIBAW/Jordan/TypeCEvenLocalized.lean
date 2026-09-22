import ManuscriptIBAW.Jordan.EmbeddedExtension
import ManuscriptIBAW.Jordan.GeneralGeometry
import ManuscriptIBAW.Jordan.SeriesBinding
import ModularRep.PaperProofs.EvenFieldFamilyAssumption53Actual

/-!
# Jordan reduction for Type C in even characteristic

The construction uses the original full H_G family, root convention, fixed
point group isomorphism and transported regular and field actions. The
published Jordan theorem is applied to the first hypothesis after
restriction has been proved. Interpreting its matched pairs and BAW-good
conclusion remains an explicit source assumption.
-/

noncomputable section

namespace ManuscriptIBAW.Jordan.TypeCEvenLocalized

open ModularRep ModularRep.PaperProofs
open CyclicOuterLemma37Concrete EvenFieldAssumption53Actual EvenFieldConcreteTypeC
open EvenFieldFLZ57CentrelessGate EvenFieldFLZFullHG EvenFieldFamilyAssumption53Actual

variable {ell r a : ℕ} {C Fq : Type}
  [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
  (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
  [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
  (scope : FLZFullHGUniverse 2 ell)
  (coverage : FullHGDefinition35Coverage scope)
  (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
  (conformal : ConformalStructuralSource r a ha C Fq)

/-- Conformal fixation and the cyclic extension theorem give the family data.
Transport of the embedded extension commutes with the inclusion of the base
group and preserves this family's root convention. -/
theorem familyFullHypothesis
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
      ell (AmbientFamily scope coverage).k) :
    letI := canonicalRegularAction
      (familyConformalAction scope coverage model conformal) (AmbientFamily scope coverage).iota
    letI := canonicalFieldAction
      (familyFieldAction scope coverage model ha) (AmbientFamily scope coverage).iota
    FullBrauerHypothesis (D := C) (AmbientFamily scope coverage).iota
      (familyFieldAction scope coverage model ha) := by
  letI := canonicalRegularAction
    (familyConformalAction scope coverage model conformal) (AmbientFamily scope coverage).iota
  letI := canonicalFieldAction
    (familyFieldAction scope coverage model ha) (AmbientFamily scope coverage).iota
  intro psi
  refine ⟨psi, MulAction.mem_orbit_self psi, ?_⟩
  apply fullRepresentative_of_embedded (AmbientFamily scope coverage).iota
    (familyFieldAction scope coverage model ha) psi
  · intro c e
    have fixed : ∀ (d : C) (chi : IBr (AmbientFamily scope coverage).iota), d • chi = chi :=
      fun d chi => family_conformal_fixation ha scope coverage model conformal d chi
    constructor
    · intro h
      exact ⟨fixed c psi, (fixed c _).symm.trans h⟩
    · rintro ⟨_, h⟩
      exact (fixed c _).trans h
  · exact family_fieldExtension ha scope coverage model principle psi

variable {Label : Type}
  (context : GeometricContext (ell := ell) (k := (AmbientFamily scope coverage).k)
    (S := Label) (familyConformalAction scope coverage model conformal)
    (familyFieldAction scope coverage model ha))
  (geometry : GeometricSelection (familyConformalAction scope coverage model conformal)
    (familyFieldAction scope coverage model ha) context)

include geometry in
theorem generalPerLabel
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
      ell (AmbientFamily scope coverage).k) :
    GeneralPerLabelHypothesis (familyConformalAction scope coverage model conformal)
      (familyFieldAction scope coverage model ha) (AmbientFamily scope coverage).iota context :=
  generalPerLabel_of_fullField _ _ _ context geometry
    (familyFullHypothesis ha scope coverage model conformal principle)

variable (frobenius : AmbientFrobeniusFieldMatch scope model)
  (blockSource : FullHGBlockSource coverage)
  (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
  (identification : CentrelessTypeCSourceIdentification scope coverage model frobenius)
  (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
    blockSource identification)

/-- The published theorem (E2) and its interpretation. The geometric choice and
restricted Brauer hypothesis are established before this source is applied. -/
structure FLZ57PerLabelMatchedPairSource : Prop where
  applyTheorem57AndUnpack :
    4 ≤ r →
    GeneralPerLabelHypothesis (familyConformalAction scope coverage model conformal)
      (familyFieldAction scope coverage model ha) (AmbientFamily scope coverage).iota context →
    ∀ strictnessAudit : FullHGStrictSourceAudit scope coverage strictSource,
    SeriesBinding (AmbientFamily scope coverage) context
      (strictnessAudit.strictModel scope.ambientPair).label →
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource →
    (¬ ell ∣ frobenius.sourceFieldSize) →
    Nonempty (FLZ57MatchedPairOutput scope coverage model frobenius
      blockSource identification semantics)

variable (rankAtLeastFour : 4 ≤ r)
  (strictnessAudit : FullHGStrictSourceAudit scope coverage strictSource)
  (seriesBinding : SeriesBinding (AmbientFamily scope coverage) context
    (strictnessAudit.strictModel scope.ambientPair).label)
  (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource)
  (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
    ell (AmbientFamily scope coverage).k)
  (source : FLZ57PerLabelMatchedPairSource ha scope coverage model conformal context
    frobenius blockSource strictSource identification semantics)

include geometry rankAtLeastFour strictnessAudit seriesBinding strictBlocks principle source in
theorem matchedPairOutput :
    Nonempty (FLZ57MatchedPairOutput scope coverage model frobenius
      blockSource identification semantics) :=
  source.applyTheorem57AndUnpack rankAtLeastFour
    (generalPerLabel ha scope coverage model conformal context geometry principle)
    strictnessAudit seriesBinding strictBlocks
    (coefficientPrime_not_dvd_sourceFieldSize scope coverage model frobenius)

include geometry rankAtLeastFour strictnessAudit seriesBinding strictBlocks principle source in
def bawGoodFamily :
    AmbientFLZBAWGoodFamilyWitness scope coverage model frobenius blockSource
      identification semantics :=
  (Classical.choice (matchedPairOutput ha scope coverage model conformal context geometry
    frobenius blockSource strictSource identification semantics rankAtLeastFour
    strictnessAudit seriesBinding strictBlocks principle source)).toBAWGoodFamilyWitness

end ManuscriptIBAW.Jordan.TypeCEvenLocalized

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
