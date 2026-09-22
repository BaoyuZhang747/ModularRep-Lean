import ManuscriptIBAW.TypeC.EvenApplicationJoint
import ModularRep.PaperProofs.CurrentFiniteSplittingAssembly
import ModularRep.PaperProofs.TypeCActualCaseSourceData

/-!
The application in even characteristic and higher rank, on the specified
Type C family. The final source combines Koshitani–Späth Definition 3.2 and
Lemma 3.3 with Späth Definition 5.17 and Remark 5.18, in the specified
splitting fields. It uses the complete block witnesses obtained from Jordan
reduction and the strict block argument.
-/
noncomputable section
namespace ManuscriptIBAW.TypeC
open ModularRep ModularRep.PaperProofs
open EvenFieldConcreteTypeC EvenFieldFLZFullHG EvenFieldFLZ57CentrelessGate
open EvenFieldAssumption53Actual EvenFieldFLZBAWGoodFamily
open EvenFieldFLZ57Proposition39AssemblyU0
open EvenFieldFLZ57ChosenRootMetadata TypeCCoherentFiniteRootConvention
open TypeCActualCaseSourceData
open TypeCActualSimpleQuotientCoordinates
open OddTwoConformalProjectiveRealisation (spProjection)
open FDRepSimpleClassKZero
local instance finiteFintype (G : Type) [Finite G] : Fintype G := Fintype.ofFinite G
open TypeBFullBlockCondition TypeBFixedRootDefinitionFamily

variable (n ell : ℕ) (F : Type) [Field F] [Finite F]

/-- The source data for the application in even characteristic and higher rank.
The equation for the field order identifies the Frobenius model with the
requested field. -/
structure HigherEvenApplicationInputs where
  a : ℕ
  positive : 0 < a
  CSpModel : Type
  Fq : Type
  [groupCSp : Group CSpModel]
  [finiteCSp : Finite CSpModel]
  [fieldFq : Field Fq]
  [finiteFq : Finite Fq]
  [charPFq : CharP Fq 2]
  [finiteFixed : Finite (FiniteSymplecticFixed n a)]
  [finiteFieldGroup : Finite (FieldGroup a)]
  [cyclicFieldGroup : IsCyclic (FieldGroup a)]
  scope : FLZFullHGUniverse 2 ell
  coverage : FullHGDefinition35Coverage scope
  model : CentrelessTypeCAmbientModel (r := n) (a := a) scope
  frobenius : AmbientFrobeniusFieldMatch scope model
  fieldCard : Nat.card F = frobenius.sourceFieldSize
  conformal : ConformalStructuralSource n a positive CSpModel Fq
  Label : Type
  context : ManuscriptIBAW.Jordan.GeometricContext
    (ell := ell) (k := (AmbientFamily scope coverage).k) (S := Label)
    (EvenFieldFLZ57CentrelessGate.familyConformalAction scope coverage model conformal)
    (EvenFieldFLZ57CentrelessGate.familyFieldAction scope coverage model positive)
  geometry : ManuscriptIBAW.Jordan.GeometricSelection
    (EvenFieldFLZ57CentrelessGate.familyConformalAction scope coverage model conformal)
    (EvenFieldFLZ57CentrelessGate.familyFieldAction scope coverage model positive) context
  blockSource : FullHGBlockSource coverage
  strictSource : FullHGStrictQuasiIsolationAdapter coverage
  classification : FullHGTypeCClassificationSource scope
  identification : CentrelessTypeCSourceIdentification scope coverage model frobenius
  coherent : ∀ pair : FullHG scope, CoherentPairStrictSourceU0 strictSource pair
  seriesBinding : ManuscriptIBAW.Jordan.SeriesBinding (AmbientFamily scope coverage) context
    ((fullHGStrictSourceAuditU0 coherent).strictModel scope.ambientPair).label
  labels : ∀ pair : FullHG scope, EvenApplicationRouting.SemisimpleLabelSource (coherent pair).strictData
  sources : ∀ pair : FullHG scope,
    EvenApplicationRouting.GuardedPairSourceInputs blockSource strictSource classification pair
      (coherent pair).strictData (labels pair)
  principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
    ell (AmbientFamily scope coverage).k
  semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
    blockSource identification
  convention : Convention ell (AmbientFamily scope coverage).k (AmbientFamily scope coverage).K
  admissible : FamilyRootAdmissibility (AmbientFamily scope coverage) convention
  physical : EvenFieldStrongFLZCompleteApplication.PhysicalInputs
    (AmbientFamily scope coverage) identification.identityEllPrimeCover
    identification.centerless convention
  joint : EvenApplication.JointPerLabelSource positive scope coverage model conformal context
    frobenius blockSource strictSource identification semantics convention admissible
  O : Type
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraOK : Algebra O (AmbientFamily scope coverage).K]
  modularSystem : ModularSystem ell (AmbientFamily scope coverage).K O
    (AmbientFamily scope coverage).k
  /-- For every finite group, the convention uses the correspondence between
  roots of unity of order prime to `ell` induced by the specified modular system. -/
  convention_modularSystem : ∀ (G : Type) [Group G] [Finite G],
    convention.rootAt G = TypeBModularGroupRootBinding.groupRoot modularSystem G
  ordinaryRoots : HasEnoughRootsOfUnity (AmbientFamily scope coverage).K
    (Nat.card (AmbientFamily scope coverage).H)
  coefficient : SpathCoefficientField ell (AmbientFamily scope coverage).k
    (AmbientFamily scope coverage).ellPrime
  ambientPhysical : OddTwoActualLocalBlockSupport.Source (AmbientFamily scope coverage).iota
    (AmbientFamily scope coverage).blockSource.operations
  ks : CurrentFiniteSplittingAssembly.Source

attribute [instance] HigherEvenApplicationInputs.groupCSp HigherEvenApplicationInputs.finiteCSp
  HigherEvenApplicationInputs.fieldFq HigherEvenApplicationInputs.finiteFq HigherEvenApplicationInputs.charPFq
  HigherEvenApplicationInputs.ringO HigherEvenApplicationInputs.domainO HigherEvenApplicationInputs.algebraOK

/-- The ambient root equation follows from admissibility in the same system. -/
theorem HigherEvenApplicationInputs.root (D : HigherEvenApplicationInputs n ell F) :
    (AmbientFamily D.scope D.coverage).iota =
      TypeBModularGroupRootBinding.groupRoot D.modularSystem
        (AmbientFamily D.scope D.coverage).H :=
  D.admissible.ambient_eq.trans (D.convention_modularSystem _)

def HigherEvenApplicationInputs.target (D : HigherEvenApplicationInputs n ell F) : ActualTarget n ell F where
  family := AmbientFamily D.scope D.coverage
  cover := D.identification.identityEllPrimeCover
  simpleEquiv := identityCoverSimpleEquiv D.positive D.scope D.coverage D.model
    D.frobenius F D.fieldCard D.identification

theorem HigherEvenApplicationInputs.complete (D : HigherEvenApplicationInputs n ell F) (rank : 4 ≤ n) :
    Nonempty (FamilyWitness D.target.family D.target.cover) := by
  let := D.finiteFixed
  let := D.finiteFieldGroup
  let := D.cyclicFieldGroup
  exact CurrentFiniteSplittingAssembly.fullFamily
    (AmbientFamily D.scope D.coverage) D.identification.identityEllPrimeCover
    D.modularSystem D.ks D.ordinaryRoots D.root D.coefficient D.physical.sourceAmbient
    (EvenFieldStrongFLZCompleteApplication.ambientGuarded
      (AmbientFamily D.scope D.coverage) D.ambientPhysical)
    (EvenFieldStrongFLZCompleteApplication.selectedRoots
      (AmbientFamily D.scope D.coverage) D.convention D.admissible)
    (EvenApplication.completeBlocks D.positive D.scope D.coverage D.model D.conformal
      D.context D.geometry D.frobenius D.blockSource D.strictSource D.classification rank
      D.identification D.semantics D.coherent D.seriesBinding D.labels D.sources D.principle
      D.convention D.admissible D.joint D.physical)

@[simp] theorem HigherEvenApplicationInputs.projection (D : HigherEvenApplicationInputs n ell F) :
    D.target.projection = (spProjection n F).comp
      (familySpEquiv D.positive D.scope D.coverage D.model D.frobenius F D.fieldCard).toMonoidHom :=
  identityCoverSimpleEquiv_quotient D.positive D.scope D.coverage D.model
    D.frobenius F D.fieldCard D.identification


end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
