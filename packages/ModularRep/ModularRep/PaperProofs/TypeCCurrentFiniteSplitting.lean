import ModularRep.PaperProofs.TypeCActualCaseSourceData
import ModularRep.PaperProofs.CurrentFiniteSplittingAssembly
import ModularRep.PaperProofs.TypeCCurrentOddPrimeApplication

/-!
# Current Type C applications with finite splitting coefficients

These application wrappers retain the earlier matrix groups, source deductions,
complete block packets and actual projective symplectic targets. The ordinary
coefficient field splits the specified finite groups in a complete modular system;
it is not required to be algebraically closed. The earlier application records
remain separate historical declarations.

The even-field route reuses the guarded P38 construction, joint FLZ output
and every complete block witness. Only the final published family construction
uses the finite-splitting source. Specified block laws, selected quotient roots,
full automorphism stabilizers and the actual cover remain fixed throughout.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.TypeCCurrentFiniteSplitting
open ModularRep FDRepSimpleClassKZero CharacterWeight
open TypeCActualCaseSourceData
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open OddTwoConformalProjectiveRealisation (Sp PSp CSp spProjection)
open TypeCActualSimpleQuotientCoordinates
local instance finiteFintype (G : Type) [Finite G] : Fintype G := Fintype.ofFinite G

section HigherOdd

open TypeBCriterionHypotheses TypeCConformalActionAdapter TypeCWeightTensorFieldAction
open TypeCOddPrimeConformalCriterionCarriers

variable (n ell : ℕ) (F : Type) [Field F] [Finite F]

/-- Exactly the published Li/criterion caller's existing source spine. -/
structure HigherOddInputs where
  [normal : (SpSubgroup n F).Normal]
  k : Type
  K : Type
  O : Type
  CyclicTarget : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraOK : Algebra O K]
  [charPk : CharP k ell]
  [closedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  [ordinaryRootsAmbient : HasEnoughRootsOfUnity K
    (Nat.card (Ambient (fieldAction n F)))]
  [groupCyclic : Group CyclicTarget]
  [cyclic : IsCyclic CyclicTarget]
  [finiteBlocksM : Fintype (LiteralPrimitiveBlock k (CSp n F))]
  [finiteBlocksG : Fintype (LiteralPrimitiveBlock k (SpSubgroup n F))]
  [finiteTensor : Finite (TensorCharacters (k := k) (SpSubgroup n F))]
  [actionM : MulAction
    (ActingGroup (k := k) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F))
    (LiteralPrimitiveBlock k (CSp n F))]
  [actionG : MulAction (Ambient (fieldAction n F))
    (LiteralPrimitiveBlock k (SpSubgroup n F))]
  iotaM : PrimeRegularRootEmbedding ell k K (CSp n F)
  iotaG : PrimeRegularRootEmbedding ell k K (SpSubgroup n F)
  injectiveM : IrreducibleBrauerCharacterInjectivity iotaM
  injectiveG : IrreducibleBrauerCharacterInjectivity iotaG
  blocks : BlockData (ell := ell) (k := k) (K := K) (SpSubgroup n F)
  reduction : OrdinaryReductionEquiv (k := k) (K := K)
    (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F)
  productFormula : BrauerLinearTensorProductFormula iotaM
  radicalKernel : RadicalKernelLiftInput (p := ell)
    (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) reduction
  other : TypeCCurrentOddPrimeApplication.SourceInputs n F
    (O := O) (CyclicTarget := CyclicTarget)
    iotaM iotaG injectiveM injectiveG blocks reduction productFormula radicalKernel
  criterion : TypeBFullCriterionSplittingSource.Theorem45SplittingCertificate

attribute [instance] HigherOddInputs.fieldk HigherOddInputs.fieldK HigherOddInputs.ringO
  HigherOddInputs.domainO HigherOddInputs.algebraOK HigherOddInputs.charPk
  HigherOddInputs.closedk HigherOddInputs.charZeroK HigherOddInputs.ordinaryRootsAmbient
  HigherOddInputs.groupCyclic HigherOddInputs.cyclic HigherOddInputs.finiteBlocksM
  HigherOddInputs.finiteBlocksG HigherOddInputs.finiteTensor

def HigherOddInputs.target (D : HigherOddInputs n ell F) : ActualTarget n ell F := by
  letI := D.normal
  letI := D.actionM
  letI := D.actionG
  exact
    { family := TypeBFixedRootCriterionFamilySplitting.downstairsFamily (SpSubgroup n F) D.iotaG D.blocks
        D.other.prime D.injectiveG D.other.localReduction
      cover := TypeCOddPrimeSymplecticCover.ellPrimeCover n F
        D.other.prime D.other.odd D.other.coverSource
      simpleEquiv := MulEquiv.refl _ }

theorem HigherOddInputs.complete (D : HigherOddInputs n ell F) :
    Nonempty (FamilyWitness D.target.family D.target.cover) := by
  letI := D.normal
  letI := D.actionM
  letI := D.actionG
  exact TypeCCurrentOddPrimeApplication.full_block_condition_source_instantiated
    n F D.iotaM D.iotaG D.injectiveM D.injectiveG D.blocks D.reduction
    D.productFormula D.radicalKernel D.other D.criterion

@[simp] theorem HigherOddInputs.projection (D : HigherOddInputs n ell F) :
    D.target.projection = TypeCOddPrimeSymplecticCover.projection n F := rfl


end HigherOdd

section HigherEven

open EvenFieldConcreteTypeC EvenFieldFLZFullHG EvenFieldFLZ57CentrelessGate
open EvenFieldAssumption53Actual EvenFieldFLZBAWGoodFamily
open EvenFieldFLZ57Proposition39AssemblyU0 EvenFieldProposition39SemisimpleRouting
open EvenFieldFLZ57ChosenRootMetadata TypeCCoherentFiniteRootConvention

variable (n ell : ℕ) (F : Type) [Field F] [Finite F]

/-- The fixed actual high-even source spine. The one field-cardinality
binding identifies its existing Frobenius model with the requested field. -/
structure HigherEvenInputs where
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
  blockSource : FullHGBlockSource coverage
  strictSource : FullHGStrictQuasiIsolationAdapter coverage
  classification : FullHGTypeCClassificationSource scope
  identification : CentrelessTypeCSourceIdentification scope coverage model frobenius
  coherent : ∀ pair : FullHG scope, CoherentPairStrictSourceU0 strictSource pair
  labels : ∀ pair : FullHG scope, SemisimpleLabelSource (coherent pair).strictData
  playlist : ∀ pair : FullHG scope,
    EvenFieldChosenStrictBlockPlaylist.SourceInputs blockSource strictSource classification pair
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
  joint : JointFLZ57MatchedPairSource positive scope coverage model frobenius conformal
    blockSource strictSource identification semantics convention admissible
  O : Type
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraOK : Algebra O (AmbientFamily scope coverage).K]
  modularSystem : ModularSystem ell (AmbientFamily scope coverage).K O
    (AmbientFamily scope coverage).k
  ordinaryRoots : HasEnoughRootsOfUnity (AmbientFamily scope coverage).K
    (Nat.card (AmbientFamily scope coverage).H)
  root : (AmbientFamily scope coverage).iota =
    TypeBModularGroupRootBinding.groupRoot modularSystem (AmbientFamily scope coverage).H
  coefficient : SpathCoefficientField ell (AmbientFamily scope coverage).k
    (AmbientFamily scope coverage).ellPrime
  ambientPhysical : OddTwoActualLocalBlockSupport.Source (AmbientFamily scope coverage).iota
    (AmbientFamily scope coverage).blockSource.operations
  ks : CurrentFiniteSplittingAssembly.Source

attribute [instance] HigherEvenInputs.groupCSp HigherEvenInputs.finiteCSp
  HigherEvenInputs.fieldFq HigherEvenInputs.finiteFq HigherEvenInputs.charPFq
  HigherEvenInputs.ringO HigherEvenInputs.domainO HigherEvenInputs.algebraOK

def HigherEvenInputs.target (D : HigherEvenInputs n ell F) : ActualTarget n ell F where
  family := AmbientFamily D.scope D.coverage
  cover := D.identification.identityEllPrimeCover
  simpleEquiv := identityCoverSimpleEquiv D.positive D.scope D.coverage D.model
    D.frobenius F D.fieldCard D.identification

theorem HigherEvenInputs.complete (D : HigherEvenInputs n ell F) (rank : 4 ≤ n) :
    Nonempty (FamilyWitness D.target.family D.target.cover) := by
  letI := D.finiteFixed
  letI := D.finiteFieldGroup
  letI := D.cyclicFieldGroup
  exact CurrentFiniteSplittingAssembly.fullFamily
    (AmbientFamily D.scope D.coverage) D.identification.identityEllPrimeCover
    D.modularSystem D.ks D.ordinaryRoots D.root D.coefficient D.physical.sourceAmbient
    (EvenFieldStrongFLZCompleteApplication.ambientGuarded
      (AmbientFamily D.scope D.coverage) D.ambientPhysical)
    (EvenFieldStrongFLZCompleteApplication.selectedRoots
      (AmbientFamily D.scope D.coverage) D.convention D.admissible)
    (EvenFieldStrongFLZCompleteApplication.completeBlocks
      D.positive D.scope D.coverage D.model D.frobenius D.conformal D.blockSource
      D.strictSource D.classification rank D.identification D.coherent D.labels D.playlist
      D.principle D.semantics D.convention D.admissible D.physical D.joint)

@[simp] theorem HigherEvenInputs.projection (D : HigherEvenInputs n ell F) :
    D.target.projection = (spProjection n F).comp
      (familySpEquiv D.positive D.scope D.coverage D.model D.frobenius F D.fieldCard).toMonoidHom :=
  identityCoverSimpleEquiv_quotient D.positive D.scope D.coverage D.model
    D.frobenius F D.fieldCard D.identification


end HigherEven
end ModularRep.PaperProofs.TypeCCurrentFiniteSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
