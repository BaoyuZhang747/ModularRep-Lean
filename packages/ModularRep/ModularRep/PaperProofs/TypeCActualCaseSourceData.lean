import ModularRep.PaperProofs.TypeCActualNumericalCases
import ModularRep.PaperProofs.TypeCActualSimpleQuotientCoordinates
import ModularRep.PaperProofs.TypeCDefiningCharacteristicSourceApplication
import ModularRep.PaperProofs.TypeCLowRankEvenSourceApplication
import ModularRep.PaperProofs.TypeCRankTwoOddNondefiningApplication
import ModularRep.PaperProofs.TypeCSp6TwoSourceApplication
import ModularRep.PaperProofs.TypeCOddPrimeLiSourceApplication
import ModularRep.PaperProofs.TypeCOddTwoCompleteSourceApplication
import ModularRep.PaperProofs.EvenFieldStrongFLZCompleteApplication

/-!
# Source-only data for the actual Type C cases

Every input below packages the existing endpoint's authenticated E1/E2
arguments. The family, cover and actual simple-group coordinate are computed
before the endpoint is invoked. No input field assumes a Brauer-to-weight
map, completed block, complete family witness or branch-result predicate.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCActualCaseSourceData

open ModularRep FDRepSimpleClassKZero CharacterWeight
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open OddTwoConformalProjectiveRealisation (Sp PSp CSp spProjection)
open TypeCActualSimpleQuotientCoordinates

local instance caseFintype (G : Type) [Finite G] : Fintype G := Fintype.ofFinite G

/-- A computed target description, with no witness field. -/
structure ActualTarget (n ell : ℕ) (F : Type) [Field F] where
  family : Definition35Family ell
  cover : EllPrimeCoverSource ell family.H
  simpleEquiv : cover.S ≃* PSp n F

def ActualTarget.projection {n ell : ℕ} {F : Type} [Field F]
    (T : ActualTarget n ell F) : T.family.H →* PSp n F :=
  T.simpleEquiv.toMonoidHom.comp T.cover.quotient

@[simp] theorem ActualTarget.projection_apply {n ell : ℕ} {F : Type} [Field F]
    (T : ActualTarget n ell F) (x : T.family.H) :
    T.projection x = T.simpleEquiv (T.cover.quotient x) := rfl

theorem ActualTarget.projection_surjective {n ell : ℕ} {F : Type} [Field F]
    (T : ActualTarget n ell F) : Function.Surjective T.projection :=
  T.simpleEquiv.surjective.comp T.cover.quotient_surjective

theorem ActualTarget.projection_kernel {n ell : ℕ} {F : Type} [Field F]
    (T : ActualTarget n ell F) : T.projection.ker = Subgroup.center T.family.H := by
  calc
    T.projection.ker = T.cover.quotient.ker := by
      ext x
      change T.simpleEquiv (T.cover.quotient x) = 1 ↔ T.cover.quotient x = 1
      exact T.simpleEquiv.map_eq_one_iff
    _ = Subgroup.center T.family.H := T.cover.quotient_kernel

/-- The existing standard primitive-family input spine, shared verbatim by
the defining, low-rank and exceptional published endpoints. -/
structure PrimitiveData (ell : ℕ) (G : Type) [Group G] [Fintype G]
    (prime : Nat.Prime ell) where
  k : Type
  K : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [charPk : CharP k ell]
  [closedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  [finiteBlocks : Fintype (LiteralPrimitiveBlock k G)]
  iota : PrimeRegularRootEmbedding ell k K G
  injective : IrreducibleBrauerCharacterInjectivity iota
  blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.1)
  localSource : PrimitiveLocalSource iota
  coefficient : SpathCoefficientField ell k prime

attribute [instance] PrimitiveData.fieldk PrimitiveData.fieldK PrimitiveData.charPk
  PrimitiveData.closedk PrimitiveData.charZeroK PrimitiveData.finiteBlocks

def PrimitiveData.family {ell : ℕ} {G : Type} [Group G] [Fintype G]
    {prime : Nat.Prime ell} (D : PrimitiveData ell G prime) : Definition35Family ell :=
  primitiveFamily D.iota D.injective D.blocks prime D.localSource

section Defining

variable (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]

structure DefiningInputs where
  primitive : PrimitiveData p (Sp n F) (TypeCActualNumericalCases.characteristic_prime F p)
  facts : TypeCDefiningCharacteristicSourceApplication.CoverFacts p n F
  source : TypeCDefiningCharacteristicSourceApplication.TheoremCCertificate

def DefiningInputs.target (D : DefiningInputs n p F) : ActualTarget n p F where
  family := D.primitive.family
  cover := TypeCDefiningCharacteristicSourceApplication.actualCover p n F D.facts
  simpleEquiv := MulEquiv.refl _

theorem DefiningInputs.complete (D : DefiningInputs n p F) :
    Nonempty (FamilyWitness D.target.family D.target.cover) :=
  TypeCDefiningCharacteristicSourceApplication.full_block_condition_source_instantiated
    p n F D.primitive.k D.primitive.K D.facts D.primitive.iota D.primitive.injective
    D.primitive.blocks D.primitive.localSource D.primitive.coefficient D.source

@[simp] theorem DefiningInputs.projection (D : DefiningInputs n p F) :
    D.target.projection = spProjection n F := rfl

end Defining

section LowEven

variable (n ell : ℕ) (F : Type) [Field F] [Finite F] [charTwo : CharP F 2]
variable (prime : Nat.Prime ell)

structure LowEvenInputs where
  primitive : PrimitiveData ell (Sp n F) prime
  facts : TypeCLowRankEvenSourceApplication.CentrelessOwnCoverFacts n F
  source : TypeCLowRankEvenSourceApplication.Theorem55Certificate

def LowEvenInputs.target (D : LowEvenInputs n ell F prime) : ActualTarget n ell F where
  family := D.primitive.family
  cover := TypeCLowRankEvenSourceApplication.actualCover n F D.facts ell prime
  simpleEquiv := MulEquiv.refl _

include charTwo in
theorem LowEvenInputs.complete (D : LowEvenInputs n ell F prime)
    (rank : n = 2 ∨ n = 3) (large : 2 < Nat.card F) (nondefining : ell ≠ 2) :
    Nonempty (FamilyWitness D.target.family D.target.cover) :=
  TypeCLowRankEvenSourceApplication.full_block_condition_source_instantiated
    ell n F D.primitive.k D.primitive.K prime D.facts D.primitive.iota
    D.primitive.injective D.primitive.blocks D.primitive.localSource
    D.primitive.coefficient rank large nondefining D.source

@[simp] theorem LowEvenInputs.projection (D : LowEvenInputs n ell F prime) :
    D.target.projection = spProjection n F := rfl

end LowEven

section RankTwoOdd

variable (ell : ℕ) (F : Type) [Field F] [Finite F]
variable (prime : Nat.Prime ell)

structure RankTwoOddInputs where
  primitive : PrimitiveData ell (Sp 2 F) prime
  coverSource : OddTwoUniversalPrimeToTwoSelfCover.OddSymplecticFullCoverSource 2 F
  perfect : commutator (Sp 2 F) = ⊤
  structural : TypeCRankTwoCyclicSourceApplication.OrderAndTorusSource F
  oddDivisorSource : TypeCRankTwoOddSourceApplication.Theorem11Certificate
  cyclicSource : TypeBCyclicDefectSource.CyclicDefectCertificate

def RankTwoOddInputs.target (D : RankTwoOddInputs ell F prime)
    (nondefiningTwo : ell ≠ 2) : ActualTarget 2 ell F where
  family := D.primitive.family
  cover := TypeCRankTwoOddSourceApplication.actualCover F D.coverSource D.perfect
    ell prime nondefiningTwo
  simpleEquiv := MulEquiv.refl _

theorem RankTwoOddInputs.complete (D : RankTwoOddInputs ell F prime)
    (nondefiningTwo : ell ≠ 2)
    (divides : ell ∣ Nat.card (PSp 2 F)) (nondefining : ¬ ell ∣ Nat.card F) :
    Nonempty (FamilyWitness (RankTwoOddInputs.target ell F prime D nondefiningTwo).family
      (RankTwoOddInputs.target ell F prime D nondefiningTwo).cover) :=
  TypeCRankTwoOddNondefiningApplication.full_block_condition_source_instantiated
    ell F D.primitive.k D.primitive.K prime nondefiningTwo D.coverSource D.perfect
    D.structural D.primitive.iota D.primitive.injective D.primitive.blocks
    D.primitive.localSource D.primitive.coefficient divides nondefining
    D.oddDivisorSource D.cyclicSource

@[simp] theorem RankTwoOddInputs.projection (D : RankTwoOddInputs ell F prime)
    (nondefiningTwo : ell ≠ 2) :
    (RankTwoOddInputs.target ell F prime D nondefiningTwo).projection = spProjection 2 F := rfl

end RankTwoOdd

section Exceptional

variable (ell : ℕ) (prime : Nat.Prime ell)

/-- U and its full-cover projection are fixed inputs, never replaced by Sp. -/
structure Sp6TwoInputs where
  U : Type
  [groupU : Group U]
  [finiteU : Fintype U]
  projection : U →* TypeCSp6TwoSourceApplication.SimpleGroup
  facts : TypeCSp6TwoSourceApplication.FullCoverSource U projection
  primitive : PrimitiveData ell U prime
  threeSource : TypeCSp6TwoSourceApplication.Theorem55Sp6TwoCertificate
  cyclicSource : TypeBCyclicDefectSource.CyclicDefectCertificate

attribute [instance] Sp6TwoInputs.groupU Sp6TwoInputs.finiteU

def Sp6TwoInputs.target (D : Sp6TwoInputs ell prime)
    (F : Type) [Field F] [Finite F] (nondefiningTwo : ell ≠ 2)
    (fieldTwo : Nat.card F = 2) :
    ActualTarget 3 ell F where
  family := D.primitive.family
  cover := TypeCSp6TwoSourceApplication.actualCover D.U D.projection D.facts
    ell prime nondefiningTwo
  simpleEquiv := (twoElementProjectiveEquiv F fieldTwo 3).symm

theorem Sp6TwoInputs.complete (D : Sp6TwoInputs ell prime)
    (F : Type) [Field F] [Finite F] (nondefiningTwo : ell ≠ 2) (fieldTwo : Nat.card F = 2)
    (divides : ell ∣ Nat.card (PSp 3 F)) :
    Nonempty (FamilyWitness (Sp6TwoInputs.target ell prime D F nondefiningTwo fieldTwo).family
      (Sp6TwoInputs.target ell prime D F nondefiningTwo fieldTwo).cover) :=
  TypeCSp6TwoSourceApplication.full_block_condition_source_instantiated
    ell D.U D.primitive.k D.primitive.K prime nondefiningTwo D.projection D.facts
    D.primitive.iota D.primitive.injective D.primitive.blocks D.primitive.localSource
    D.primitive.coefficient ((twoElementProjective_dvd_iff F fieldTwo 3 ell).mp divides)
    D.threeSource D.cyclicSource

@[simp] theorem Sp6TwoInputs.projection_eq (D : Sp6TwoInputs ell prime)
    (F : Type) [Field F] [Finite F] (nondefiningTwo : ell ≠ 2) (fieldTwo : Nat.card F = 2) :
    (Sp6TwoInputs.target ell prime D F nondefiningTwo fieldTwo).projection =
      projectionOverTwoElementField F fieldTwo D.projection := rfl

end Exceptional

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
  [closedK : IsAlgClosed K]
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
  other : TypeCOddPrimeLiSourceApplication.OtherInputs n F
    (O := O) (CyclicTarget := CyclicTarget)
    iotaM iotaG injectiveM injectiveG blocks reduction productFormula radicalKernel
  li : TypeCOddPrimeLiSourceApplication.Li55Certificate
  criterion : TypeBBroughSpathCriterionSource.Theorem45Certificate

attribute [instance] HigherOddInputs.fieldk HigherOddInputs.fieldK HigherOddInputs.ringO
  HigherOddInputs.domainO HigherOddInputs.algebraOK HigherOddInputs.charPk
  HigherOddInputs.closedk HigherOddInputs.charZeroK HigherOddInputs.closedK
  HigherOddInputs.groupCyclic HigherOddInputs.cyclic HigherOddInputs.finiteBlocksM
  HigherOddInputs.finiteBlocksG HigherOddInputs.finiteTensor

def HigherOddInputs.target (D : HigherOddInputs n ell F) : ActualTarget n ell F := by
  letI := D.normal
  letI := D.actionM
  letI := D.actionG
  exact
    { family := downstairsFamily (SpSubgroup n F) D.iotaG D.blocks
        D.other.prime D.injectiveG D.other.localReduction
      cover := TypeCOddPrimeSymplecticCover.ellPrimeCover n F
        D.other.prime D.other.odd D.other.coverSource
      simpleEquiv := MulEquiv.refl _ }

theorem HigherOddInputs.complete (D : HigherOddInputs n ell F) :
    Nonempty (FamilyWitness D.target.family D.target.cover) := by
  letI := D.normal
  letI := D.actionM
  letI := D.actionG
  exact TypeCOddPrimeLiSourceApplication.full_block_condition_source_instantiated
    n F D.iotaM D.iotaG D.injectiveM D.injectiveG D.blocks D.reduction
    D.productFormula D.radicalKernel D.other D.li D.criterion

@[simp] theorem HigherOddInputs.projection (D : HigherOddInputs n ell F) :
    D.target.projection = TypeCOddPrimeSymplecticCover.projection n F := rfl

end HigherOdd

section OddTwo

open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZFullHG OddTwoFullHGPrincipalRouting OddTwoTypeASourceJoin
open OddTwoFLZ57LiteralMapSource OddTwoProjectiveAutomorphismDiagonalJoin
open OddTwoConformalProjectiveRealisation
open OddTwoUniversalPrimeToTwoSelfCover OddTwoFinalBlockOrbitCentralCoverDescentWindow
open OddTwoDefinition35GlobalAssembly OddTwoFengMalleForwardSourceJoin
open OddTwoFullHGPrincipalApplication TypeCCoherentFiniteRootConvention
open TypeCOddTwoCoherentTargetData TypeCOddTwoChosenRootMetadata
open TypeCOddTwoCoherentFamilyApplication TypeCOddTwoCanonicalPrimitiveFamily

variable (n pDef : ℕ) (F : Type) [Field F] [Finite F] [CharP F pDef]

/-- The complete existing odd-two source call, with its Sp map computed by
the predecessor rather than an input field. -/
structure OddTwoInputs where
  scope : FLZFullHGUniverse pDef 2
  coverage : FullHGDefinition35Coverage scope
  strictSource : FullHGStrictQuasiIsolationAdapter coverage
  routing : FullHGPrincipalRoutingSource coverage strictSource
  blockSource : FullHGBlockSource coverage
  interpretation : FullHGInterpretation scope coverage blockSource strictSource
  sources : PrincipalSourcePlaylist routing blockSource interpretation
  typeA : ∀ (pair : FullHG scope)
    (presentation : TypeAActualPresentation pDef (routing.pairSource pair).rank
      (coverage.presentation pair).family.H),
    TypeAApplicationData (coverage.presentation pair).family presentation
      (blockSource.automorphisms pair) (blockSource.source pair)
  center : OddTwoConformalProjectiveRealisation.CenterIntersectionSource n F
  brough : BroughGroupSource center
  cover : OddSymplecticFullCoverSource n F
  lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F)
  problem : LiteralFengMalleProblem n F
  support : OperationsBrauerSupport problem.iota problem.irreducibleBrauerInjective
    problem.blockSource.operations
  reduction : ∀ (b : LiteralBlock problem)
      (w : LiteralWeightFibre problem.blockSource b),
    SelectedLocalReductionSource problem.blockSource b w
  binding : AmbientBinding problem support reduction scope coverage
  input : InputSemantics problem
  coordinates : RegularActionCoordinates brough cover lifting
  assumptionSource : FLZRemark54Source brough cover lifting problem
  theoremSource : FLZTheorem57MapSource brough cover lifting problem support reduction
    scope coverage blockSource strictSource
  diagonal : LiteralDiagonalFieldRealisation n F
  convention : Convention 2 problem.k problem.K
  targetData : CanonicalTargetData problem convention
  admissible : problem.iota = convention.rootAt
    (OddTwoFinalBlockOrbitCentralCoverDescentWindow.LiteralSp n F)
  physical : PhysicalInputs (targetData.targetData admissible).toProblem
  joint : JointFengMalleProposition34Source problem diagonal convention targetData admissible
  cor46 : LiteralFengMalleCorollary46Certificate problem diagonal

def OddTwoInputs.target (D : OddTwoInputs n pDef F) : ActualTarget n 2 F where
  family := canonicalFamily (D.targetData.targetData D.admissible).toProblem
    D.convention rfl (fun _ _ => rfl) D.targetData.support
  cover := canonicalCover (D.targetData.targetData D.admissible).toProblem
    D.convention rfl (fun _ _ => rfl) D.targetData.support
  simpleEquiv := MulEquiv.refl _

theorem OddTwoInputs.complete (D : OddTwoInputs n pDef F) :
    Nonempty (FamilyWitness D.target.family D.target.cover) :=
  TypeCOddTwoCompleteSourceApplication.full_block_condition_source_instantiated
    D.routing D.blockSource D.interpretation D.sources D.typeA D.brough D.cover D.lifting
    D.problem D.support D.reduction D.binding D.input D.coordinates D.assumptionSource
    D.theoremSource D.diagonal D.convention D.targetData D.admissible D.physical D.joint D.cor46

@[simp] theorem OddTwoInputs.projection (D : OddTwoInputs n pDef F) :
    D.target.projection = MonoidHom.id (PSp n F) := rfl

end OddTwo

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
  splitting : IsAlgClosed (AmbientFamily scope coverage).K
  coefficient : SpathCoefficientField ell (AmbientFamily scope coverage).k
    (AmbientFamily scope coverage).ellPrime
  ambientPhysical : OddTwoActualLocalBlockSupport.Source (AmbientFamily scope coverage).iota
    (AmbientFamily scope coverage).blockSource.operations
  ks : TypeCKoshitaniSpathFamilySource.Source.{0}

attribute [instance] HigherEvenInputs.groupCSp HigherEvenInputs.finiteCSp
  HigherEvenInputs.fieldFq HigherEvenInputs.finiteFq HigherEvenInputs.charPFq

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
  exact ⟨EvenFieldStrongFLZCompleteApplication.familyWitness
    D.positive D.scope D.coverage D.model D.frobenius D.conformal D.blockSource
    D.strictSource D.classification rank D.identification D.coherent D.labels D.playlist
    D.principle D.semantics D.convention D.admissible D.physical D.joint
    D.splitting D.coefficient D.ambientPhysical D.ks⟩

@[simp] theorem HigherEvenInputs.projection (D : HigherEvenInputs n ell F) :
    D.target.projection = (spProjection n F).comp
      (familySpEquiv D.positive D.scope D.coverage D.model D.frobenius F D.fieldCard).toMonoidHom :=
  identityCoverSimpleEquiv_quotient D.positive D.scope D.coverage D.model
    D.frobenius F D.fieldCard D.identification

end HigherEven

end ModularRep.PaperProofs.TypeCActualCaseSourceData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
