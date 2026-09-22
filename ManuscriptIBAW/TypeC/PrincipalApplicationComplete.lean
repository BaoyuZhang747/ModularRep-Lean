import ManuscriptIBAW.TypeC.PrincipalApplication
import ModularRep.PaperProofs.TypeCActualCaseSourceData

/-!
# The complete principal application on the canonical family

The principal parameter construction and the Jordan theorem for each label
give the symplectic correspondence. The joint Feng–Malle construction then
chooses an original PSp witness together with the root convention of its
extension characters. Transport to the canonical family preserves the cover,
primitive blocks and selected quotient characters.

The joint published construction supplies a witness and its compatible root
convention together. This is stronger than the bare existence of an original
witness, and its coefficient interpretation remains an explicit source
hypothesis.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
open ModularRep.PaperProofs.OddTwoDefinition35GlobalAssembly
open ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin
open ModularRep.PaperProofs.TypeCCoherentFiniteRootConvention
open ModularRep.PaperProofs.TypeCOddTwoCoherentTargetData
open ModularRep.PaperProofs.TypeCOddTwoChosenRootMetadata
open ModularRep.PaperProofs.TypeCOddTwoCoherentFamilyApplication
open ModularRep.PaperProofs.TypeCOddTwoCanonicalPrimitiveFamily
open ModularRep.PaperProofs.TypeBFullBlockCondition
open ModularRep.PaperProofs.TypeCActualCaseSourceData (ActualTarget)
open ManuscriptIBAW.Jordan

variable (n pDef : ℕ) (F : Type) [Field F] [Finite F] [CharP F pDef]

local instance completeApplicationFintype (G : Type) [Finite G] : Fintype G :=
  Fintype.ofFinite G

local instance completeApplicationFieldAutomorphismFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective

/-- Source data in odd characteristic at the prime two, in rank at least three.
The principal correspondence and the restriction for each label are proved
from these assumptions. All target roots and block operations precede the
joint published choice of the original PSp witness. -/
structure OddTwoApplicationInputs where
  rank_ge_three : 3 ≤ n
  scope : FLZFullHGUniverse pDef 2
  coverage : FullHGDefinition35Coverage scope
  strictSource : FullHGStrictQuasiIsolationAdapter coverage
  routing : FullHGPrincipalRoutingSource coverage strictSource
  blockSource : FullHGBlockSource coverage
  interpretation : FullHGInterpretation scope coverage blockSource strictSource
  sources : PrincipalApplicationFamilySource routing blockSource interpretation
  typeA : ∀ (pair : FullHG scope)
    (presentation : TypeAActualPresentation pDef (routing.pairSource pair).rank
      (coverage.presentation pair).family.H),
    TypeAApplicationData (coverage.presentation pair).family presentation
      (blockSource.automorphisms pair) (blockSource.source pair)
  center : CenterIntersectionSource n F
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
  Label : Type
  context : GeometricContext (ell := 2) (k := problem.k) (S := Label)
    ((regularAction brough cover lifting).comp SemidirectProduct.inl)
    (spFieldAction (n := n) (F := F))
  geometry : GeometricSelection
    ((regularAction brough cover lifting).comp SemidirectProduct.inl)
    (spFieldAction (n := n) (F := F)) context
  theoremSource : TypeCOddLocalized.FLZ57PerLabelMapSource brough cover lifting
    problem support reduction scope coverage blockSource strictSource context
  series : TypeCOddLocalized.AmbientSeriesBinding brough cover lifting
    problem support reduction scope coverage blockSource strictSource context
    binding interpretation
  diagonal : LiteralDiagonalFieldRealisation n F
  convention : Convention 2 problem.k problem.K
  targetData : CanonicalTargetData problem convention
  admissible : problem.iota = convention.rootAt
    (ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow.LiteralSp n F)
  physical : PhysicalInputs (targetData.targetData admissible).toProblem
  joint : JointFengMalleProposition34Source problem diagonal convention targetData admissible
  cor46 : LiteralFengMalleCorollary46Certificate problem diagonal

namespace OddTwoApplicationInputs

variable {n pDef F} (D : OddTwoApplicationInputs n pDef F)

/-- The target is formed before the principal or global map is evaluated. -/
def target : ActualTarget n 2 F where
  family := canonicalFamily (D.targetData.targetData D.admissible).toProblem
    D.convention rfl (fun _ _ => rfl) D.targetData.support
  cover := canonicalCover (D.targetData.targetData D.admissible).toProblem
    D.convention rfl (fun _ _ => rfl) D.targetData.support
  simpleEquiv := MulEquiv.refl _

/-- The complete witness uses the constructed Sp map, the same joint source and
root convention, and the specified interpretations of quotient groups and
characters. -/
def familyWitness : FamilyWitness D.target.family D.target.cover :=
  canonicalFamilyWitnessFromFengMalle D.problem D.diagonal D.convention D.targetData
    D.admissible D.physical D.joint D.input
    (principalApplicationGlobalMap D.routing D.blockSource D.interpretation D.sources
      D.typeA D.brough D.cover D.lifting D.problem D.support D.reduction D.binding
      D.input D.coordinates D.assumptionSource D.context D.geometry D.theoremSource D.series)
    D.cor46

omit [CharP F pDef] in
/-- Conditional complete output on the specified family and cover. -/
theorem complete : Nonempty (FamilyWitness D.target.family D.target.cover) :=
  ⟨D.familyWitness⟩

omit [CharP F pDef] in
@[simp] theorem projection :
    D.target.projection = MonoidHom.id (PSp n F) := rfl

end OddTwoApplicationInputs

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
