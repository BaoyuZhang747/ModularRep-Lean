import ModularRep.PaperProofs.OddTwoFullHGPrincipalApplication
import ModularRep.PaperProofs.TypeCOddTwoCanonicalPrimitiveFamily

/-!
# Complete canonical odd-two output from the actual Full-HG source application

The Sp correspondence is computed by the accepted principal/Jordan/FLZ
application. It then enters the exact joint Feng--Malle choice in one modular
system, followed by the constructed original and canonical family witnesses.
No correspondence, completed seed, strict-block packet or complete witness is
an external input. Existing authenticated E1/E2 source arguments stay explicit.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoCompleteSourceApplication

open ModularRep CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZFullHG
open OddTwoFullHGPrincipalRouting OddTwoTypeASourceJoin
open OddTwoFLZ57LiteralMapSource OddTwoConformalProjectiveRealisation
open OddTwoProjectiveAutomorphismDiagonalJoin OddTwoUniversalPrimeToTwoSelfCover
open OddTwoFinalBlockOrbitCentralCoverDescentWindow OddTwoDefinition35GlobalAssembly
open OddTwoFengMalleForwardSourceJoin OddTwoFullHGPrincipalApplication
open TypeCCoherentFiniteRootConvention TypeCOddTwoCoherentTargetData
open TypeCOddTwoChosenRootMetadata TypeCOddTwoCoherentFamilyApplication
open TypeCOddTwoCanonicalPrimitiveFamily TypeBFullBlockCondition

variable {pDef : ℕ} {scope : FLZFullHGUniverse pDef 2}
variable {coverage : FullHGDefinition35Coverage scope}
variable {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
variable (routing : FullHGPrincipalRoutingSource coverage strictSource)
variable (blockSource : FullHGBlockSource coverage)
variable (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
variable (sources : PrincipalSourcePlaylist routing blockSource interpretation)
variable (typeA : ∀ (pair : FullHG scope)
    (presentation : TypeAActualPresentation pDef (routing.pairSource pair).rank
      (coverage.presentation pair).family.H),
    TypeAApplicationData (coverage.presentation pair).family presentation
      (blockSource.automorphisms pair) (blockSource.source pair))

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [CharP F pDef]
variable {center : CenterIntersectionSource n F} (B : BroughGroupSource center)
variable (cover : OddSymplecticFullCoverSource n F)
variable (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))
variable (P : LiteralFengMalleProblem n F)
variable (support : OperationsBrauerSupport P.iota P.irreducibleBrauerInjective
  P.blockSource.operations)
variable (reduction : ∀ (b : LiteralBlock P) (w : LiteralWeightFibre P.blockSource b),
  SelectedLocalReductionSource P.blockSource b w)
variable (binding : AmbientBinding P support reduction scope coverage)
variable (input : InputSemantics P)
variable (coordinates : RegularActionCoordinates B cover lifting)
variable (assumptionSource : FLZRemark54Source B cover lifting P)
variable (theoremSource : FLZTheorem57MapSource B cover lifting P support reduction
  scope coverage blockSource strictSource)

variable (O : LiteralDiagonalFieldRealisation n F)
variable (C : Convention 2 P.k P.K) (S : CanonicalTargetData P C)
variable (admissible : P.iota =
  C.rootAt (OddTwoFinalBlockOrbitCentralCoverDescentWindow.LiteralSp n F))
variable (physical : PhysicalInputs (S.targetData admissible).toProblem)
variable (jointSource : JointFengMalleProposition34Source P O C S admissible)
variable (cor46 : LiteralFengMalleCorollary46Certificate P O)

/-- Every complete-family clause is constructed after the actual source
application computes its Sp correspondence. The target keeps the original
PSp identity prime-to-two cover, specified catalogue and selected local table. -/
def familyWitness :
    FamilyWitness
      (canonicalFamily (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support)
      (canonicalCover (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support) :=
  canonicalFamilyWitnessFromFengMalle P O C S admissible physical jointSource input
    (assembledGlobalMap routing blockSource interpretation sources typeA
      B cover lifting P support reduction binding input coordinates assumptionSource theoremSource)
    cor46

include routing blockSource interpretation sources typeA B cover lifting
  support reduction binding input coordinates assumptionSource theoremSource
  physical jointSource cor46 in
/-- The exact conditional complete canonical target, with every external
source argument retained. This is the odd-field prime-two application only. -/
theorem full_block_condition_source_instantiated :
    Nonempty (FamilyWitness
      (canonicalFamily (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support)
      (canonicalCover (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support)) :=
  ⟨familyWitness routing blockSource interpretation sources typeA B cover lifting P
    support reduction binding input coordinates assumptionSource theoremSource O C S admissible
    physical jointSource cor46⟩

end ModularRep.PaperProofs.TypeCOddTwoCompleteSourceApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
