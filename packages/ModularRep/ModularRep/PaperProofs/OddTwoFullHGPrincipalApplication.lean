import ModularRep.PaperProofs.OddTwoPrincipalFamilyCompletedSeed
import ModularRep.PaperProofs.OddTwoPrincipalFamilyAuthenticInterpretation

/-!
# The uniform principal application and fixed final Type C window

Every principal value is constructed from its licensed source-only family
inputs. The authentic meaning is derived from the SAME Full-HG predicate,
for every root packet, and the correction and carrier transport are computed.
The unfiltered strict-block packet then feeds the fixed literal FLZ map,
construction from block orbit representatives and forward Feng--Malle gate.

All external source arguments retain their existing authentic scope.
No completed principal supplier, strict-block packet, global map or desired
final proposition is an input to this composition.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoFullHGPrincipalApplication

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCompletedSeed
open ModularRep.PaperProofs.OddTwoPrincipalFamilyAuthenticInterpretation
open ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
open ModularRep.PaperProofs.OddTwoDefinition35GlobalAssembly
open ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin

variable {pDef : ℕ} {scope : FLZFullHGUniverse pDef 2}
variable {coverage : FullHGDefinition35Coverage scope}
variable {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
variable (routing : FullHGPrincipalRoutingSource coverage strictSource)
variable (blockSource : FullHGBlockSource coverage)
variable (interpretation : FullHGInterpretation scope coverage blockSource strictSource)

/-- Only the existing licensed primitive/root/published inputs, on each
actual computed D. Every Full-HG pair, block and routed carrier remains in
the quantifier. There is no intrinsic-meaning or completed-seed field. -/
structure PrincipalSourcePlaylist where
  atPrincipal : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block)
      (coordinates : SymplecticCoordinates pDef (routing.pairSource pair).rank
        (coverage.presentation pair).family.H)
      (carrier : OddSymplecticPrincipalCarrier
        ((coverage.presentation pair).family.problem block)
        (routing.pairSource pair).rank coordinates.F),
    FamilyInputs (coverage.presentation pair).family block carrier
      (interpretation.blockSemantics pair) (interpretation.standard pair)

variable (sources : PrincipalSourcePlaylist routing blockSource interpretation)

/-- K constructs the previously open supplier. The only intrinsic meaning
used is the every-root theorem from this SAME Full-HG interpretation. -/
def completedPrincipalSeeds : CompletedPrincipalSeeds routing blockSource where
  atPrincipal pair block coordinates carrier := by
    let family := (coverage.presentation pair).family
    let input := interpretation.blockSemantics pair
    let I := sources.atPrincipal pair block coordinates carrier
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    exact ⟨completedAt family block carrier input (interpretation.standard pair) I
      (blockSource.automorphisms pair block) (blockSource.source pair block)
      (authenticInterpretation scope coverage blockSource strictSource interpretation pair block
        carrier I.operations I.dictionary I.published.standardTransport)⟩

variable (typeA : ∀ (pair : FullHG scope)
    (presentation : TypeAActualPresentation pDef (routing.pairSource pair).rank
      (coverage.presentation pair).family.H),
    TypeAApplicationData (coverage.presentation pair).family presentation
      (blockSource.automorphisms pair) (blockSource.source pair))

/-- K combines the existing full routing, coefficient-two type-A source,
and newly computed principal supplier. No relative pair is discarded. -/
def strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource :=
  fullHG_strictBlocks routing blockSource typeA
    (completedPrincipalSeeds routing blockSource interpretation sources)

section FinalApplication

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [CharP F pDef]
variable {C : CenterIntersectionSource n F} (B : BroughGroupSource C)
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

/-- The literal Sp map is combined from the actual FLZ block maps obtained
using the computed strict-block packet. It is not a new source input. -/
def assembledGlobalMap : LiteralGlobalMap P :=
  OddTwoFLZ57LiteralMapSource.globalMap B cover lifting P support reduction
    scope coverage blockSource strictSource binding interpretation input coordinates
    assumptionSource theoremSource
    (strictBlocks routing blockSource interpretation sources typeA)

include routing blockSource interpretation sources typeA B cover lifting
  support reduction binding input coordinates assumptionSource theoremSource in
/-- The fixed original Spath target follows by the recorded FORWARD gate.
All external assumptions remain explicit; no assertion identifies the
final target map with the constructed Sp map or adds another central descent. -/
theorem originalIBAW
    (O : LiteralDiagonalFieldRealisation n F) (target : TargetData P)
    (fm34 : FengMalleProposition34Source P O target)
    (cor46 : LiteralFengMalleCorollary46Certificate P O) :
    OddTwoLiteralSpathTarget.OriginalIBAW target.toProblem :=
  originalIBAW_of_literalGlobalMap P O target fm34 input
    (assembledGlobalMap routing blockSource interpretation sources typeA
      B cover lifting P support reduction binding input coordinates assumptionSource theoremSource)
    cor46

end FinalApplication

end ModularRep.PaperProofs.OddTwoFullHGPrincipalApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
