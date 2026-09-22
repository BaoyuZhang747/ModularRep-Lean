import ManuscriptIBAW.TypeC.EvenApplicationInputs
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

/-! The BAW-good criterion for symplectic blocks with cyclic outer action.
Feng–Li–Zhang, Theorem 3.18, supplies the criterion. Its equivariance and
extension hypotheses are proved from the constructed bijection. -/
noncomputable section
namespace ManuscriptIBAW.TypeC.EvenApplication
open scoped MonoidAlgebra Pointwise

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldEJGCPairActual
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverExplicitHypotheses
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldLemmas35_36Actual
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks
open ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder
open ModularRep.PaperProofs.EvenFieldProposition39Relative
open ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank
open ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven
open ModularRep.PaperProofs.EvenFieldProposition39Sp6Three
open ModularRep.PaperProofs.EvenFieldProposition39Suzuki
open ModularRep.PaperProofs.EvenFieldProposition39TypeA

open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
structure SelfCoverAmbient
    {r a ell : ℕ} {ha : 0 < a}
    (source : UnipotentInputs r a ell ha) where
  identification :
    let _ := source.fintypeFixed
    SelfCoverSourceIdentification
      (p := ell) (H := FiniteSymplecticFixed r a)
  automorphismMap_bijective :
    Function.Bijective (semidirectToMulAut
      (fieldAction r a ha))

/-- Prove the structural conditions from the specified cover identification. -/
def SelfCoverAmbient.structural
    {r a ell : ℕ} {ha : 0 < a}
    {source : UnipotentInputs r a ell ha}
    (ambient : SelfCoverAmbient source) :
    StructuralSource (fieldAction r a ha) := by
  letI := source.fintypeFixed
  exact
    { perfect := ⟨ambient.identification.ellPrimeCover.perfect⟩
      centerless := ambient.identification.center_eq_bot
      automorphismMap_bijective := ambient.automorphismMap_bijective }

abbrev currentProblem {r a ell : ℕ} {ha : 0 < a}
    (source : UnipotentInputs r a ell ha) :=
  let _ := source.fintypeFixed
  let _ := source.finiteField
  SelfCoverProblem source.iota source.hinj source.blocks
      (fieldAction r a ha) source.blockSource source.block
      source.T source.localReduction

abbrev currentAutomorphisms {r a ell : ℕ} {ha : 0 < a}
    (source : UnipotentInputs r a ell ha)
    (ambient : SelfCoverAmbient source) :=
  let _ := source.fintypeFixed
  let _ := source.finiteField
  let _ := source.cyclicField
  SelfCoverAutomorphisms source.iota source.hinj source.blocks
      (fieldAction r a ha) source.blockSource source.block
      source.T source.localReduction ambient.structural


section Criterion
variable {r a ell : ℕ} {ha : 0 < a}
  (input : UnipotentInputs r a ell ha)

variable (ambient : SelfCoverAmbient input)
  (relation :
    let _ := input.fintypeFixed
    FLZBAWGoodRelation (currentProblem input) (currentAutomorphisms input ambient)
    ambient.identification.ellPrimeCover)

/-- E2: FLZ Theorem 3.18 with its full BAW-good conclusion, including the actual
identity cover, actions, fixed relation, and complete explicit clauses. This
does not infer BAW-goodness from the weaker relation in Definition 3.5. -/
structure CriterionSource where
  operations :
    let _ := input.fintypeFixed
    ClauseIIISourceOperations input.iota input.hinj input.blocks
    input.blockSource input.block
  operationAdapters :
    let _ := input.fintypeFixed
    ClauseIIISelfCoverAdapters input.iota input.hinj input.blocks
    input.blockSource input.block operations
  applyTheorem318 :
    let _ := input.fintypeFixed
    let _ := input.finiteField
    let _ := input.cyclicField
    CompletedExplicitPackage input.iota input.hinj input.blocks
    (fieldAction r a ha) input.blockSource input.block input.T input.localReduction
    input.endgame ambient.structural operations operationAdapters →
    Nonempty (FLZBAWGoodBlockWitness (currentProblem input)
      (currentAutomorphisms input ambient) ambient.identification.ellPrimeCover relation)

variable (criterion : CriterionSource input ambient relation)
  (globalRoots :
    let _ := input.fintypeFixed
    let _ := input.finiteField
    ∀ psi : BrauerFibre input.iota input.hinj input.blocks input.block,
    ClauseIVAGlobalRootInput input.iota input.hinj input.blocks (fieldAction r a ha)
      input.blockSource input.block input.T psi)
  (localRoots :
    let _ := input.fintypeFixed
    let _ := input.finiteField
    ∀ psi : BrauerFibre input.iota input.hinj input.blocks input.block,
    ClauseIVBLocalRootInput (field := fieldAction r a ha)
      (blockSource := input.blockSource) (block := input.block)
      (localReduction := input.localReduction) (input.endgame.omega.toEquiv psi))

include criterion globalRoots localRoots in
/-- Apply the criterion to the constructed map, semidirect product equivariance
and extensions, with the stated root conditions. -/
theorem unipotent_bawGood :
    let _ := input.fintypeFixed
    Nonempty (FLZBAWGoodBlockWitness (currentProblem input)
      (currentAutomorphisms input ambient) ambient.identification.ellPrimeCover relation) := by
  let := input.fintypeFixed
  let := input.finiteField
  let := input.cyclicField
  exact criterion.applyTheorem318 (completedExplicitPackage_of_cyclicEndgame
    (iota := input.iota) (hinj := input.hinj) (blocks := input.blocks)
    (field := fieldAction r a ha) (blockSource := input.blockSource)
    (block := input.block) (T := input.T) (localReduction := input.localReduction)
    ambient.structural criterion.operations criterion.operationAdapters
    input.endgame globalRoots localRoots)

/-- External forward implication of Feng--Li--Zhang after equation (3.17), from BAW-goodness
to the specified Definition 3.5 relation for the same character and weight. No converse is assumed. -/
structure RelationPassage
    (source : FLZSourceSemantics (currentProblem input) (currentAutomorphisms input ambient)) : Prop where
  implication : ∀ psi weight, relation.bawGoodBlockIsomorphic psi weight →
    source.definition35BlockIsomorphic psi weight

include criterion globalRoots localRoots in
theorem unipotent_definition35
    (source : FLZSourceSemantics (currentProblem input) (currentAutomorphisms input ambient))
    (passage : RelationPassage input ambient relation source) :
    Nonempty (Definition35IBAWBijection (currentProblem input)
      (currentAutomorphisms input ambient) source) := by
  obtain ⟨good⟩ := unipotent_bawGood input ambient relation criterion globalRoots localRoots
  refine ⟨{ omega := good.omega
            equivariant := good.equivariant
            blockIsomorphism := ?_ }⟩
  intro psi
  exact passage.implication psi (good.omega psi) (good.blockIsomorphism psi)
end Criterion
end ManuscriptIBAW.TypeC.EvenApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
