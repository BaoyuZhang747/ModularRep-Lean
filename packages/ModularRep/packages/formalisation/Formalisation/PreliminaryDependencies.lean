import Formalisation.DependencyGraph
import Formalisation.ExactStabilizer
import Formalisation.IBAWOrbitTransport
import Formalisation.PCore
import Mathlib.Tactic

/-!
# Dependency certificate for the preliminaries

This file lists the citation-level and semantic inputs used in Section 2 and
the manuscript results derived from them.  The resulting graph is
machine-checked to be acyclic.  It deliberately distinguishes the abstract
finite set and group-theoretic deductions proved elsewhere in this project
from character-theoretic facts that are still external.

The theorem `preliminaries_of_dependencies` is conditional: it propagates the
listed leaves through the supplied proof rules.  It does not turn a literature
citation into a Lean proof or inspect whether a proof rule closed over an
unlisted assumption.
-/

namespace Formalisation.PreliminaryDependencies

open Formalisation.DependencyGraph

/-- Every external input and derived result used in the preliminaries. -/
inductive Node where
  -- Cited inputs.
  | spathBlockInductionDefinition
  | spathIBAWDefinition
  | spathTripleEquivalence
  | flzTripleFormulation
  | koshitaniSpathBlockOrbitLemma
  | spathBlockOrbitRemark
  | spathFixedPointDescent
  | burnsideMarkInjectivity
  | conlonPermutationLatticeTheorem
  | geckHissIntegralBasicSetDefinition
  | isaacsCyclicOrdinaryExtension
  | navarroCyclicBrauerExtension
  -- Character-theoretic facts not developed in Mathlib.
  | centralReductionBijection
  | centralIdempotentSectorFacts
  -- Results of Section 2.
  | centralSectorCompatibility
  | localIBAWRestriction
  | blockOrbitAggregation
  | fixedPointDescentCorollary
  | hypoelementarySubgroupInheritance
  | conlonMarkCorollary
  | integralBasicSetBridge
  | cyclicCharacterExtension
  | preliminariesAvailable
  deriving DecidableEq, Repr

def kind : Node → NodeKind
  | .spathBlockInductionDefinition
  | .spathIBAWDefinition
  | .spathTripleEquivalence
  | .flzTripleFormulation
  | .koshitaniSpathBlockOrbitLemma
  | .spathBlockOrbitRemark
  | .spathFixedPointDescent
  | .burnsideMarkInjectivity
  | .conlonPermutationLatticeTheorem
  | .geckHissIntegralBasicSetDefinition
  | .isaacsCyclicOrdinaryExtension
  | .navarroCyclicBrauerExtension => .cited
  | .centralReductionBijection
  | .centralIdempotentSectorFacts => .semanticBridge
  | _ => .derived

/-- Immediate dependencies, with citation locators documented at the use
sites in `02-preliminaries.tex`. -/
def dependencies : Node → List Node
  | .centralSectorCompatibility =>
      [.centralReductionBijection, .centralIdempotentSectorFacts,
        .spathBlockInductionDefinition]
  | .localIBAWRestriction =>
      [.spathIBAWDefinition, .spathTripleEquivalence, .flzTripleFormulation]
  | .blockOrbitAggregation =>
      [.koshitaniSpathBlockOrbitLemma, .spathBlockOrbitRemark,
        .centralSectorCompatibility]
  | .fixedPointDescentCorollary => [.spathFixedPointDescent]
  | .hypoelementarySubgroupInheritance => []
  | .conlonMarkCorollary =>
      [.hypoelementarySubgroupInheritance,
        .conlonPermutationLatticeTheorem, .burnsideMarkInjectivity]
  | .integralBasicSetBridge =>
      [.geckHissIntegralBasicSetDefinition, .conlonMarkCorollary]
  | .cyclicCharacterExtension =>
      [.isaacsCyclicOrdinaryExtension, .navarroCyclicBrauerExtension]
  | .preliminariesAvailable =>
      [.centralSectorCompatibility, .localIBAWRestriction,
        .blockOrbitAggregation, .fixedPointDescentCorollary,
        .conlonMarkCorollary, .integralBasicSetBridge,
        .cyclicCharacterExtension]
  | _ => []

def rank : Node → ℕ
  | .spathBlockInductionDefinition
  | .spathIBAWDefinition
  | .spathTripleEquivalence
  | .flzTripleFormulation
  | .koshitaniSpathBlockOrbitLemma
  | .spathBlockOrbitRemark
  | .spathFixedPointDescent
  | .burnsideMarkInjectivity
  | .conlonPermutationLatticeTheorem
  | .geckHissIntegralBasicSetDefinition
  | .isaacsCyclicOrdinaryExtension
  | .navarroCyclicBrauerExtension
  | .centralReductionBijection
  | .centralIdempotentSectorFacts => 0
  | .centralSectorCompatibility
  | .localIBAWRestriction
  | .fixedPointDescentCorollary
  | .hypoelementarySubgroupInheritance
  | .cyclicCharacterExtension => 1
  | .blockOrbitAggregation
  | .conlonMarkCorollary => 2
  | .integralBasicSetBridge => 3
  | .preliminariesAvailable => 4

/-- The complete Section 2 dependency graph. -/
def graph : Graph Node where
  kind := kind
  dependencies := dependencies
  rank := rank
  dependencies_lower := by
    intro n d h
    cases n <;> cases d <;> simp [dependencies, rank] at h ⊢
  external_has_no_dependencies := by
    intro n h
    cases n <;> simp [kind, dependencies] at h ⊢

theorem no_immediate_self_dependency (n : Node) :
    n ∉ dependencies n := graph.not_mem_own_dependencies n

theorem no_immediate_two_cycle {n d : Node} (h : d ∈ dependencies n) :
    n ∉ dependencies d := graph.no_two_cycle h

/-- Conditional dependency construction for Section 2.  Concrete abstract parts
related to this ledger are proved separately in `PCore`, `ExactStabilizer`,
and the iBAW construction files; identifying those generic theorems with a
manuscript claim remains part of the supplied interpretation and rules. -/
theorem preliminaries_of_dependencies
    (I : Interpretation Node)
    (E : ExternalFacts graph I)
    (R : DerivedRules graph I) :
    I.claim .preliminariesAvailable :=
  graph.derive_all I E R .preliminariesAvailable

end Formalisation.PreliminaryDependencies


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
