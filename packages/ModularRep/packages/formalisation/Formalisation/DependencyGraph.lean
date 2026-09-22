import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Auditable dependency graphs

This module supplies the abstract machinery used by the manuscript
dependency audit.  Nodes are classified as cited inputs, computational
inputs, still external semantic bridges, or derived manuscript results.
Every edge must lower a natural-number rank.  This gives a machine-checked
certificate that the dependency graph is acyclic.

For an interpretation assigning a proposition to every node, external facts
and one proof rule for each derived node imply every result in the graph.
The framework checks the declared dependency structure and its acyclicity.
It does not inspect the provenance of a supplied proof rule: such a rule can
close over assumptions not represented by graph nodes.  Consequently these
files are conditional dependency ledgers, not proof provenance certificates.
Nor does the framework assert that a cited theorem, computation, or semantic
bridge is true; those three kinds are deliberately visible assumptions.
-/

namespace Formalisation.DependencyGraph

/-- Provenance of a node in the dependency audit. -/
inductive NodeKind where
  | cited
  | computation
  | semanticBridge
  | derived
  deriving DecidableEq, Repr

/-- A finite or otherwise explicitly presented dependency graph. -/
structure Graph (Node : Type*) where
  kind : Node → NodeKind
  dependencies : Node → List Node
  rank : Node → ℕ
  dependencies_lower : ∀ {n d : Node}, d ∈ dependencies n → rank d < rank n
  external_has_no_dependencies : ∀ {n : Node}, kind n ≠ NodeKind.derived →
    dependencies n = []

variable {Node : Type*}

/-- A proposition assigned to every dependency node. -/
structure Interpretation (Node : Type*) where
  claim : Node → Prop

/-- Proofs of all cited, computational, and semantic-bridge leaves. -/
structure ExternalFacts (G : Graph Node) (I : Interpretation Node) where
  prove : ∀ n, G.kind n ≠ NodeKind.derived → I.claim n

/-- A proof rule for each derived result.  Its listed immediate dependencies
are supplied as explicit arguments.  Lean's type theory does not prevent the
rule itself from having been constructed using additional closed-over facts. -/
structure DerivedRules (G : Graph Node) (I : Interpretation Node) where
  prove : ∀ n, G.kind n = NodeKind.derived →
    (∀ d, d ∈ G.dependencies n → I.claim d) → I.claim n

namespace Graph

variable (G : Graph Node) (I : Interpretation Node)

/-- Acyclic dependency induction: external leaves and the listed proof rules
derive every claim in the graph. -/
theorem derive_all (E : ExternalFacts G I) (R : DerivedRules G I) :
    ∀ n, I.claim n := by
  intro n
  induction n using (measure G.rank).wf.induction with
  | h n ih =>
      by_cases hn : G.kind n = NodeKind.derived
      · apply R.prove n hn
        intro d hd
        exact ih d (G.dependencies_lower hd)
      · exact E.prove n hn

/-- In particular, no node is one of its own immediate dependencies. -/
theorem not_mem_own_dependencies (n : Node) : n ∉ G.dependencies n := by
  intro h
  have := G.dependencies_lower h
  omega

/-- There is no dependency edge in both directions. -/
theorem no_two_cycle {n d : Node} (hnd : d ∈ G.dependencies n) :
    n ∉ G.dependencies d := by
  intro hdn
  have h₁ := G.dependencies_lower hnd
  have h₂ := G.dependencies_lower hdn
  omega

end Graph

end Formalisation.DependencyGraph


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
