import Formalisation

/-!
# Manuscript dependency ledger

This separate module exposes the companion dependency inventory for the iBAW
manuscript.  It exposes the node types used to catalogue
citations, semantic bridges, computations, and manuscript deductions.

The generic graph machinery is not a verification of any representation
theory.  Its `Interpretation.claim` and `DerivedRules.prove` fields are
arbitrary supplied propositions and proofs.  The graph therefore receives no
proof credit for a manuscript theorem; only separately typed mathematical
theorems in this project do.  The inventory remains useful for locating proof
obligations.  It is deliberately not imported by `ModularRep.lean`, so the
umbrella trust check contains only typed mathematical mechanisms and the
literal cycle checker.
-/

namespace ModularRep.ManuscriptVerification

/-- The node type for the dependency ledger of Section 2. -/
abbrev PreliminaryNode := Formalisation.PreliminaryDependencies.Node

/-- The node type for the dependency ledger of the type C section. -/
abbrev TypeCNode := Formalisation.TypeCDependencies.Node

/-- The node type for the dependency ledger of the type B section. -/
abbrev TypeBNode := Formalisation.TypeBDependencies.Node

/-- The node type for the dependency ledger of the sporadic section. -/
abbrev SporadicNode := Formalisation.SporadicDependencies.Node

end ModularRep.ManuscriptVerification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
