import ModularRep.DefectZeroRepresentation
import ModularRep.OrdinaryIrreducibleCharacter

/-!
# Defect zero for ordinary irreducible characters

The predicate retains one simple representation witnessing both the character
and defect zero. Its equivalence-transport theorem remains in the weight
bridge; this module defines only the neutral predicate.
-/

open CategoryTheory Module

namespace ModularRep

universe u

/-- A function-valued ordinary irreducible character has defect zero when it
is afforded by a simple defect-zero finite-dimensional representation.  The
existential formulation avoids choosing a degree from a character value in
the coefficient field. -/
def IsDefectZeroOrdinaryCharacter
    (p : ℕ) {K H : Type u} [Field K] [CharZero K] [Group H] [Finite H]
    (chi : OrdinaryIrreducibleCharacter.Irr K H) : Prop :=
  ∃ V : FDRep K H,
    Simple V ∧ V.character = chi ∧ IsDefectZeroRepresentation p V

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
