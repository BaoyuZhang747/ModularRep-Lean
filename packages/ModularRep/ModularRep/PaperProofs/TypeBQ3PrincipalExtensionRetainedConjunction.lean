import Mathlib.Logic.Basic

/-! Logical construction retains the original witnesses and all seven clauses. -/

namespace ModularRep.PaperProofs.TypeBQ3PrincipalExtensionRetainedConjunction

universe u v

/-- Append a consequence of the first and third clauses at the same witnesses. -/
theorem append
    {A : Sort u} {B : Sort v}
    {P₁ P₂ P₃ P₄ P₅ P₆ P₇ T : A → B → Prop}
    (previous : ∃ a b, P₁ a b ∧ P₂ a b ∧ P₃ a b ∧ P₄ a b ∧
      P₅ a b ∧ P₆ a b ∧ P₇ a b)
    (step : ∀ a b, P₁ a b → P₃ a b → T a b) :
    ∃ a b, P₁ a b ∧ P₂ a b ∧ P₃ a b ∧ P₄ a b ∧
      P₅ a b ∧ P₆ a b ∧ P₇ a b ∧ T a b :=
  Exists.elim previous fun a ha =>
    Exists.elim ha fun b h =>
      ⟨a, b, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2, step a b h.1 h.2.2.1⟩

end ModularRep.PaperProofs.TypeBQ3PrincipalExtensionRetainedConjunction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
