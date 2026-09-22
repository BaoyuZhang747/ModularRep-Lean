import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.FinCases

/-! Finite block fibres decompose from the actual block assignment.
No equation decomposing character or weight counts is a source premise. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoFibre

theorem two_roles_bijective {B : Type*} (roles : Fin 2 → B)
    (hinj : Function.Injective roles) (hcard : Nat.card B = 2) :
    Function.Bijective roles := by
  let : Finite B := Nat.finite_of_card_ne_zero (by omega)
  apply (Nat.bijective_iff_injective_and_card roles).mpr
  exact ⟨hinj, by simp [hcard]⟩

theorem two_roles_cover {B : Type*} (roles : Fin 2 → B)
    (hinj : Function.Injective roles) (hcard : Nat.card B = 2) (b : B) :
    b = roles 0 ∨ b = roles 1 := by
  obtain ⟨i, rfl⟩ := (two_roles_bijective roles hinj hcard).surjective b
  fin_cases i <;> simp

theorem card_eq_two_fibres {A B : Type*} [Finite A]
    (f : A → B) (b0 b1 : B) (hne : b0 ≠ b1)
    (hcover : ∀ b : B, b = b0 ∨ b = b1) :
    Nat.card A = Nat.card {x : A // f x = b0} +
      Nat.card {x : A // f x = b1} := by
  classical
  have hiff : ∀ x : A, (¬ f x = b0) ↔ f x = b1 := by
    intro x
    constructor
    · intro hx
      exact (hcover (f x)).resolve_left hx
    · intro hx heq
      exact hne (heq.symm.trans hx)
  let e := (Equiv.sumCompl (fun x : A => f x = b0)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight hiff))
  exact (Nat.card_congr e).trans Nat.card_sum

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoFibre



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
