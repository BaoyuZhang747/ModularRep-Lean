import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures

/-! # Two supported block fibres determine the large-block residual -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoSupportedTotals

open SporadicFi24P3Definition44NamedCarrierFiniteFibres
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation

theorem twoSupported_large_card {A B : Type*}
    (f : A → B) (P : B → Prop) (roles : Fin 2 ≃ {b : B // P b})
    (h25 : Nat.card {a : A // P (f a)} = 25)
    (h2 : Nat.card {a : A // f a = (roles 1).1} = 2) :
    Nat.card {a : A // f a = (roles 0).1} = 23 := by
  classical
  let S := {a : A // P (f a) ∧ True}
  have hS : Nat.card S = 25 := by simpa only [S, and_true] using h25
  let _ : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; decide)
  let q : S → Fin 2 := fun a => roles.symm ⟨f a.1, a.2.1⟩
  have ef (i : Fin 2) : {a : S // q a = i} ≃ {a : A // f a = (roles i).1 ∧ True} :=
    (Equiv.subtypeEquivRight fun a => by
      change roles.symm ⟨f a.1, a.2.1⟩ = i ↔ f a.1 = (roles i).1
      rw [roles.symm_apply_eq]
      exact Subtype.ext_iff).trans
        (supportedFixedFibreEquiv f P (fun _ => True) (roles i).1 (roles i).2)
  have hsum : Nat.card S = ∑ i : Fin 2, Nat.card {a : A // f a = (roles i).1 ∧ True} := by
    refine (card_eq_fibres q).trans ?_
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.card_congr (ef i)
  have hbalance : 25 = Nat.card {a : A // f a = (roles 0).1} + 2 := by
    simpa [hS, Fin.sum_univ_succ, h2] using hsum
  omega

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoSupportedTotals


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
