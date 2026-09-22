import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation
import Mathlib.Algebra.BigOperators.Fin

/-! # Five supported fibres determine the remaining total and fixed counts -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures

open SporadicFi24P3Definition44NamedCarrierFiniteFibres
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation

def fibreSignature {A B : Type*} (f : A → B) (T : A → Prop) (b : B) : Nat × Nat :=
  (Nat.card {a : A // f a = b}, Nat.card {a : A // f a = b ∧ T a})

def nonprincipalSignature (j : Fin 4) : Nat × Nat :=
  if j = 0 then (3, 1) else if j = 1 then (3, 3) else (1, 1)

theorem fiveSupported_card_balance {A B : Type*}
    (f : A → B) (P : B → Prop) (T : A → Prop)
    (roles : Fin 5 ≃ {b : B // P b}) [Finite {a : A // P (f a) ∧ T a}] :
    Nat.card {a : A // P (f a) ∧ T a} =
      Nat.card {a : A // f a = (roles 0).1 ∧ T a} +
        ∑ j : Fin 4, Nat.card {a : A // f a = (roles j.succ).1 ∧ T a} := by
  classical
  let S := {a : A // P (f a) ∧ T a}
  let q : S → Fin 5 := fun a => roles.symm ⟨f a.1, a.2.1⟩
  have ef (i : Fin 5) : {a : S // q a = i} ≃
      {a : A // f a = (roles i).1 ∧ T a} :=
    (Equiv.subtypeEquivRight fun a => by
      change roles.symm ⟨f a.1, a.2.1⟩ = i ↔ f a.1 = (roles i).1
      rw [roles.symm_apply_eq]
      exact Subtype.ext_iff).trans
        (supportedFixedFibreEquiv f P T (roles i).1 (roles i).2)
  calc
    Nat.card S = ∑ i : Fin 5, Nat.card {a : S // q a = i} := card_eq_fibres q
    _ = ∑ i : Fin 5, Nat.card {a : A // f a = (roles i).1 ∧ T a} := by
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.card_congr (ef i)
    _ = _ := by rw [Fin.sum_univ_succ]

theorem principalSignature_of_five {A B : Type*}
    (f : A → B) (P : B → Prop) (T : A → Prop)
    (roles : Fin 5 ≃ {b : B // P b})
    (h41 : Nat.card {a : A // P (f a)} = 41)
    (h31 : Nat.card {a : A // P (f a) ∧ T a} = 31)
    (hother : ∀ j : Fin 4,
      fibreSignature f T (roles j.succ).1 = nonprincipalSignature j) :
    fibreSignature f T (roles 0).1 = (33, 25) := by
  classical
  have hTrue : Nat.card {a : A // P (f a) ∧ True} = 41 := by
    simpa only [and_true] using h41
  let _ : Finite {a : A // P (f a) ∧ True} :=
    Nat.finite_of_card_ne_zero (by rw [hTrue]; decide)
  let _ : Finite {a : A // P (f a) ∧ T a} :=
    Nat.finite_of_card_ne_zero (by rw [h31]; decide)
  have ht := fiveSupported_card_balance f P (fun _ => True) roles
  have hf := fiveSupported_card_balance f P T roles
  have hrestTotal : (∑ j : Fin 4,
      Nat.card {a : A // f a = (roles j.succ).1 ∧ True}) = 8 := by
    calc
      _ = ∑ j : Fin 4, (nonprincipalSignature j).1 := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [fibreSignature, and_true] using congrArg Prod.fst (hother j)
      _ = 8 := by decide
  have hrestFixed : (∑ j : Fin 4,
      Nat.card {a : A // f a = (roles j.succ).1 ∧ T a}) = 6 := by
    calc
      _ = ∑ j : Fin 4, (nonprincipalSignature j).2 := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [fibreSignature] using congrArg Prod.snd (hother j)
      _ = 6 := by decide
  rw [hTrue, hrestTotal] at ht
  rw [h31, hrestFixed] at hf
  simp only [and_true] at ht
  unfold fibreSignature
  exact Prod.ext (by omega) (by omega)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
