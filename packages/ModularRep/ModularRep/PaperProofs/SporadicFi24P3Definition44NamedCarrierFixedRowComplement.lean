import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Basic

/-! # Fixed-point subtraction from an invariant singleton row -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedRowComplement

theorem natCard_subtype_compl {X : Type*} [Finite X] (P : X → Prop) :
    Nat.card {x : X // ¬ P x} = Nat.card X - Nat.card {x : X // P x} := by
  classical
  let : Fintype X := Fintype.ofFinite X
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_compl P

theorem fixed_compl_card_one_of_invariant_singleton
    {X : Type*} (f : X → X) (P : X → Prop)
    (hP : ∀ x : X, P x → P (f x))
    (hsingle : Nat.card {x : X // P x} = 1)
    (hfixed : Nat.card {x : X // f x = x} = 2) :
    Nat.card {x : X // ¬ P x ∧ f x = x} = 1 := by
  classical
  have hsub : Subsingleton {x : X // P x} := (Nat.card_eq_one_iff_unique.mp hsingle).1
  have hfix (x : X) (hx : P x) : f x = x :=
    congrArg Subtype.val (hsub.elim ⟨f x, hP x hx⟩ ⟨x, hx⟩)
  let : Finite {x : X // f x = x} := Nat.finite_of_card_ne_zero (by rw [hfixed]; decide)
  let eP : {x : {x : X // f x = x} // P x.1} ≃ {x : X // P x} :=
    Equiv.subtypeSubtypeEquivSubtype (fun hx => hfix _ hx)
  let eN : {x : {x : X // f x = x} // ¬ P x.1} ≃
      {x : X // ¬ P x ∧ f x = x} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : X => f x = x) (fun x : X => ¬ P x)).trans
      (Equiv.subtypeEquivRight (fun _ => and_comm))
  have hpos : Nat.card {x : {x : X // f x = x} // P x.1} = 1 :=
    (Nat.card_congr eP).trans hsingle
  have hneg := natCard_subtype_compl (fun x : {x : X // f x = x} => P x.1)
  rw [hfixed, hpos] at hneg
  exact (Nat.card_congr eN).symm.trans hneg

theorem compl_card_three_of_card_four {X : Type*} (P : X → Prop)
    (htotal : Nat.card X = 4) (hsingle : Nat.card {x : X // P x} = 1) :
    Nat.card {x : X // ¬ P x} = 3 := by
  let : Finite X := Nat.finite_of_card_ne_zero (by rw [htotal]; decide)
  have h := natCard_subtype_compl P
  rwa [htotal, hsingle] at h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedRowComplement


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
