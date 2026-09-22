import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Literal fibre-sum cancellation over a finite set of blocks. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteFibres

theorem card_eq_fibres {A B : Type*} [Finite A] [Fintype B] (f : A → B) :
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} :=
  (Nat.card_congr (Equiv.sigmaFiberEquiv f).symm).trans Nat.card_sigma

theorem card_fibre_eq_of_other_fibres {A C B : Type*}
    [Finite A] [Finite C] [Finite B] (f : A → B) (g : C → B) (b0 : B)
    (htotal : Nat.card A = Nat.card C)
    (hother : ∀ b : B, b ≠ b0 →
      Nat.card {a : A // f a = b} = Nat.card {c : C // g c = b}) :
    Nat.card {a : A // f a = b0} = Nat.card {c : C // g c = b0} := by
  classical
  let : Fintype B := Fintype.ofFinite _
  have hf := card_eq_fibres f
  have hg := card_eq_fibres g
  have hrest : (∑ b ∈ Finset.univ.erase b0, Nat.card {a : A // f a = b}) =
      ∑ b ∈ Finset.univ.erase b0, Nat.card {c : C // g c = b} := by
    apply Finset.sum_congr rfl
    intro b hb
    exact hother b (Finset.mem_erase.mp hb).1
  have hfSplit := Finset.sum_erase_add Finset.univ
    (fun b : B => Nat.card {a : A // f a = b}) (Finset.mem_univ b0)
  have hgSplit := Finset.sum_erase_add Finset.univ
    (fun b : B => Nat.card {c : C // g c = b}) (Finset.mem_univ b0)
  omega

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteFibres


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
