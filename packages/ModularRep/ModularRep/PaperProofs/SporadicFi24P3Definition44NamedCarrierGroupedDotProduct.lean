import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGroupedDotProduct

universe u v w
variable {Tag : Type u} {Index : Type v}
variable [Fintype Tag] [DecidableEq Tag] [Fintype Index]

theorem sum_grouped_by_tag
    {A : Type w} [AddCommMonoid A]
    (tag : Index → Tag) (term : Index → A) :
    (∑ d : Tag, ∑ j : Index, if tag j = d then term j else 0) =
      ∑ j : Index, term j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem sum_eq_grouped_of_tagged_values
    {A : Type w} [AddCommMonoid A]
    (tag : Index → Tag) (term : Index → A) (grouped : Tag → Index → A)
    (hvalues : ∀ d j, tag j = d → grouped d j = term j) :
    (∑ j : Index, term j) =
      ∑ d : Tag, ∑ j : Index, if tag j = d then grouped d j else 0 := by
  calc
    (∑ j : Index, term j) =
        ∑ d : Tag, ∑ j : Index, if tag j = d then term j else 0 :=
      (sum_grouped_by_tag tag term).symm
    _ = ∑ d : Tag, ∑ j : Index,
        if tag j = d then grouped d j else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : tag j = d
      · simp only [if_pos h]
        exact (hvalues d j h).symm
      · simp only [if_neg h]

theorem sum_eq_cast_of_grouped_residuals
    {K : Type w} [Ring K]
    (tag : Index → Tag) (term : Index → K) (grouped : Tag → Index → K)
    (constant : Tag → ℤ)
    (hvalues : ∀ d j, tag j = d → grouped d j = term j)
    (hchecked : ∀ d,
      (∑ j : Index, if tag j = d then grouped d j else 0) -
        (constant d : K) = 0) :
    (∑ j : Index, term j) = ((∑ d : Tag, constant d : ℤ) : K) := by
  calc
    (∑ j : Index, term j) =
        ∑ d : Tag, ∑ j : Index,
          if tag j = d then grouped d j else 0 :=
      sum_eq_grouped_of_tagged_values tag term grouped hvalues
    _ = ∑ d : Tag, (constant d : K) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact sub_eq_zero.mp (hchecked d)
    _ = ((∑ d : Tag, constant d : ℤ) : K) :=
      (Int.cast_sum Finset.univ constant).symm

theorem dot_eq_scaled_delta_of_grouped_residuals
    {K : Type w} [Ring K] {n : ℕ}
    (tag : Index → Tag) (left right : Index → K)
    (grouped : Tag → Index → K) (constant : Tag → ℤ)
    (L : ℤ) (a b : Fin n)
    (hvalues : ∀ d j, tag j = d → grouped d j = left j * right j)
    (hchecked : ∀ d,
      (∑ j : Index, if tag j = d then grouped d j else 0) -
        (constant d : K) = 0)
    (hbudget : (∑ d : Tag, constant d) = if a = b then L else 0) :
    (∑ j : Index, left j * right j) =
      (L : K) * (if a = b then 1 else 0) := by
  have h := sum_eq_cast_of_grouped_residuals tag
    (fun j => left j * right j) grouped constant hvalues hchecked
  rw [hbudget] at h
  by_cases hab : a = b
  · simpa only [if_pos hab, mul_one] using h
  · simpa only [if_neg hab, Int.cast_zero, mul_zero] using h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGroupedDotProduct


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
