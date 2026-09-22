import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Localization on a finite union of classes

The partition map is explicit. In the GGGR application it is the actual
conjugacy class map, and the selected labels are actual rational classes.
Only the pointwise vanishing and constancy inputs are needed here.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.FiniteClassPairing

open scoped BigOperators

variable {X A J K : Type*} [Fintype X] [Fintype J] [Field K]

def fibre (classOf : X → A) (label : J → A) (j : J) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => classOf x = label j)

theorem sum_localize (classOf : X → A) (label : J → A)
    (label_injective : Function.Injective label) (f : X → K) (v : J → K)
    (constant : ∀ j x, classOf x = label j → f x = v j)
    (outside : ∀ x, (∀ j, classOf x ≠ label j) → f x = 0) :
    ∑ x, f x = ∑ j, ((fibre classOf label j).card : K) * v j := by
  classical
  have partition : ∀ x, f x = ∑ j, if classOf x = label j then f x else 0 := by
    intro x
    by_cases hx : ∃ j, classOf x = label j
    · obtain ⟨j, hj⟩ := hx
      symm
      calc
        (∑ k, if classOf x = label k then f x else 0) =
            (if classOf x = label j then f x else 0) := by
          apply Finset.sum_eq_single j
          · intro k _ hkj
            have hk : classOf x ≠ label k := by
              intro hk
              exact hkj (label_injective (hk.symm.trans hj))
            simp [hk]
          · simp
        _ = f x := by simp [hj]
    · have hx' : ∀ j, classOf x ≠ label j := by simpa using hx
      simp [hx', outside x hx']
  calc
    (∑ x, f x) = ∑ x, ∑ j, if classOf x = label j then f x else 0 :=
      Finset.sum_congr rfl (fun x _ => partition x)
    _ = ∑ j, ∑ x, if classOf x = label j then f x else 0 := Finset.sum_comm
    _ = ∑ j, ((fibre classOf label j).card : K) * v j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      calc
        (∑ x ∈ Finset.univ.filter (fun x => classOf x = label j), f x) =
            ∑ x ∈ fibre classOf label j, v j := by
          apply Finset.sum_congr rfl
          intro x hx
          exact constant j x (Finset.mem_filter.mp hx).2
        _ = ((fibre classOf label j).card : K) * v j := by simp

omit [Fintype J] in
theorem weight_ne_zero [CharZero K] [Nonempty X]
    (classOf : X → A) (label : J → A) (representative : J → X)
    (rep_class : ∀ j, classOf (representative j) = label j) (j : J) :
    ((fibre classOf label j).card : K) / (Fintype.card X : K) ≠ 0 := by
  classical
  apply div_ne_zero
  · exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
      ⟨representative j, by simp [fibre, rep_class]⟩)
  · exact Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)

end ManuscriptIBAW.FiniteClassPairing

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
