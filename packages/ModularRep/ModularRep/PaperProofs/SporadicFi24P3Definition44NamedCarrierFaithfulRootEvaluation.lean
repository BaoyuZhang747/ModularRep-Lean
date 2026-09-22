import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnRelations
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
import Mathlib.Tactic.FinCases
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulRootEvaluation
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
open SporadicFi24P3Definition44NamedCarrierFaithfulLocalRelations
open SporadicFi24P3Definition44NamedCarrierFaithfulColumnRelations
variable {K : Type*} [Field K] [CharZero K]

def localRoots (zeta : K) (d : Fin 6) : K := zeta ^ (770385 / conductor d)
def fullRoots (zeta : K) (d : Fin 7) : K := zeta ^ (770385 / fullConductor d)

theorem local_modulus_zero {zeta : K} (hzeta : IsPrimitiveRoot zeta 770385) :
    ∀ d, eval (localRoots zeta d) (modulus d) = 0 := by
  intro d
  fin_cases d
  · rfl
  · change eval (zeta ^ 154077) [1, 1, 1, 1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 154077) 5 :=
      localRoot_isPrimitive (d := 5) (by norm_num) hzeta (by norm_num)
    have h := phi5_zero hroot
    generalize zeta ^ 154077 = w at h ⊢
    unfold phi5 at h
    simp only [eval, Int.cast_one, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 36685) [1, -1, 0, 1, -1, 0, 1, 0, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 36685) 21 :=
      localRoot_isPrimitive (d := 21) (by norm_num) hzeta (by norm_num)
    have h := phi21_zero hroot
    generalize zeta ^ 36685 = w at h ⊢
    unfold phi21 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 33495) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 33495) 23 :=
      localRoot_isPrimitive (d := 23) (by norm_num) hzeta (by norm_num)
    have h := phi23_zero hroot
    generalize zeta ^ 33495 = w at h ⊢
    unfold phi23 at h
    simp only [eval, Int.cast_one, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 26565) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 26565) 29 :=
      localRoot_isPrimitive (d := 29) (by norm_num) hzeta (by norm_num)
    have h := phi29_zero hroot
    generalize zeta ^ 26565 = w at h ⊢
    unfold phi29 at h
    simp only [eval, Int.cast_one, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 23345) [1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 23345) 33 :=
      localRoot_isPrimitive (d := 33) (by norm_num) hzeta (by norm_num)
    have h := phi33_zero hroot
    generalize zeta ^ 23345 = w at h ⊢
    unfold phi33 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h

theorem full_modulus_zero {zeta : K} (hzeta : IsPrimitiveRoot zeta 770385) :
    ∀ d, eval (fullRoots zeta d) (fullModulus d) = 0 := by
  intro d
  fin_cases d
  · rfl
  · change eval (zeta ^ 256795) [1, 1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 256795) 3 :=
      localRoot_isPrimitive (d := 3) (by norm_num) hzeta (by norm_num)
    have h := phi3_zero hroot
    generalize zeta ^ 256795 = w at h ⊢
    unfold phi3 at h
    simp only [eval, Int.cast_one, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 51359) [1, -1, 0, 1, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 51359) 15 :=
      localRoot_isPrimitive (d := 15) (by norm_num) hzeta (by norm_num)
    have h := phi15_zero hroot
    generalize zeta ^ 51359 = w at h ⊢
    unfold phi15 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 36685) [1, -1, 0, 1, -1, 0, 1, 0, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 36685) 21 :=
      localRoot_isPrimitive (d := 21) (by norm_num) hzeta (by norm_num)
    have h := phi21_zero hroot
    generalize zeta ^ 36685 = w at h ⊢
    unfold phi21 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 23345) [1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 23345) 33 :=
      localRoot_isPrimitive (d := 33) (by norm_num) hzeta (by norm_num)
    have h := phi33_zero hroot
    generalize zeta ^ 23345 = w at h ⊢
    unfold phi33 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 11165) [1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 11165) 69 :=
      localRoot_isPrimitive (d := 69) (by norm_num) hzeta (by norm_num)
    have h := phi69_zero hroot
    generalize zeta ^ 11165 = w at h ⊢
    unfold phi69 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 8855) [1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 8855) 87 :=
      localRoot_isPrimitive (d := 87) (by norm_num) hzeta (by norm_num)
    have h := phi87_zero hroot
    generalize zeta ^ 8855 = w at h ⊢
    unfold phi87 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulRootEvaluation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
