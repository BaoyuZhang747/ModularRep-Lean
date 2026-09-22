import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLocalRelations
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
import Mathlib.Tactic.FinCases

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRootEvaluation

open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open SporadicFi24P3Definition44NamedCarrierFaithfulLocalRelations
open SporadicFi24P3Definition44NamedCarrierTrivialLocalRelations

variable {K : Type*} [Field K] [CharZero K]

def localRoots (zeta : K) (d : Fin 7) : K := zeta ^ (10015005 / conductor d)

theorem local_modulus_zero {zeta : K} (hzeta : IsPrimitiveRoot zeta 10015005) :
    ∀ d, eval (localRoots zeta d) (modulus d) = 0 := by
  intro d
  fin_cases d
  · rfl
  · change eval (zeta ^ 2003001) [1, 1, 1, 1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 2003001) 5 :=
      localRoot_isPrimitive (d := 5) (by norm_num) hzeta (by norm_num)
    have h := phi5_zero hroot
    generalize zeta ^ 2003001 = w at h ⊢
    unfold phi5 at h
    simp only [eval, Int.cast_one, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 770385) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 770385) 13 :=
      localRoot_isPrimitive (d := 13) (by norm_num) hzeta (by norm_num)
    have h := phi13_zero hroot
    generalize zeta ^ 770385 = w at h ⊢
    unfold phi13 at h
    simp only [eval, Int.cast_one, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 476905) [1, -1, 0, 1, -1, 0, 1, 0, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 476905) 21 :=
      localRoot_isPrimitive (d := 21) (by norm_num) hzeta (by norm_num)
    have h := phi21_zero hroot
    generalize zeta ^ 476905 = w at h ⊢
    unfold phi21 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 435435) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 435435) 23 :=
      localRoot_isPrimitive (d := 23) (by norm_num) hzeta (by norm_num)
    have h := phi23_zero hroot
    generalize zeta ^ 435435 = w at h ⊢
    unfold phi23 at h
    simp only [eval, Int.cast_one, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 345345) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 345345) 29 :=
      localRoot_isPrimitive (d := 29) (by norm_num) hzeta (by norm_num)
    have h := phi29_zero hroot
    generalize zeta ^ 345345 = w at h ⊢
    unfold phi29 at h
    simp only [eval, Int.cast_one, mul_zero, add_zero]
    linear_combination h
  · change eval (zeta ^ 303485) [1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1] = 0
    have hroot : IsPrimitiveRoot (zeta ^ 303485) 33 :=
      localRoot_isPrimitive (d := 33) (by norm_num) hzeta (by norm_num)
    have h := phi33_zero hroot
    generalize zeta ^ 303485 = w at h ⊢
    unfold phi33 at h
    simp only [eval, Int.cast_zero, Int.cast_one, Int.cast_neg, mul_zero, add_zero]
    linear_combination h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRootEvaluation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
