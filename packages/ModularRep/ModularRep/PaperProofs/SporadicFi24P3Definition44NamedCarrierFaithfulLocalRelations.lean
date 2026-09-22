import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSparseCyclotomicCertificate
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLocalRelations
open SporadicFi24P3Definition44NamedCarrierSparseCyclotomicCertificate
variable {K : Type*} [Field K]

theorem localRoot_isPrimitive {N d : ℕ} {zeta : K}
    (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N) (hdN : d ∣ N) :
    IsPrimitiveRoot (zeta ^ (N / d)) d :=
  IsPrimitiveRoot.pow hN hzeta (Nat.div_mul_cancel hdN).symm

variable [CharZero K]

def phi5 (w : K) : K := (1 + w + w ^ 2 + w ^ 3 + w ^ 4)

theorem phi5_zero {w : K} (hw : IsPrimitiveRoot w 5) : phi5 w = 0 := by
  have h5 : (1 + w + w ^ 2 + w ^ 3 + w ^ 4) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 5) hw
      (by norm_num : 1 < 5) (by norm_num : 5 ∣ 5)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi5
  exact h5

def phi21 (w : K) : K := (1 + (-1) * w + w ^ 3 + (-1) * w ^ 4 + w ^ 6 + (-1) * w ^ 8 + w ^ 9 + (-1) * w ^ 11 + w ^ 12)

theorem phi21_zero {w : K} (hw : IsPrimitiveRoot w 21) : phi21 w = 0 := by
  have h3 : (1 + w ^ 7 + w ^ 14) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 21) hw
      (by norm_num : 1 < 3) (by norm_num : 3 ∣ 21)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  have h7 : (1 + w ^ 3 + w ^ 6 + w ^ 9 + w ^ 12 + w ^ 15 + w ^ 18) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 21) hw
      (by norm_num : 1 < 7) (by norm_num : 7 ∣ 21)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi21
  linear_combination h7 - (w + w ^ 4) * h3

def phi23 (w : K) : K := (1 + w + w ^ 2 + w ^ 3 + w ^ 4 + w ^ 5 + w ^ 6 + w ^ 7 + w ^ 8 + w ^ 9 + w ^ 10 + w ^ 11 + w ^ 12 + w ^ 13 + w ^ 14 + w ^ 15 + w ^ 16 + w ^ 17 + w ^ 18 + w ^ 19 + w ^ 20 + w ^ 21 + w ^ 22)

theorem phi23_zero {w : K} (hw : IsPrimitiveRoot w 23) : phi23 w = 0 := by
  have h23 : (1 + w + w ^ 2 + w ^ 3 + w ^ 4 + w ^ 5 + w ^ 6 + w ^ 7 + w ^ 8 + w ^ 9 + w ^ 10 + w ^ 11 + w ^ 12 + w ^ 13 + w ^ 14 + w ^ 15 + w ^ 16 + w ^ 17 + w ^ 18 + w ^ 19 + w ^ 20 + w ^ 21 + w ^ 22) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 23) hw
      (by norm_num : 1 < 23) (by norm_num : 23 ∣ 23)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi23
  exact h23

def phi29 (w : K) : K := (1 + w + w ^ 2 + w ^ 3 + w ^ 4 + w ^ 5 + w ^ 6 + w ^ 7 + w ^ 8 + w ^ 9 + w ^ 10 + w ^ 11 + w ^ 12 + w ^ 13 + w ^ 14 + w ^ 15 + w ^ 16 + w ^ 17 + w ^ 18 + w ^ 19 + w ^ 20 + w ^ 21 + w ^ 22 + w ^ 23 + w ^ 24 + w ^ 25 + w ^ 26 + w ^ 27 + w ^ 28)

theorem phi29_zero {w : K} (hw : IsPrimitiveRoot w 29) : phi29 w = 0 := by
  have h29 : (1 + w + w ^ 2 + w ^ 3 + w ^ 4 + w ^ 5 + w ^ 6 + w ^ 7 + w ^ 8 + w ^ 9 + w ^ 10 + w ^ 11 + w ^ 12 + w ^ 13 + w ^ 14 + w ^ 15 + w ^ 16 + w ^ 17 + w ^ 18 + w ^ 19 + w ^ 20 + w ^ 21 + w ^ 22 + w ^ 23 + w ^ 24 + w ^ 25 + w ^ 26 + w ^ 27 + w ^ 28) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 29) hw
      (by norm_num : 1 < 29) (by norm_num : 29 ∣ 29)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi29
  exact h29

def phi33 (w : K) : K := (1 + (-1) * w + w ^ 3 + (-1) * w ^ 4 + w ^ 6 + (-1) * w ^ 7 + w ^ 9 + (-1) * w ^ 10 + w ^ 11 + (-1) * w ^ 13 + w ^ 14 + (-1) * w ^ 16 + w ^ 17 + (-1) * w ^ 19 + w ^ 20)

theorem phi33_zero {w : K} (hw : IsPrimitiveRoot w 33) : phi33 w = 0 := by
  have h3 : (1 + w ^ 11 + w ^ 22) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 33) hw
      (by norm_num : 1 < 3) (by norm_num : 3 ∣ 33)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  have h11 : (1 + w ^ 3 + w ^ 6 + w ^ 9 + w ^ 12 + w ^ 15 + w ^ 18 + w ^ 21 + w ^ 24 + w ^ 27 + w ^ 30) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 33) hw
      (by norm_num : 1 < 11) (by norm_num : 11 ∣ 33)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi33
  linear_combination (1 + w ^ 3 + w ^ 6 + w ^ 9) * h3 - w * h11

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLocalRelations


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
