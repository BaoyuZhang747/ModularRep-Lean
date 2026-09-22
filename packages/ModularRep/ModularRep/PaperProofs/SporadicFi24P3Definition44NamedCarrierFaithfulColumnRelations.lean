import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLocalRelations
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnRelations
open SporadicFi24P3Definition44NamedCarrierSparseCyclotomicCertificate
variable {K : Type*} [Field K] [CharZero K]

def phi3 (w : K) : K := (1 + w + w ^ 2)

theorem phi3_zero {w : K} (hw : IsPrimitiveRoot w 3) : phi3 w = 0 := by
  have h3 : (1 + w + w ^ 2) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 3) hw
      (by norm_num : 1 < 3) (by norm_num : 3 ∣ 3)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi3
  exact h3

def phi15 (w : K) : K := (1 + (-1) * w + w ^ 3 + (-1) * w ^ 4 + w ^ 5 + (-1) * w ^ 7 + w ^ 8)

theorem phi15_zero {w : K} (hw : IsPrimitiveRoot w 15) : phi15 w = 0 := by
  have h3 : (1 + w ^ 5 + w ^ 10) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 15) hw
      (by norm_num : 1 < 3) (by norm_num : 3 ∣ 15)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  have h5 : (1 + w ^ 3 + w ^ 6 + w ^ 9 + w ^ 12) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 15) hw
      (by norm_num : 1 < 5) (by norm_num : 5 ∣ 15)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi15
  linear_combination (1 + w ^ 3) * h3 - w * h5

def phi69 (w : K) : K := (1 + (-1) * w + w ^ 3 + (-1) * w ^ 4 + w ^ 6 + (-1) * w ^ 7 + w ^ 9 + (-1) * w ^ 10 + w ^ 12 + (-1) * w ^ 13 + w ^ 15 + (-1) * w ^ 16 + w ^ 18 + (-1) * w ^ 19 + w ^ 21 + (-1) * w ^ 22 + w ^ 23 + (-1) * w ^ 25 + w ^ 26 + (-1) * w ^ 28 + w ^ 29 + (-1) * w ^ 31 + w ^ 32 + (-1) * w ^ 34 + w ^ 35 + (-1) * w ^ 37 + w ^ 38 + (-1) * w ^ 40 + w ^ 41 + (-1) * w ^ 43 + w ^ 44)

theorem phi69_zero {w : K} (hw : IsPrimitiveRoot w 69) : phi69 w = 0 := by
  have h3 : (1 + w ^ 23 + w ^ 46) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 69) hw
      (by norm_num : 1 < 3) (by norm_num : 3 ∣ 69)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  have h23 : (1 + w ^ 3 + w ^ 6 + w ^ 9 + w ^ 12 + w ^ 15 + w ^ 18 + w ^ 21 + w ^ 24 + w ^ 27 + w ^ 30 + w ^ 33 + w ^ 36 + w ^ 39 + w ^ 42 + w ^ 45 + w ^ 48 + w ^ 51 + w ^ 54 + w ^ 57 + w ^ 60 + w ^ 63 + w ^ 66) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 69) hw
      (by norm_num : 1 < 23) (by norm_num : 23 ∣ 69)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi69
  linear_combination (1 + w ^ 3 + w ^ 6 + w ^ 9 + w ^ 12 + w ^ 15 + w ^ 18 + w ^ 21) * h3 - w * h23

def phi87 (w : K) : K := (1 + (-1) * w + w ^ 3 + (-1) * w ^ 4 + w ^ 6 + (-1) * w ^ 7 + w ^ 9 + (-1) * w ^ 10 + w ^ 12 + (-1) * w ^ 13 + w ^ 15 + (-1) * w ^ 16 + w ^ 18 + (-1) * w ^ 19 + w ^ 21 + (-1) * w ^ 22 + w ^ 24 + (-1) * w ^ 25 + w ^ 27 + (-1) * w ^ 28 + w ^ 29 + (-1) * w ^ 31 + w ^ 32 + (-1) * w ^ 34 + w ^ 35 + (-1) * w ^ 37 + w ^ 38 + (-1) * w ^ 40 + w ^ 41 + (-1) * w ^ 43 + w ^ 44 + (-1) * w ^ 46 + w ^ 47 + (-1) * w ^ 49 + w ^ 50 + (-1) * w ^ 52 + w ^ 53 + (-1) * w ^ 55 + w ^ 56)

theorem phi87_zero {w : K} (hw : IsPrimitiveRoot w 87) : phi87 w = 0 := by
  have h3 : (1 + w ^ 29 + w ^ 58) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 87) hw
      (by norm_num : 1 < 3) (by norm_num : 3 ∣ 87)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  have h29 : (1 + w ^ 3 + w ^ 6 + w ^ 9 + w ^ 12 + w ^ 15 + w ^ 18 + w ^ 21 + w ^ 24 + w ^ 27 + w ^ 30 + w ^ 33 + w ^ 36 + w ^ 39 + w ^ 42 + w ^ 45 + w ^ 48 + w ^ 51 + w ^ 54 + w ^ 57 + w ^ 60 + w ^ 63 + w ^ 66 + w ^ 69 + w ^ 72 + w ^ 75 + w ^ 78 + w ^ 81 + w ^ 84) = 0 := by
    have h := ratEval_geometric_zero (by norm_num : 0 < 87) hw
      (by norm_num : 1 < 29) (by norm_num : 29 ∣ 87)
    simpa [ratEval, geometricPolynomial, Finset.sum_range_succ] using h
  unfold phi87
  linear_combination (1 + w ^ 3 + w ^ 6 + w ^ 9 + w ^ 12 + w ^ 15 + w ^ 18 + w ^ 21 + w ^ 24 + w ^ 27) * h3 - w * h29

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnRelations


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
