import ModularRep.PaperProofs.FiniteRowRankCertificate

/-! # Row-rank certificates from a selected minor inverse -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

universe u v w

structure RowInverseCertificate (K : Type u) [Field K]
    {Row : Type v} {Column : Type w} (rows : Row → Column → K) (n : ℕ) where
  basisPosition : Fin n → Row
  pivotColumn : Fin n → Column
  inverse : Matrix (Fin n) (Fin n) K
  right_inverse :
    Matrix.of (fun a c : Fin n => rows (basisPosition a) (pivotColumn c)) * inverse = 1
  coefficients : Row → Fin n → K
  reconstruct : ∀ r, rows r = ∑ a, coefficients r a • rows (basisPosition a)

variable {K : Type u} [Field K] {Row : Type v} {Column : Type w}
variable {rows : Row → Column → K} {n : ℕ}

theorem selectedMinor_det_ne_zero (C : RowInverseCertificate K rows n) :
    Matrix.det (Matrix.of (fun a c : Fin n => rows (C.basisPosition a) (C.pivotColumn c))) ≠ 0 := by
  have hdet :
      Matrix.det (Matrix.of (fun a c : Fin n => rows (C.basisPosition a) (C.pivotColumn c))) *
        Matrix.det C.inverse = 1 := by
    rw [← Matrix.det_mul, C.right_inverse, Matrix.det_one]
  intro hzero
  rw [hzero, zero_mul] at hdet
  exact zero_ne_one hdet

def rankCertificate (C : RowInverseCertificate K rows n) :
    FiniteRowRankCertificate K rows n where
  basisPosition := C.basisPosition
  pivotColumn := C.pivotColumn
  selectedMinorValue :=
    Matrix.det (Matrix.of (fun a c : Fin n => rows (C.basisPosition a) (C.pivotColumn c)))
  selectedMinor_eq := rfl
  selectedMinor_ne_zero := selectedMinor_det_ne_zero C
  coefficients := C.coefficients
  reconstruct := C.reconstruct

theorem rows_finrank (C : RowInverseCertificate K rows n) :
    Module.finrank K (Submodule.span K (Set.range rows)) = n :=
  (rankCertificate C).rows_finrank

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRowInverseCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
