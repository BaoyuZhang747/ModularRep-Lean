import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

noncomputable section
open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierScalarColumnExpansion

open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

universe u v w x
variable {K : Type u} [Field K]
variable {Row : Type v} {Representative : Type w} {Column : Type x}

/-- A descriptor gives either zero or a scalar multiple of one representative column. -/
def columnExpansion (column : Column → Option (Representative × K)) :
    (Representative → K) →ₗ[K] (Column → K) where
  toFun f c := match column c with
    | none => 0
    | some js => js.2 * f js.1
  map_add' f g := by
    funext c
    cases h : column c <;> simp [h, mul_add]
  map_smul' a f := by
    funext c
    cases h : column c <;> simp [h, mul_left_comm]

theorem columnExpansion_apply_none
    (column : Column → Option (Representative × K))
    (f : Representative → K) {c : Column} (hc : column c = none) :
    columnExpansion column f c = 0 := by
  change (match column c with | none => 0 | some js => js.2 * f js.1) = 0
  rw [hc]

theorem columnExpansion_apply_some
    (column : Column → Option (Representative × K))
    (f : Representative → K) {c : Column} {j : Representative} {s : K}
    (hc : column c = some (j, s)) :
    columnExpansion column f c = s * f j := by
  change (match column c with | none => 0 | some js => js.2 * f js.1) = _
  rw [hc]

theorem columnExpansion_reconstruct
    (column : Column → Option (Representative × K))
    (rows : Row → Representative → K) {n : ℕ}
    (basisPosition : Fin n → Row) (coefficients : Row → Fin n → K)
    (hrec : ∀ r, rows r = ∑ a, coefficients r a • rows (basisPosition a))
    (r : Row) :
    columnExpansion column (rows r) =
      ∑ a, coefficients r a • columnExpansion column (rows (basisPosition a)) := by
  rw [hrec r, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact map_smul (columnExpansion column) (coefficients r a) (rows (basisPosition a))

def expandedRowInverseCertificate
    (column : Column → Option (Representative × K))
    (representativeColumn : Representative → Column)
    (hrepresentative : ∀ j, column (representativeColumn j) = some (j, 1))
    {rows : Row → Representative → K} {n : ℕ}
    (C : RowInverseCertificate K rows n) :
    RowInverseCertificate K
      (fun r => columnExpansion column (rows r)) n where
  basisPosition := C.basisPosition
  pivotColumn := fun a => representativeColumn (C.pivotColumn a)
  inverse := C.inverse
  right_inverse := by
    have hminor :
        Matrix.of (fun a c : Fin n =>
          columnExpansion column (rows (C.basisPosition a))
            (representativeColumn (C.pivotColumn c))) =
          Matrix.of (fun a c : Fin n =>
            rows (C.basisPosition a) (C.pivotColumn c)) := by
      ext a c
      change columnExpansion column (rows (C.basisPosition a))
        (representativeColumn (C.pivotColumn c)) =
          rows (C.basisPosition a) (C.pivotColumn c)
      rw [columnExpansion_apply_some column _ (hrepresentative (C.pivotColumn c))]
      exact one_mul _
    rw [hminor]
    exact C.right_inverse
  coefficients := C.coefficients
  reconstruct := columnExpansion_reconstruct column rows
    C.basisPosition C.coefficients C.reconstruct

def expandedRankCertificate
    (column : Column → Option (Representative × K))
    (representativeColumn : Representative → Column)
    (hrepresentative : ∀ j, column (representativeColumn j) = some (j, 1))
    {rows : Row → Representative → K} {n : ℕ}
    (C : RowInverseCertificate K rows n) :
    FiniteRowRankCertificate K
      (fun r => columnExpansion column (rows r)) n :=
  rankCertificate (expandedRowInverseCertificate column representativeColumn hrepresentative C)

theorem expandedRows_finrank
    (column : Column → Option (Representative × K))
    (representativeColumn : Representative → Column)
    (hrepresentative : ∀ j, column (representativeColumn j) = some (j, 1))
    {rows : Row → Representative → K} {n : ℕ}
    (C : RowInverseCertificate K rows n) :
    Module.finrank K
      (Submodule.span K
        (Set.range fun r => columnExpansion column (rows r))) = n :=
  (expandedRankCertificate column representativeColumn hrepresentative C).rows_finrank

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierScalarColumnExpansion


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
