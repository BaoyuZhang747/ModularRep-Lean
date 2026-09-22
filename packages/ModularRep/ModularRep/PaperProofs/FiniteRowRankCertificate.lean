import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Finite row-rank certificates

This module packages the small certificate used by finite character-table
calculations: selected rows have a nonzero square minor, and every row is an
explicit linear combination of them.  The kernel derives linear independence,
spanning, and the row rank.  No rank assertion is stored in the certificate.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs

universe u v w

/-- A certificate that a finite family of rows has rank `r`.

`selectedMinorValue` is kept separate from the determinant equality so that a
parser-facing constructor can expose the literal value printed by a program
and prove its nonvanishing independently. -/
structure FiniteRowRankCertificate
    (K : Type u) [Field K]
    {I : Type v} {J : Type w}
    (rows : I → J → K) (r : ℕ) where
  basisPosition : Fin r → I
  pivotColumn : Fin r → J
  selectedMinorValue : K
  selectedMinor_eq :
    Matrix.det (fun a c : Fin r =>
      rows (basisPosition a) (pivotColumn c)) = selectedMinorValue
  selectedMinor_ne_zero : selectedMinorValue ≠ 0
  coefficients : I → Fin r → K
  reconstruct : ∀ i,
    rows i = ∑ a, coefficients i a • rows (basisPosition a)

namespace FiniteRowRankCertificate

variable {K : Type u} [Field K]
variable {I : Type v} {J : Type w}
variable {rows : I → J → K} {r : ℕ}

/-- The selected rows, defined from their positions in the full family. -/
def basisRows (C : FiniteRowRankCertificate K rows r) : Fin r → J → K :=
  fun a => rows (C.basisPosition a)

/-- Evaluation at the selected pivot columns. -/
def selectedCoordinate (C : FiniteRowRankCertificate K rows r) :
    (J → K) →ₗ[K] (Fin r → K) where
  toFun f := fun c => f (C.pivotColumn c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The selected square minor is nonzero. -/
theorem selectedMinor_det_ne_zero
    (C : FiniteRowRankCertificate K rows r) :
    Matrix.det (fun a c : Fin r =>
      rows (C.basisPosition a) (C.pivotColumn c)) ≠ 0 := by
  rw [C.selectedMinor_eq]
  exact C.selectedMinor_ne_zero

/-- A nonzero selected minor makes the selected rows linearly independent. -/
theorem basisRows_linearIndependent
    (C : FiniteRowRankCertificate K rows r) :
    LinearIndependent K C.basisRows := by
  let M : Matrix (Fin r) (Fin r) K := fun a c =>
    rows (C.basisPosition a) (C.pivotColumn c)
  have hdet : M.det ≠ 0 := by
    simpa only [M] using C.selectedMinor_det_ne_zero
  have hrows : LinearIndependent K (fun a => M a) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hcomp :
      C.selectedCoordinate ∘ C.basisRows = fun a => M a := by
    funext a c
    rfl
  apply LinearIndependent.of_comp C.selectedCoordinate
  simpa only [hcomp] using hrows

/-- The reconstruction relations show that the selected and full row families
have the same span. -/
theorem basisRows_span
    (C : FiniteRowRankCertificate K rows r) :
    Submodule.span K (Set.range C.basisRows) =
      Submodule.span K (Set.range rows) := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨C.basisPosition a, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [C.reconstruct i]
    exact Submodule.sum_mem _ (fun a _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self a)))

/-- Kernel-checked rank conclusion obtained from the minor and reconstruction
relations. -/
theorem rows_finrank
    (C : FiniteRowRankCertificate K rows r) :
    Module.finrank K (Submodule.span K (Set.range rows)) = r := by
  rw [← C.basisRows_span]
  calc
    Module.finrank K (Submodule.span K (Set.range C.basisRows)) =
        Fintype.card (Fin r) :=
      finrank_span_eq_card C.basisRows_linearIndependent
    _ = r := Fintype.card_fin r

end FiniteRowRankCertificate

end ModularRep.PaperProofs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
