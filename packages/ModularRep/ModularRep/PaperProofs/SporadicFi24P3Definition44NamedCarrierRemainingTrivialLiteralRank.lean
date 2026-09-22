import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegralRowInverseCertificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation

/-! Literal ranks and exact full-column fixedness for the remaining trivial-sector blocks. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralRank

open ModularRep
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierIntegralRowInverseCertificate
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData

universe u v
variable {K : Type u} [Field K]

def dihedralIntegerRows : Fin 5 → Fin 91 → K := fun r c => (dihedralIntegerRow r c : K)

theorem dihedral_raw_eq_integer (zeta : K) (r : Fin 5) (c : Fin 91) :
    rawEvaluatedRows zeta (dihedralRow r) c = dihedralIntegerRows r c := by
  unfold rawEvaluatedRows dihedralIntegerRows
  exact (checkEq_sound _ _ _ (dihedralConstantChecks r c)).trans
    (by simp only [eval, mul_zero, add_zero])

theorem dihedralIntegerRows_fixed (r : Fin 5) (c : Fin 91) :
    dihedralIntegerRows (K := K) r (fullPerm c) = dihedralIntegerRows r c :=
  congrArg (fun z : ℤ => (z : K)) (dihedralFixedChecks r c)

def zeroRows (zeta : K) (j : Fin 2) : Fin 1 → Fin 91 → K :=
  fun r => rawEvaluatedRows zeta (zeroRow j r)

theorem zeroRows_fixed (zeta : K) (j : Fin 2) (r : Fin 1) (c : Fin 91) :
    zeroRows zeta j r (fullPerm c) = zeroRows zeta j r c := by
  have hr : r = (0 : Fin 1) := Subsingleton.elim _ _
  subst r
  unfold zeroRows rawEvaluatedRows
  rw [fullPerm_apply, rootTag_fixed, zeroPolynomial_fixed]

theorem zeroRows_unit (zeta : K) (j : Fin 2) : zeroRows zeta j 0 (57 : Fin 91) = 1 := by
  unfold zeroRows rawEvaluatedRows
  rw [zeroUnitCheck]
  simp only [eval, mul_zero, add_zero, Int.cast_one]

def singletonRankCertificate {Column : Type v}
    (rows : Fin 1 → Column → K) (pivot : Column) (hentry : rows 0 pivot ≠ 0) :
    FiniteRowRankCertificate K rows 1 where
  basisPosition := fun _ => 0
  pivotColumn := fun _ => pivot
  selectedMinorValue := rows 0 pivot
  selectedMinor_eq := Matrix.det_fin_one _
  selectedMinor_ne_zero := hentry
  coefficients := fun _ _ => 1
  reconstruct := by
    intro r
    have hr : r = (0 : Fin 1) := Subsingleton.elim _ _
    subst r
    simp only [Fin.sum_univ_one, one_smul]

def zeroRankCertificate (zeta : K) (j : Fin 2) :
    FiniteRowRankCertificate K (zeroRows zeta j) 1 :=
  singletonRankCertificate (zeroRows zeta j) 57 (by rw [zeroRows_unit]; exact one_ne_zero)

theorem zero_rows_finrank (zeta : K) (j : Fin 2) :
    Module.finrank K (Submodule.span K (Set.range (zeroRows zeta j))) = 1 :=
  (zeroRankCertificate zeta j).rows_finrank

variable [CharZero K]

def dihedralRowInverseCertificate : RowInverseCertificate K (dihedralIntegerRows (K := K)) 3 :=
  scaledIntegerRowInverseCertificate dihedralIntegerRow dihedralBasis dihedralPivot
    dihedralNumerator 1 (by decide) dihedralInverseChecks
    dihedralCoefficients dihedralReconstructionChecks

theorem dihedral_integer_rows_finrank :
    Module.finrank K (Submodule.span K (Set.range (dihedralIntegerRows (K := K)))) = 3 :=
  (rankCertificate (dihedralRowInverseCertificate (K := K))).rows_finrank

def dihedralLiteralRankCertificate (zeta : K) :
    FiniteRowRankCertificate K (fun r : Fin 5 => rawEvaluatedRows zeta (dihedralRow r)) 3 := by
  have heq : (fun r : Fin 5 => rawEvaluatedRows zeta (dihedralRow r)) =
      dihedralIntegerRows (K := K) := by
    funext r c
    exact dihedral_raw_eq_integer zeta r c
  rw [heq]
  exact rankCertificate dihedralRowInverseCertificate

theorem dihedral_literal_rows_finrank (zeta : K) :
    Module.finrank K (Submodule.span K
      (Set.range fun r : Fin 5 => rawEvaluatedRows zeta (dihedralRow r))) = 3 :=
  (dihedralLiteralRankCertificate zeta).rows_finrank

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
