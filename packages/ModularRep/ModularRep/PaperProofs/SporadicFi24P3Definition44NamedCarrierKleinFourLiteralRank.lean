import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegralRowInverseCertificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation

/-! Rank certificates for the four original Klein-four-block rows. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourLiteralRank

open ModularRep
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierIntegralRowInverseCertificate
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation

universe u
variable {K : Type u} [Field K]

def integerRows : Fin 4 → Fin 91 → K := fun r c => (integerRow r c : K)

theorem selected_raw_eq_integer (zeta : K) (r : Fin 4) (c : Fin 91) :
    rawEvaluatedRows zeta (selectedRow r) c = integerRows r c := by
  unfold rawEvaluatedRows integerRows
  exact (checkEq_sound _ _ _ (constantChecks r c)).trans (by simp only [eval, mul_zero, add_zero])

theorem integerRows_action (r : Fin 4) (c : Fin 91) :
    integerRows (K := K) r (fullPerm c) = integerRows (rowImage r) c := by
  exact congrArg (fun z : ℤ => (z : K)) (rowActionChecks r c)

variable [CharZero K]

def integerRawCertificate : RowInverseCertificate K (integerRows (K := K)) 3 :=
  scaledIntegerRowInverseCertificate integerRow rawBasis rawPivot rawNumerator 9
    (by decide) rawInverseChecks rawCoefficients rawReconstructionChecks

def integerPlusCertificate :
    RowInverseCertificate K (fun r c => (plusIntegerRow r c : K)) 2 :=
  scaledIntegerRowInverseCertificate plusIntegerRow plusBasis plusPivot plusNumerator 2
    (by decide) plusInverseChecks plusCoefficients plusReconstructionChecks

theorem integer_rows_finrank :
    Module.finrank K (Submodule.span K (Set.range (integerRows (K := K)))) = 3 :=
  (rankCertificate (integerRawCertificate (K := K))).rows_finrank

theorem integer_plus_rows_finrank :
    Module.finrank K (Submodule.span K (Set.range fun r c =>
      integerRows (K := K) r c + integerRows r (fullPerm c))) = 2 := by
  have heq : (fun r c => integerRows (K := K) r c + integerRows r (fullPerm c)) =
      (fun r c => (plusIntegerRow r c : K)) := by
    funext r c
    simp only [plusIntegerRow, integerRows, Int.cast_add]
    rfl
  rw [heq]
  exact (rankCertificate (integerPlusCertificate (K := K))).rows_finrank

def selectedRawCertificate (zeta : K) :
    RowInverseCertificate K (fun r : Fin 4 => rawEvaluatedRows zeta (selectedRow r)) 3 := by
  have heq : (fun r : Fin 4 => rawEvaluatedRows zeta (selectedRow r)) = integerRows := by
    funext r c
    exact selected_raw_eq_integer zeta r c
  rw [heq]
  exact integerRawCertificate

theorem literal_rows_finrank (zeta : K) :
    Module.finrank K (Submodule.span K
      (Set.range fun r : Fin 4 => rawEvaluatedRows zeta (selectedRow r))) = 3 :=
  (rankCertificate (selectedRawCertificate zeta)).rows_finrank

theorem literal_plus_rows_finrank (zeta : K) :
    Module.finrank K (Submodule.span K (Set.range fun r : Fin 4 => fun c =>
      rawEvaluatedRows zeta (selectedRow r) c +
        rawEvaluatedRows zeta (selectedRow r) (fullPerm c))) = 2 := by
  have heq : (fun r : Fin 4 => fun c =>
      rawEvaluatedRows zeta (selectedRow r) c +
        rawEvaluatedRows zeta (selectedRow r) (fullPerm c)) =
      (fun r c => integerRows (K := K) r c + integerRows r (fullPerm c)) := by
    funext r c
    exact congrArg₂ (fun x y : K => x + y)
      (selected_raw_eq_integer zeta r c) (selected_raw_eq_integer zeta r (fullPerm c))
  rw [heq]
  exact integer_plus_rows_finrank

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourLiteralRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
