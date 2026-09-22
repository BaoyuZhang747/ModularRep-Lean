import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ModularRep.PaperProofs.FiniteRowRankCertificate
import ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract

/-!
# The V3 raw restriction-row rank certificate for `Fi'_{24}` at three

The finite V3 restriction-row certificate
records six ordinary restriction rows
in a common conductor-29 encoding. It
selects rows `[1,2,3,5]`, pivot columns `[1,2,5,28]`, prints the resulting
cyclotomic determinant, and gives six reconstruction relations.

This module transcribes that finite artefact.  Its only cyclotomic datum is a
chosen primitive 29th root.  The selected determinant is calculated from the
literal entries.  Its nonvanishing is proved in Lean: after the relation
`1 + zeta + ... + zeta^28 = 0`, the printed determinant contains the value of
a nonzero polynomial of degree at most 27 at `zeta`; the minimal polynomial
of `zeta` has degree 28.

The resulting `FiniteRowRankCertificate` stores only the selected positions,
the printed minor, its proved nonvanishing, and the six reconstruction
relations.  Linear independence, equality of spans, and rank four are all
downstream kernel theorems from `FiniteRowRankCertificate.lean`.

The V3 transcript is a development artefact, not the canonical character
table supplement.  `CanonicalSupplementV3Binding` therefore keeps the
identification of the canonical restriction rows with this transcription as
an explicit source field.  Only after that binding is supplied do we build a
`Fi24P3PlusRankReplaySource`.
-/

noncomputable section

open scoped BigOperators MonoidAlgebra
open Polynomial

namespace ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate

open ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract

universe u

/-- The exact common-conductor datum used by the V3 serialisation. -/
structure PrimitiveTwentyNineEncoding (K : Type u) [Field K] [CharZero K] where
  zeta : K
  primitive : IsPrimitiveRoot zeta 29

variable {K : Type u} [Field K] [CharZero K]

/-- Exponents carrying coefficient `-98778939581527603200` in the printed
minor.  This is also the exponent set in row 5, column 28. -/
def negativeExponents : Finset ℕ :=
  {1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28}

/-- Exponents carrying coefficient `+98778939581527603200` in the printed
minor.  Together with `negativeExponents` these partition `1,...,28`. -/
def positiveExponents : Finset ℕ :=
  {2, 3, 8, 10, 11, 12, 14, 15, 17, 18, 19, 21, 26, 27}

/-- The two literal cyclotomic sums appearing in rows 5 and 6. -/
def negativePowerSum (E : PrimitiveTwentyNineEncoding K) : K :=
  Finset.sum negativeExponents fun e ↦ E.zeta ^ e

def positivePowerSum (E : PrimitiveTwentyNineEncoding K) : K :=
  Finset.sum positiveExponents fun e ↦ E.zeta ^ e

private theorem all_twentyNine_powers_sum_zero
    (E : PrimitiveTwentyNineEncoding K) :
    Finset.sum (Finset.range 29) (fun e ↦ E.zeta ^ e) = 0 := by
  letI : Fact (Nat.Prime 29) := ⟨by decide⟩
  have hroot := E.primitive.isRoot_cyclotomic (by norm_num : 0 < 29)
  simpa [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime,
    Polynomial.eval_finset_sum] using hroot

/-- The two printed exponent lists, together with exponent zero, are all
powers below 29. -/
theorem one_add_negative_add_positive_eq_zero
    (E : PrimitiveTwentyNineEncoding K) :
    1 + negativePowerSum E + positivePowerSum E = 0 := by
  have h := all_twentyNine_powers_sum_zero E
  norm_num [Finset.sum_range_succ, negativePowerSum, positivePowerSum,
    negativeExponents, positiveExponents] at h ⊢
  linear_combination h

/-- The literal V3 value of the selected minor.  The coefficient at every
power is exactly the one printed by `RAW_NONZERO_MINOR_DETERMINANT`. -/
def printedRawMinorValue (E : PrimitiveTwentyNineEncoding K) : K :=
  (98778939581527603200 : K) *
    (positivePowerSum E - negativePowerSum E)

/-- A degree-at-most-27 rational polynomial whose value at `zeta` is the
printed signed power sum. -/
private def reducedMinorPolynomial : ℚ[X] :=
  C 1 + C 2 * Finset.sum positiveExponents (fun e ↦ X ^ e)

private theorem reducedMinorPolynomial_ne_zero :
    reducedMinorPolynomial ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun P : ℚ[X] ↦ P.coeff 0) hzero
  norm_num [reducedMinorPolynomial, positiveExponents] at hcoeff

private theorem reducedMinorPolynomial_degree_lt_twentyEight :
    reducedMinorPolynomial.degree < (28 : WithBot ℕ) := by
  unfold reducedMinorPolynomial
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · rw [degree_C (by norm_num : (1 : ℚ) ≠ 0)]
    norm_num
  · refine (degree_mul_le _ _).trans_lt ?_
    rw [degree_C (by norm_num : (2 : ℚ) ≠ 0), zero_add]
    refine (degree_sum_le positiveExponents (fun e : ℕ ↦ (X : ℚ[X]) ^ e)).trans_lt ?_
    rw [Finset.sup_lt_iff]
    · intro e he
      rw [degree_X_pow]
      exact WithBot.coe_lt_coe.mpr (by
        simp [positiveExponents] at he
        rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num)
    · exact WithBot.bot_lt_coe 28

private theorem reducedMinorPolynomial_aeval
    (E : PrimitiveTwentyNineEncoding K) :
    aeval E.zeta reducedMinorPolynomial =
      1 + 2 * positivePowerSum E := by
  rw [reducedMinorPolynomial, map_add, aeval_C, map_mul, aeval_C]
  simp only [positivePowerSum, positiveExponents, Finset.sum_insert,
    Finset.sum_singleton, map_sum, map_add, map_pow, aeval_X]
  norm_num

/-- The signed root sum in the printed determinant is nonzero.  If it
vanished, `reducedMinorPolynomial` would give a nonzero relation of degree
below 28 for a primitive 29th root, contradicting its cyclotomic minimal
polynomial. -/
theorem positive_sub_negative_ne_zero
    (E : PrimitiveTwentyNineEncoding K) :
    positivePowerSum E - negativePowerSum E ≠ 0 := by
  have hreduced :
      positivePowerSum E - negativePowerSum E =
        1 + 2 * positivePowerSum E := by
    linear_combination -(one_add_negative_add_positive_eq_zero E)
  rw [hreduced]
  intro hzero
  have heval : aeval E.zeta reducedMinorPolynomial = 0 := by
    rw [reducedMinorPolynomial_aeval E]
    exact hzero
  have hdegree := minpoly.degree_le_of_ne_zero ℚ E.zeta
    reducedMinorPolynomial_ne_zero heval
  have hmin := Polynomial.cyclotomic_eq_minpoly_rat E.primitive
    (by norm_num : 0 < 29)
  rw [← hmin] at hdegree
  letI : Fact (Nat.Prime 29) := ⟨by decide⟩
  have hcyclotomicDegree :
      (cyclotomic 29 ℚ).degree = (28 : WithBot ℕ) := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime (by decide)]
    norm_num
  rw [hcyclotomicDegree] at hdegree
  exact (not_le_of_gt reducedMinorPolynomial_degree_lt_twentyEight) hdegree

/-- The exact printed minor is nonzero; the large rational coefficient is
nonzero by characteristic zero and the cyclotomic factor is handled above. -/
theorem printedRawMinorValue_ne_zero
    (E : PrimitiveTwentyNineEncoding K) :
    printedRawMinorValue E ≠ 0 := by
  rw [printedRawMinorValue]
  exact mul_ne_zero (by norm_num) (positive_sub_negative_ne_zero E)

/-! ## The sixteen selected entries and six reconstruction relations -/

abbrev RowIndex :=
  SporadicFi24P3PlusRankReplayContract.RowIndex

abbrev RegularClassIndex :=
  SporadicFi24P3PlusRankReplayContract.RegularClassIndex

/-- Zero-based transcription of the printed row positions `[1,2,3,5]`. -/
def selectedOriginalRows : Fin 4 → RowIndex := ![0, 1, 2, 4]

/-- Zero-based transcription of the printed pivot columns `[1,2,5,28]`. -/
def selectedPivotColumns : Fin 4 → RegularClassIndex := ![0, 1, 4, 27]

/-- The sixteen literal entries at the selected rows and columns.  The only
non-rational entry is row 5, column 28, encoded exactly as the negative sum
of the fourteen powers printed by the V3 artefact. -/
def selectedMinorMatrix (E : PrimitiveTwentyNineEncoding K) :
    Matrix (Fin 4) (Fin 4) K := !![
  54234085491, 1384371, 27, 0;
  118588933386, -2453814, 594, 1;
  156321775827, -85293, -189, 0;
  164572397352, -577368, 216, -negativePowerSum E
]

private def constantCofactorMatrix : Matrix (Fin 3) (Fin 3) K := !![
  54234085491, 1384371, 27;
  156321775827, -85293, -189;
  164572397352, -577368, 216
]

private def powerCofactorMatrix : Matrix (Fin 3) (Fin 3) K := !![
  54234085491, 1384371, 27;
  118588933386, -2453814, 594;
  156321775827, -85293, -189
]

private theorem constantCofactorMatrix_det :
    Matrix.det (constantCofactorMatrix (K := K)) =
      (-98778939581527603200 : K) := by
  rw [Matrix.det_fin_three]
  change
    (54234085491 : K) * (-85293) * 216 -
          54234085491 * (-189) * (-577368) -
        1384371 * 156321775827 * 216 +
      1384371 * (-189) * 164572397352 +
    27 * 156321775827 * (-577368) -
      27 * (-85293) * 164572397352 =
      -98778939581527603200
  norm_num

private theorem powerCofactorMatrix_det :
    Matrix.det (powerCofactorMatrix (K := K)) =
      (197557879163055206400 : K) := by
  rw [Matrix.det_fin_three]
  change
    (54234085491 : K) * (-2453814) * (-189) -
          54234085491 * 594 * (-85293) -
        1384371 * 118588933386 * (-189) +
      1384371 * 594 * 156321775827 +
    27 * 118588933386 * (-85293) -
      27 * (-2453814) * 156321775827 =
      197557879163055206400
  norm_num

/-- Direct calculation of the printed four-by-four minor.  The determinant
first simplifies to `c * (-1 - 2 A)` for the negative exponent sum `A`; the
primitive-root relation identifies this with the printed `c * (B - A)`. -/
theorem selectedMinorMatrix_det
    (E : PrimitiveTwentyNineEncoding K) :
    Matrix.det (selectedMinorMatrix E) = printedRawMinorValue E := by
  have hconstant :
      (selectedMinorMatrix E).submatrix
          (Fin.succ (0 : Fin 3)).succAbove
            (3 : Fin 4).succAbove =
        constantCofactorMatrix := by
    ext a c
    fin_cases a <;> fin_cases c <;> rfl
  have hpower :
      (selectedMinorMatrix E).submatrix
          ((0 : Fin 1).succ.succ.succ).succAbove
            (3 : Fin 4).succAbove =
        powerCofactorMatrix := by
    ext a c
    fin_cases a <;> fin_cases c <;> rfl
  have hconstantDet :
      Matrix.det ((selectedMinorMatrix E).submatrix
        (Fin.succ (0 : Fin 3)).succAbove (3 : Fin 4).succAbove) =
          (-98778939581527603200 : K) := by
    rw [hconstant, constantCofactorMatrix_det]
  have hpowerDet :
      Matrix.det ((selectedMinorMatrix E).submatrix
        ((0 : Fin 1).succ.succ.succ).succAbove
          (3 : Fin 4).succAbove) =
          (197557879163055206400 : K) := by
    rw [hpower, powerCofactorMatrix_det]
  have hentry0 : selectedMinorMatrix E 0 3 = 0 := rfl
  have hentry1 :
      selectedMinorMatrix E (Fin.succ (0 : Fin 3)) 3 = 1 := rfl
  have hentry2 :
      selectedMinorMatrix E ((0 : Fin 2).succ.succ) 3 = 0 := rfl
  have hentry3 :
      selectedMinorMatrix E ((0 : Fin 1).succ.succ.succ) 3 =
        -negativePowerSum E := rfl
  rw [Matrix.det_succ_column (selectedMinorMatrix E) (3 : Fin 4)]
  simp only [Fin.sum_univ_succ]
  rw [hentry0, hentry1, hentry2, hentry3, hconstantDet, hpowerDet]
  simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul]
  rw [printedRawMinorValue]
  norm_num [Fin.val_succ]
  linear_combination
    (-98778939581527603200 : K) *
      one_add_negative_add_positive_eq_zero E

/-- The narrow V3 GAP certificate attached to six actual row functions.
The single matrix equality is precisely the sixteen selected entries.  The
only nontrivial reconstruction relations are the printed equalities for rows
4 and 6; the other four selected/or repeated rows need no source rank fact. -/
structure V3RawRowPacket
    (E : PrimitiveTwentyNineEncoding K)
    (rows : RowIndex → RegularClassIndex → K) where
  selectedEntries : ∀ a c,
    rows (selectedOriginalRows a) (selectedPivotColumns c) =
      selectedMinorMatrix E a c
  row4_eq_row3 : rows 3 = rows 2
  row6_eq : rows 5 = rows 0 + rows 1 + rows 2 - rows 4

/-- The six coefficient vectors printed by
`RAW_ROW_RELATION_COEFFICIENTS`. -/
def reconstructionCoefficients : RowIndex → Fin 4 → K := ![
  ![1, 0, 0, 0],
  ![0, 1, 0, 0],
  ![0, 0, 1, 0],
  ![0, 0, 1, 0],
  ![0, 0, 0, 1],
  ![1, 1, 1, -1]
]

namespace V3RawRowPacket

variable {E : PrimitiveTwentyNineEncoding K}
variable {rows : RowIndex → RegularClassIndex → K}

/-- The six printed row relations, expanded as the linear combinations
required by `FiniteRowRankCertificate`. -/
theorem reconstruct (S : V3RawRowPacket E rows) (i : RowIndex) :
    rows i = ∑ a, reconstructionCoefficients (K := K) i a •
      rows (selectedOriginalRows a) := by
  fin_cases i
  · funext c
    simp [reconstructionCoefficients, selectedOriginalRows,
      Fin.sum_univ_succ]
  · funext c
    simp [reconstructionCoefficients, selectedOriginalRows,
      Fin.sum_univ_succ]
  · funext c
    simp [reconstructionCoefficients, selectedOriginalRows,
      Fin.sum_univ_succ]
  · change rows 3 = _
    rw [S.row4_eq_row3]
    funext c
    simp [reconstructionCoefficients, selectedOriginalRows,
      Fin.sum_univ_succ]
  · funext c
    simp [reconstructionCoefficients, selectedOriginalRows,
      Fin.sum_univ_succ]
  · change rows 5 = _
    rw [S.row6_eq]
    funext c
    simp [reconstructionCoefficients, selectedOriginalRows,
      Fin.sum_univ_succ]
    ring

/-- The production rank certificate built from only the sixteen selected
entries, the proved cyclotomic minor, and the six simple row relations. -/
def rankCertificate (S : V3RawRowPacket E rows) :
    FiniteRowRankCertificate K rows 4 where
  basisPosition := selectedOriginalRows
  pivotColumn := selectedPivotColumns
  selectedMinorValue := printedRawMinorValue E
  selectedMinor_eq := by
    have hmatrix :
        (fun a c : Fin 4 ↦
          rows (selectedOriginalRows a) (selectedPivotColumns c)) =
          selectedMinorMatrix E := by
      funext a c
      exact S.selectedEntries a c
    rw [hmatrix]
    exact selectedMinorMatrix_det E
  selectedMinor_ne_zero := printedRawMinorValue_ne_zero E
  coefficients := reconstructionCoefficients (K := K)
  reconstruct := reconstruct S

/-- Kernel-derived independence of the four selected original rows. -/
theorem selectedOriginalRows_linearIndependent
    (S : V3RawRowPacket E rows) :
    LinearIndependent K S.rankCertificate.basisRows :=
  S.rankCertificate.basisRows_linearIndependent

/-- Kernel-derived equality of the selected and complete row spans. -/
theorem selectedOriginalRows_span
    (S : V3RawRowPacket E rows) :
    Submodule.span K (Set.range S.rankCertificate.basisRows) =
      Submodule.span K (Set.range rows) :=
  S.rankCertificate.basisRows_span

/-- Kernel-derived raw row rank.  No rank assertion is a field of the V3
packet or of the canonical binding below. -/
theorem rows_finrank_eq_four
    (S : V3RawRowPacket E rows) :
    Module.finrank K (Submodule.span K (Set.range rows)) = 4 :=
  S.rankCertificate.rows_finrank

end V3RawRowPacket

/-! ## Explicit binding to the canonical supplement and replay adapter -/

/-- The sole bridge that may identify the development V3 evidence with the
canonical Fischer supplement used by the production proof.  It fixes the
actual six restriction-row functions, attaches the narrow V3 certificate to
those very functions, and records the full pointwise symmetrisation check
printed by the artefact.  It contains no independence, span, or rank field. -/
structure CanonicalSupplementV3Binding
    (E : PrimitiveTwentyNineEncoding K) where
  restrictionRows : RowIndex → RegularClassIndex → K
  rawPacket : V3RawRowPacket E restrictionRows
  symmetrised_rows_eq : ∀ i c,
    restrictionRows i c +
        restrictionRows i (regularOuterPermutation c) =
      replayedPlusRows (K := K) i c

namespace CanonicalSupplementV3Binding

/-- Once the explicit canonical-supplement binding is supplied, all fields
of the existing plus-rank replay source are available.  The regular class
permutation is fixed literally; raw rank remains a kernel conclusion from
`rawPacket.rankCertificate`. -/
def toPlusRankReplaySource
    {E : PrimitiveTwentyNineEncoding K}
    (B : CanonicalSupplementV3Binding E) :
    Fi24P3PlusRankReplaySource K where
  restrictionRows := B.restrictionRows
  regularPermutation := regularOuterPermutation
  regularPermutation_eq := rfl
  symmetrised_rows_eq := B.symmetrised_rows_eq
  rankCertificate := B.rawPacket.rankCertificate

end CanonicalSupplementV3Binding

end ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
