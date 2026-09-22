import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ModularRep.PaperProofs.FiniteRowRankCertificate

/-!
# A no-smuggling replay contract for the `Fi'_{24}` prime-three plus rank

In `fi24blocks.g`, the nonprincipal prime-three calculation forms a basis of
the six ordinary restriction rows, adds to each basis row its pullback by the
outer permutation of the thirty `3`-regular class coordinates, and calls
`RankMat`.  The checked-in `fi24blocks.out` prints only `l=4`, `fixed=2`, and
`free2=1`; it does not print either the restriction matrix or the regular-class
permutation.  Thus that output cannot by itself be replayed to obtain the
intermediate `plusRank` without reversing `fixed = 2 * plusRank - l`.

This file isolates the smallest honest finite check.  `replayedPlusRows` is
the exact rational six-by-thirty symmetrised matrix exposed by the focused V3
diagnostic: the first three rows are literal, the fourth repeats the third,
and the last two are their displayed half-sum.  Lean proves its row rank is
three from a nonzero three-by-three minor and the explicit reconstruction
relations.

`Fi24P3PlusRankReplaySource` is deliberately not instantiated here.  It asks
for the missing source data in a conclusion-free form: raw restriction rows,
the regular-class permutation, the equality of `row + row{regularPerm}` with
the literal replay matrix, and a finite minor-and-reconstruction certificate
for the raw rows.  It has no rank, fixed-count, Brauer-fibre, signature,
character--weight map, or cancellation field.  Once a canonical GAP output
emits enough exact data to construct this source, the kernel derives both raw
and symmetrised ranks.

Identifying these table coordinates with the literal Fischer group, its
primitive block, the chosen ordinary characters, the coefficient/root
convention, and the canonical right outer action remains external.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract

abbrev RowIndex := Fin 6
abbrev RegularClassIndex := Fin 30

/-- Zero-based form of the ordinary-row action
`[59,76,88,89,91,92] -> [59,76,88,89,92,91]`. -/
def ordinaryOuterPermutation : Equiv.Perm RowIndex :=
  Equiv.swap (4 : RowIndex) (5 : RowIndex)

/-- Zero-based form of the regular-class action: GAP positions 28 and 29 are
interchanged in the ordered thirty-element regular-class list. -/
def regularOuterPermutation : Equiv.Perm RegularClassIndex :=
  Equiv.swap (27 : RegularClassIndex) (28 : RegularClassIndex)

/-- The first three rows of the exact symmetrised restriction matrix. -/
def independentReplayedPlusRows {K : Type*} [Field K] :
    Fin 3 -> RegularClassIndex -> K := ![
  ![108468170982, 2768742, 187110, -2970, 54, 198, 432, 38, 24, -2,
    -18, 6, -8, 0, 6, 2, -10, 0, 2, 0, 4, 0, -2, 0, 0, 2, -2, 0, 0, -2],
  ![237177866772, -4907628, -210924, 3348, 1188, 180, -378, -70, 0,
    -20, 12, -12, 22, 6, 0, 2, 2, 0, 0, -2, -2, -2, 0, 0, 0, 2, -2,
    2, 2, 0],
  ![312643551654, -170586, 78246, -1242, -378, -90, 54, 28, 0, -10,
    6, 6, 14, 6, -6, -8, 4, 0, -2, 2, 2, -2, 2, 0, 0, 0, 0, 0, 0,
    -2]
]

/-- The complete six-row matrix whose row span is replayed.  Writing the
three dependent rows by their certificate relations makes the upper-rank
witness definitional rather than a hidden numerical assertion. -/
def replayedPlusRows {K : Type*} [Field K] :
    RowIndex -> RegularClassIndex -> K := ![
  independentReplayedPlusRows (K := K) 0,
  independentReplayedPlusRows (K := K) 1,
  independentReplayedPlusRows (K := K) 2,
  independentReplayedPlusRows (K := K) 2,
  fun c => (independentReplayedPlusRows (K := K) 0 c +
    independentReplayedPlusRows (K := K) 1 c +
    independentReplayedPlusRows (K := K) 2 c) / 2,
  fun c => (independentReplayedPlusRows (K := K) 0 c +
    independentReplayedPlusRows (K := K) 1 c +
    independentReplayedPlusRows (K := K) 2 c) / 2
]

def selectedRows : Fin 3 -> RowIndex := ![0, 1, 2]

def selectedColumns : Fin 3 -> RegularClassIndex := ![0, 1, 4]

/-- Evaluation at the three columns used for the nonzero minor. -/
def selectedCoordinate {K : Type*} [Field K] :
    (RegularClassIndex -> K) →ₗ[K] (Fin 3 -> K) where
  toFun f := fun c => f (selectedColumns c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The selected minor is the exact nonzero integer printed by the finite
certificate.  This is calculated from the displayed entries, not assumed. -/
theorem selectedMinor_det
    {K : Type*} [Field K] [CharZero K] :
    Matrix.det (fun (a c : Fin 3) =>
      replayedPlusRows (K := K) (selectedRows a) (selectedColumns c)) =
        (1580463033304441651200 : K) := by
  let A : Matrix (Fin 3) (Fin 3) K := fun a c =>
    replayedPlusRows (K := K) (selectedRows a) (selectedColumns c)
  have hA : A = !![
      (108468170982 : K), 2768742, 54;
      237177866772, -4907628, 1188;
      312643551654, -170586, -378] := by
    ext a c
    fin_cases a <;> fin_cases c
    · change (108468170982 : K) = 108468170982
      rfl
    · change (2768742 : K) = 2768742
      rfl
    · change (54 : K) = 54
      rfl
    · change (237177866772 : K) = 237177866772
      rfl
    · change (-4907628 : K) = -4907628
      rfl
    · change (1188 : K) = 1188
      rfl
    · change (312643551654 : K) = 312643551654
      rfl
    · change (-170586 : K) = -170586
      rfl
    · change (-378 : K) = -378
      rfl
  change Matrix.det A = (1580463033304441651200 : K)
  rw [hA, Matrix.det_fin_three]
  change
      (108468170982 : K) * (-4907628) * (-378) -
          108468170982 * 1188 * (-170586) -
        2768742 * 237177866772 * (-378) +
      2768742 * 1188 * 312643551654 +
      54 * 237177866772 * (-170586) -
      54 * (-4907628) * 312643551654 =
        (1580463033304441651200 : K)
  norm_num

theorem selectedMinor_det_ne_zero
    {K : Type*} [Field K] [CharZero K] :
    Matrix.det (fun (a c : Fin 3) =>
      replayedPlusRows (K := K) (selectedRows a) (selectedColumns c)) ≠ 0 := by
  rw [selectedMinor_det]
  norm_num

/-- Coefficients expressing all six symmetrised rows in the selected three. -/
def reconstructionCoefficients {K : Type*} [Field K] :
    RowIndex -> Fin 3 -> K := ![
  ![1, 0, 0],
  ![0, 1, 0],
  ![0, 0, 1],
  ![0, 0, 1],
  ![1 / 2, 1 / 2, 1 / 2],
  ![1 / 2, 1 / 2, 1 / 2]
]

theorem replayedPlusRows_reconstruct
    {K : Type*} [Field K] [CharZero K] (i : RowIndex) :
    replayedPlusRows (K := K) i =
      ∑ a, reconstructionCoefficients (K := K) i a •
        replayedPlusRows (K := K) (selectedRows a) := by
  funext c
  fin_cases i <;>
    simp [replayedPlusRows, reconstructionCoefficients, selectedRows,
      Fin.sum_univ_succ, Matrix.cons_val] <;> ring

theorem selectedReplayedPlusRows_linearIndependent
    {K : Type*} [Field K] [CharZero K] :
    LinearIndependent K
      (fun a => replayedPlusRows (K := K) (selectedRows a)) := by
  let M : Matrix (Fin 3) (Fin 3) K := fun a c =>
    replayedPlusRows (K := K) (selectedRows a) (selectedColumns c)
  have hdet : M.det ≠ 0 := by
    simpa only [M] using selectedMinor_det_ne_zero (K := K)
  have hrows : LinearIndependent K (fun a => M a) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hcomp :
      selectedCoordinate (K := K) ∘
          (fun a => replayedPlusRows (K := K) (selectedRows a)) =
        fun a => M a := by
    funext a c
    rfl
  apply LinearIndependent.of_comp (selectedCoordinate (K := K))
  simpa only [hcomp] using hrows

theorem replayedPlusRows_span_eq_selected
    {K : Type*} [Field K] [CharZero K] :
    Submodule.span K
        (Set.range (replayedPlusRows (K := K))) =
      Submodule.span K
        (Set.range (fun a =>
          replayedPlusRows (K := K) (selectedRows a))) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [replayedPlusRows_reconstruct i]
    exact Submodule.sum_mem _ (fun a _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self a)))
  · refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨selectedRows a, rfl⟩

/-- Kernel-checked finite conclusion: the displayed six-by-thirty
symmetrised matrix has row rank three over every characteristic-zero field. -/
theorem replayedPlusRows_finrank_eq_three
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K
      (Submodule.span K (Set.range (replayedPlusRows (K := K)))) = 3 := by
  rw [replayedPlusRows_span_eq_selected]
  calc
    Module.finrank K
        (Submodule.span K
          (Set.range (fun a =>
            replayedPlusRows (K := K) (selectedRows a)))) =
        Fintype.card (Fin 3) :=
      finrank_span_eq_card selectedReplayedPlusRows_linearIndependent
    _ = 3 := Fintype.card_fin 3

/-- Linear form of `row + row{sigma}` used to compare an arbitrary spanning
row family with the rows returned by GAP's `BaseMat`. -/
def plusPullbackLinear {K : Type*} [Field K]
    (sigma : Equiv.Perm RegularClassIndex) :
    (RegularClassIndex -> K) →ₗ[K] (RegularClassIndex -> K) where
  toFun f := fun c => f c + f (sigma c)
  map_add' f g := by
    funext c
    simp only [Pi.add_apply]
    abel
  map_smul' a f := by
    funext c
    simp [mul_add]

theorem span_plusRows_eq_map_span
    {K I : Type*} [Field K]
    (sigma : Equiv.Perm RegularClassIndex)
    (rows : I -> RegularClassIndex -> K) :
    Submodule.span K
        (Set.range (fun i => plusPullbackLinear (K := K) sigma (rows i))) =
      (Submodule.span K (Set.range rows)).map
        (plusPullbackLinear (K := K) sigma) := by
  change Submodule.span K
      (Set.range ((plusPullbackLinear (K := K) sigma) ∘ rows)) = _
  rw [Set.range_comp, Submodule.span_image]

/-- Honest source shape for attaching the finite replay to GAP output.

The finite rank certificate exposes selected row and column positions, the
literal value of the selected minor, and reconstruction coefficients.  Linear
independence, spanning, and rank are derived in the kernel.  The remaining
fields expose the regular-class permutation and the complete pointwise
symmetrised data.  None of them can be filled from a final fixed-point count
alone. -/
structure Fi24P3PlusRankReplaySource (K : Type*) [Field K] where
  restrictionRows : RowIndex -> RegularClassIndex -> K
  regularPermutation : Equiv.Perm RegularClassIndex
  regularPermutation_eq : regularPermutation = regularOuterPermutation
  symmetrised_rows_eq : ∀ i c,
    restrictionRows i c + restrictionRows i (regularPermutation c) =
      replayedPlusRows (K := K) i c
  rankCertificate : FiniteRowRankCertificate K restrictionRows 4

namespace Fi24P3PlusRankReplaySource

/-- The four selected raw rows named by the finite certificate. -/
abbrev basisRows {K : Type*} [Field K]
    (S : Fi24P3PlusRankReplaySource K) :
    Fin 4 → RegularClassIndex → K :=
  S.rankCertificate.basisRows

/-- Linear independence is checked from the selected nonzero minor. -/
theorem basisRows_linearIndependent
    {K : Type*} [Field K]
    (S : Fi24P3PlusRankReplaySource K) :
    LinearIndependent K S.basisRows :=
  S.rankCertificate.basisRows_linearIndependent

/-- The reconstruction relations prove that the selected rows span all six
raw rows. -/
theorem basisRows_span
    {K : Type*} [Field K]
    (S : Fi24P3PlusRankReplaySource K) :
    Submodule.span K (Set.range S.basisRows) =
      Submodule.span K (Set.range S.restrictionRows) :=
  S.rankCertificate.basisRows_span

/-- The raw restriction matrix has row rank four because the four `BaseMat`
rows are independent and span all six rows. -/
theorem restrictionRows_finrank_eq_four
    {K : Type*} [Field K]
    (S : Fi24P3PlusRankReplaySource K) :
    Module.finrank K
      (Submodule.span K (Set.range S.restrictionRows)) = 4 :=
  S.rankCertificate.rows_finrank

def allPlusRows {K : Type*} [Field K]
    (S : Fi24P3PlusRankReplaySource K) :
    RowIndex -> RegularClassIndex -> K :=
  fun i => plusPullbackLinear S.regularPermutation (S.restrictionRows i)

/-- These are the rows on which `fi24blocks.g` calls `RankMat`, up to replacing
the row-reduced basis by any basis with the same raw row span. -/
def basisPlusRows {K : Type*} [Field K]
    (S : Fi24P3PlusRankReplaySource K) :
    Fin 4 -> RegularClassIndex -> K :=
  fun i => plusPullbackLinear S.regularPermutation (S.basisRows i)

theorem allPlusRows_eq_replayed
    {K : Type*} [Field K]
    (S : Fi24P3PlusRankReplaySource K) :
    allPlusRows S = replayedPlusRows (K := K) := by
  funext i c
  change S.restrictionRows i c +
      S.restrictionRows i (S.regularPermutation c) = _
  exact S.symmetrised_rows_eq i c

theorem basisPlusRows_span_eq_allPlusRows_span
    {K : Type*} [Field K]
    (S : Fi24P3PlusRankReplaySource K) :
    Submodule.span K (Set.range (basisPlusRows S)) =
      Submodule.span K (Set.range (allPlusRows S)) := by
  change Submodule.span K
      (Set.range (fun i => plusPullbackLinear S.regularPermutation
        (S.basisRows i))) =
    Submodule.span K
      (Set.range (fun i => plusPullbackLinear S.regularPermutation
        (S.restrictionRows i)))
  rw [span_plusRows_eq_map_span, span_plusRows_eq_map_span,
    S.basisRows_span]

/-- The replayed counterpart of GAP's unprinted `plusRank`: it is derived
from the restriction-plus-permutation data and never from `fixed = 2`. -/
theorem basisPlusRows_finrank_eq_three
    {K : Type*} [Field K] [CharZero K]
    (S : Fi24P3PlusRankReplaySource K) :
    Module.finrank K
      (Submodule.span K (Set.range (basisPlusRows S))) = 3 := by
  rw [basisPlusRows_span_eq_allPlusRows_span, allPlusRows_eq_replayed]
  exact replayedPlusRows_finrank_eq_three

end Fi24P3PlusRankReplaySource

end ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
