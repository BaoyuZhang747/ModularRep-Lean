import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3Rows

/-! The fixed literal rows are closed under the actual column permutation.
Their common zero column will distinguish the block from the trivial character. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3BlockAction
open SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
open SporadicFi24P3V3RawRankCertificate
open SporadicFi24P3PlusRankReplayContract
variable {K : Type*} [Field K] [CharZero K]

theorem literalV3Rows_outer (E : PrimitiveTwentyNineEncoding K) :
    ∀ r c, literalV3Rows E r (regularOuterPermutation c) =
      literalV3Rows E (ordinaryOuterPermutation r) c := by
  have hfixed (r : Fin 3) (c : Fin 30) :
      literalV3FixedRow (K := K) r (regularOuterPermutation c) =
        literalV3FixedRow (K := K) r c := by
    refine Equiv.apply_swap_eq_self (v := literalV3FixedRow (K := K) r)
      (i := (27 : Fin 30)) (j := 28) ?_ c
    fin_cases r <;> rfl
  intro r c
  fin_cases r
  · change literalV3FixedRow (K := K) 0 (regularOuterPermutation c) =
      literalV3FixedRow (K := K) 0 c
    exact hfixed 0 c
  · change literalV3FixedRow (K := K) 1 (regularOuterPermutation c) =
      literalV3FixedRow (K := K) 1 c
    exact hfixed 1 c
  · change literalV3FixedRow (K := K) 2 (regularOuterPermutation c) =
      literalV3FixedRow (K := K) 2 c
    exact hfixed 2 c
  · change literalV3FixedRow (K := K) 2 (regularOuterPermutation c) =
      literalV3FixedRow (K := K) 2 c
    exact hfixed 2 c
  · change literalV3Rows E 4 (regularOuterPermutation c) = literalV3Rows E 5 c
    exact (congrFun (literalV3Rows_sixth_eq_swapped_fifth E) c).symm
  · change literalV3Rows E 5 (regularOuterPermutation c) = literalV3Rows E 4 c
    calc
      _ = literalV3Rows E 4 (regularOuterPermutation (regularOuterPermutation c)) :=
        congrFun (literalV3Rows_sixth_eq_swapped_fifth E) (regularOuterPermutation c)
      _ = _ := by
        rw [show regularOuterPermutation (regularOuterPermutation c) = c from
          Equiv.swap_apply_self (27 : Fin 30) 28 c]

theorem literalV3Rows_zero_column (E : PrimitiveTwentyNineEncoding K) :
    ∀ r, literalV3Rows E r 23 = 0 := by
  intro r
  fin_cases r
  · change (0 : K) / 2 = 0
    norm_num
  · change (0 : K) / 2 = 0
    norm_num
  · change (0 : K) / 2 = 0
    norm_num
  · change (0 : K) / 2 = 0
    norm_num
  · rfl
  · change (0 : K) / 2 + 0 / 2 + 0 / 2 - 0 = 0
    norm_num

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3BlockAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
