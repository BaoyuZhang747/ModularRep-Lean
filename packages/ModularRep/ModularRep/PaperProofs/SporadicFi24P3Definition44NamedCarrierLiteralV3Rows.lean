import ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate
import Mathlib.Tactic.LinearCombination

/-! Literal transcription of the preserved six-by-thirty V3 export.
This proves finite coordinate identities only. Identification with actual
ordinary characters, the canonical supplement, and regular representatives
remains external; no canonical computational output is changed here. -/

noncomputable section
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
open SporadicFi24P3V3RawRankCertificate
open SporadicFi24P3PlusRankReplayContract
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The first three exported rows, recovered from their accepted doubles. -/
def literalV3FixedRow (r : Fin 3) : Fin 30 → K :=
  fun c => independentReplayedPlusRows (K := K) r c / 2

/-- The fifth ordinary restriction row of the export. -/
def literalV3Row4 (E : PrimitiveTwentyNineEncoding K) : Fin 30 → K := ![
  164572397352, -577368, 13608, -216, 216,
  72, 27, -1, 6, -8, 0, 0, 7, 3, 0,
  -1, -1, 0, 0, 0, 1, -1, 0, 0, 0,
  1, -1, -negativePowerSum E, -positivePowerSum E, -1
]

def literalV3Rows (E : PrimitiveTwentyNineEncoding K) : Fin 6 → Fin 30 → K := ![
  literalV3FixedRow (K := K) 0,
  literalV3FixedRow (K := K) 1,
  literalV3FixedRow (K := K) 2,
  literalV3FixedRow (K := K) 2,
  literalV3Row4 E,
  literalV3FixedRow (K := K) 0 + literalV3FixedRow (K := K) 1 +
    literalV3FixedRow (K := K) 2 - literalV3Row4 E
]

theorem literalV3Rows_selectedEntries (E : PrimitiveTwentyNineEncoding K) :
    ∀ a c : Fin 4,
      literalV3Rows E (selectedOriginalRows a) (selectedPivotColumns c) =
        selectedMinorMatrix E a c := by
  intro a c
  fin_cases a <;> fin_cases c
  · change ((108468170982 : K) / 2) = (54234085491 : K)
    norm_num
  · change ((2768742 : K) / 2) = (1384371 : K)
    norm_num
  · change ((54 : K) / 2) = (27 : K)
    norm_num
  · change ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((237177866772 : K) / 2) = (118588933386 : K)
    norm_num
  · change ((-4907628 : K) / 2) = (-2453814 : K)
    norm_num
  · change ((1188 : K) / 2) = (594 : K)
    norm_num
  · change ((2 : K) / 2) = (1 : K)
    norm_num
  · change ((312643551654 : K) / 2) = (156321775827 : K)
    norm_num
  · change ((-170586 : K) / 2) = (-85293 : K)
    norm_num
  · change ((-378 : K) / 2) = (-189 : K)
    norm_num
  · change ((0 : K) / 2) = (0 : K)
    norm_num
  · change (164572397352 : K) = (164572397352 : K)
    norm_num
  · change (-577368 : K) = (-577368 : K)
    norm_num
  · change (216 : K) = (216 : K)
    norm_num
  · change (-negativePowerSum E) = (-negativePowerSum E)
    norm_num

theorem literalV3RawPacket (E : PrimitiveTwentyNineEncoding K) :
    V3RawRowPacket E (literalV3Rows E) :=
  ⟨literalV3Rows_selectedEntries E, rfl, rfl⟩

theorem literalV3Rows_sixth_eq_swapped_fifth (E : PrimitiveTwentyNineEncoding K) :
    literalV3Rows E 5 = fun c => literalV3Rows E 4 (regularOuterPermutation c) := by
  have h := one_add_negative_add_positive_eq_zero E
  funext c
  fin_cases c
  · change ((((108468170982 : K) / 2) + ((237177866772 : K) / 2) + ((312643551654 : K) / 2)) - (164572397352 : K)) = (164572397352 : K)
    norm_num
  · change ((((2768742 : K) / 2) + ((-4907628 : K) / 2) + ((-170586 : K) / 2)) - (-577368 : K)) = (-577368 : K)
    norm_num
  · change ((((187110 : K) / 2) + ((-210924 : K) / 2) + ((78246 : K) / 2)) - (13608 : K)) = (13608 : K)
    norm_num
  · change ((((-2970 : K) / 2) + ((3348 : K) / 2) + ((-1242 : K) / 2)) - (-216 : K)) = (-216 : K)
    norm_num
  · change ((((54 : K) / 2) + ((1188 : K) / 2) + ((-378 : K) / 2)) - (216 : K)) = (216 : K)
    norm_num
  · change ((((198 : K) / 2) + ((180 : K) / 2) + ((-90 : K) / 2)) - (72 : K)) = (72 : K)
    norm_num
  · change ((((432 : K) / 2) + ((-378 : K) / 2) + ((54 : K) / 2)) - (27 : K)) = (27 : K)
    norm_num
  · change ((((38 : K) / 2) + ((-70 : K) / 2) + ((28 : K) / 2)) - (-1 : K)) = (-1 : K)
    norm_num
  · change ((((24 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (6 : K)) = (6 : K)
    norm_num
  · change ((((-2 : K) / 2) + ((-20 : K) / 2) + ((-10 : K) / 2)) - (-8 : K)) = (-8 : K)
    norm_num
  · change ((((-18 : K) / 2) + ((12 : K) / 2) + ((6 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((6 : K) / 2) + ((-12 : K) / 2) + ((6 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((-8 : K) / 2) + ((22 : K) / 2) + ((14 : K) / 2)) - (7 : K)) = (7 : K)
    norm_num
  · change ((((0 : K) / 2) + ((6 : K) / 2) + ((6 : K) / 2)) - (3 : K)) = (3 : K)
    norm_num
  · change ((((6 : K) / 2) + ((0 : K) / 2) + ((-6 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((2 : K) / 2) + ((2 : K) / 2) + ((-8 : K) / 2)) - (-1 : K)) = (-1 : K)
    norm_num
  · change ((((-10 : K) / 2) + ((2 : K) / 2) + ((4 : K) / 2)) - (-1 : K)) = (-1 : K)
    norm_num
  · change ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((2 : K) / 2) + ((0 : K) / 2) + ((-2 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((0 : K) / 2) + ((-2 : K) / 2) + ((2 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((4 : K) / 2) + ((-2 : K) / 2) + ((2 : K) / 2)) - (1 : K)) = (1 : K)
    norm_num
  · change ((((0 : K) / 2) + ((-2 : K) / 2) + ((-2 : K) / 2)) - (-1 : K)) = (-1 : K)
    norm_num
  · change ((((-2 : K) / 2) + ((0 : K) / 2) + ((2 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) = (0 : K)
    norm_num
  · change ((((2 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (1 : K)) = (1 : K)
    norm_num
  · change ((((-2 : K) / 2) + ((-2 : K) / 2) + ((0 : K) / 2)) - (-1 : K)) = (-1 : K)
    norm_num
  · change ((((0 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (-negativePowerSum E)) = (-positivePowerSum E)
    norm_num
    linear_combination h
  · change ((((0 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (-positivePowerSum E)) = (-negativePowerSum E)
    norm_num
    linear_combination h
  · change ((((-2 : K) / 2) + ((0 : K) / 2) + ((-2 : K) / 2)) - (-1 : K)) = (-1 : K)
    norm_num

theorem literalV3Rows_symmetrised (E : PrimitiveTwentyNineEncoding K) :
    ∀ r : Fin 6, ∀ c : Fin 30,
      literalV3Rows E r c + literalV3Rows E r (regularOuterPermutation c) =
        replayedPlusRows (K := K) r c := by
  have h := one_add_negative_add_positive_eq_zero E
  intro r c
  fin_cases r <;> fin_cases c
  · change ((108468170982 : K) / 2) + ((108468170982 : K) / 2) = (108468170982 : K)
    norm_num
  · change ((2768742 : K) / 2) + ((2768742 : K) / 2) = (2768742 : K)
    norm_num
  · change ((187110 : K) / 2) + ((187110 : K) / 2) = (187110 : K)
    norm_num
  · change ((-2970 : K) / 2) + ((-2970 : K) / 2) = (-2970 : K)
    norm_num
  · change ((54 : K) / 2) + ((54 : K) / 2) = (54 : K)
    norm_num
  · change ((198 : K) / 2) + ((198 : K) / 2) = (198 : K)
    norm_num
  · change ((432 : K) / 2) + ((432 : K) / 2) = (432 : K)
    norm_num
  · change ((38 : K) / 2) + ((38 : K) / 2) = (38 : K)
    norm_num
  · change ((24 : K) / 2) + ((24 : K) / 2) = (24 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((-18 : K) / 2) + ((-18 : K) / 2) = (-18 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((-8 : K) / 2) + ((-8 : K) / 2) = (-8 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((-10 : K) / 2) + ((-10 : K) / 2) = (-10 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((4 : K) / 2) + ((4 : K) / 2) = (4 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((237177866772 : K) / 2) + ((237177866772 : K) / 2) = (237177866772 : K)
    norm_num
  · change ((-4907628 : K) / 2) + ((-4907628 : K) / 2) = (-4907628 : K)
    norm_num
  · change ((-210924 : K) / 2) + ((-210924 : K) / 2) = (-210924 : K)
    norm_num
  · change ((3348 : K) / 2) + ((3348 : K) / 2) = (3348 : K)
    norm_num
  · change ((1188 : K) / 2) + ((1188 : K) / 2) = (1188 : K)
    norm_num
  · change ((180 : K) / 2) + ((180 : K) / 2) = (180 : K)
    norm_num
  · change ((-378 : K) / 2) + ((-378 : K) / 2) = (-378 : K)
    norm_num
  · change ((-70 : K) / 2) + ((-70 : K) / 2) = (-70 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-20 : K) / 2) + ((-20 : K) / 2) = (-20 : K)
    norm_num
  · change ((12 : K) / 2) + ((12 : K) / 2) = (12 : K)
    norm_num
  · change ((-12 : K) / 2) + ((-12 : K) / 2) = (-12 : K)
    norm_num
  · change ((22 : K) / 2) + ((22 : K) / 2) = (22 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((312643551654 : K) / 2) + ((312643551654 : K) / 2) = (312643551654 : K)
    norm_num
  · change ((-170586 : K) / 2) + ((-170586 : K) / 2) = (-170586 : K)
    norm_num
  · change ((78246 : K) / 2) + ((78246 : K) / 2) = (78246 : K)
    norm_num
  · change ((-1242 : K) / 2) + ((-1242 : K) / 2) = (-1242 : K)
    norm_num
  · change ((-378 : K) / 2) + ((-378 : K) / 2) = (-378 : K)
    norm_num
  · change ((-90 : K) / 2) + ((-90 : K) / 2) = (-90 : K)
    norm_num
  · change ((54 : K) / 2) + ((54 : K) / 2) = (54 : K)
    norm_num
  · change ((28 : K) / 2) + ((28 : K) / 2) = (28 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-10 : K) / 2) + ((-10 : K) / 2) = (-10 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((14 : K) / 2) + ((14 : K) / 2) = (14 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((-6 : K) / 2) + ((-6 : K) / 2) = (-6 : K)
    norm_num
  · change ((-8 : K) / 2) + ((-8 : K) / 2) = (-8 : K)
    norm_num
  · change ((4 : K) / 2) + ((4 : K) / 2) = (4 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((312643551654 : K) / 2) + ((312643551654 : K) / 2) = (312643551654 : K)
    norm_num
  · change ((-170586 : K) / 2) + ((-170586 : K) / 2) = (-170586 : K)
    norm_num
  · change ((78246 : K) / 2) + ((78246 : K) / 2) = (78246 : K)
    norm_num
  · change ((-1242 : K) / 2) + ((-1242 : K) / 2) = (-1242 : K)
    norm_num
  · change ((-378 : K) / 2) + ((-378 : K) / 2) = (-378 : K)
    norm_num
  · change ((-90 : K) / 2) + ((-90 : K) / 2) = (-90 : K)
    norm_num
  · change ((54 : K) / 2) + ((54 : K) / 2) = (54 : K)
    norm_num
  · change ((28 : K) / 2) + ((28 : K) / 2) = (28 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-10 : K) / 2) + ((-10 : K) / 2) = (-10 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((14 : K) / 2) + ((14 : K) / 2) = (14 : K)
    norm_num
  · change ((6 : K) / 2) + ((6 : K) / 2) = (6 : K)
    norm_num
  · change ((-6 : K) / 2) + ((-6 : K) / 2) = (-6 : K)
    norm_num
  · change ((-8 : K) / 2) + ((-8 : K) / 2) = (-8 : K)
    norm_num
  · change ((4 : K) / 2) + ((4 : K) / 2) = (4 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change ((2 : K) / 2) + ((2 : K) / 2) = (2 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((0 : K) / 2) + ((0 : K) / 2) = (0 : K)
    norm_num
  · change ((-2 : K) / 2) + ((-2 : K) / 2) = (-2 : K)
    norm_num
  · change (164572397352 : K) + (164572397352 : K) = (((108468170982 : K) + (237177866772 : K) + (312643551654 : K)) / 2)
    norm_num
  · change (-577368 : K) + (-577368 : K) = (((2768742 : K) + (-4907628 : K) + (-170586 : K)) / 2)
    norm_num
  · change (13608 : K) + (13608 : K) = (((187110 : K) + (-210924 : K) + (78246 : K)) / 2)
    norm_num
  · change (-216 : K) + (-216 : K) = (((-2970 : K) + (3348 : K) + (-1242 : K)) / 2)
    norm_num
  · change (216 : K) + (216 : K) = (((54 : K) + (1188 : K) + (-378 : K)) / 2)
    norm_num
  · change (72 : K) + (72 : K) = (((198 : K) + (180 : K) + (-90 : K)) / 2)
    norm_num
  · change (27 : K) + (27 : K) = (((432 : K) + (-378 : K) + (54 : K)) / 2)
    norm_num
  · change (-1 : K) + (-1 : K) = (((38 : K) + (-70 : K) + (28 : K)) / 2)
    norm_num
  · change (6 : K) + (6 : K) = (((24 : K) + (0 : K) + (0 : K)) / 2)
    norm_num
  · change (-8 : K) + (-8 : K) = (((-2 : K) + (-20 : K) + (-10 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((-18 : K) + (12 : K) + (6 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((6 : K) + (-12 : K) + (6 : K)) / 2)
    norm_num
  · change (7 : K) + (7 : K) = (((-8 : K) + (22 : K) + (14 : K)) / 2)
    norm_num
  · change (3 : K) + (3 : K) = (((0 : K) + (6 : K) + (6 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((6 : K) + (0 : K) + (-6 : K)) / 2)
    norm_num
  · change (-1 : K) + (-1 : K) = (((2 : K) + (2 : K) + (-8 : K)) / 2)
    norm_num
  · change (-1 : K) + (-1 : K) = (((-10 : K) + (2 : K) + (4 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((0 : K) + (0 : K) + (0 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((2 : K) + (0 : K) + (-2 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((0 : K) + (-2 : K) + (2 : K)) / 2)
    norm_num
  · change (1 : K) + (1 : K) = (((4 : K) + (-2 : K) + (2 : K)) / 2)
    norm_num
  · change (-1 : K) + (-1 : K) = (((0 : K) + (-2 : K) + (-2 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((-2 : K) + (0 : K) + (2 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((0 : K) + (0 : K) + (0 : K)) / 2)
    norm_num
  · change (0 : K) + (0 : K) = (((0 : K) + (0 : K) + (0 : K)) / 2)
    norm_num
  · change (1 : K) + (1 : K) = (((2 : K) + (2 : K) + (0 : K)) / 2)
    norm_num
  · change (-1 : K) + (-1 : K) = (((-2 : K) + (-2 : K) + (0 : K)) / 2)
    norm_num
  · change (-negativePowerSum E) + (-positivePowerSum E) = (((0 : K) + (2 : K) + (0 : K)) / 2)
    norm_num
    linear_combination -h
  · change (-positivePowerSum E) + (-negativePowerSum E) = (((0 : K) + (2 : K) + (0 : K)) / 2)
    norm_num
    linear_combination -h
  · change (-1 : K) + (-1 : K) = (((-2 : K) + (0 : K) + (-2 : K)) / 2)
    norm_num
  · change ((((108468170982 : K) / 2) + ((237177866772 : K) / 2) + ((312643551654 : K) / 2)) - (164572397352 : K)) + ((((108468170982 : K) / 2) + ((237177866772 : K) / 2) + ((312643551654 : K) / 2)) - (164572397352 : K)) = (((108468170982 : K) + (237177866772 : K) + (312643551654 : K)) / 2)
    norm_num
  · change ((((2768742 : K) / 2) + ((-4907628 : K) / 2) + ((-170586 : K) / 2)) - (-577368 : K)) + ((((2768742 : K) / 2) + ((-4907628 : K) / 2) + ((-170586 : K) / 2)) - (-577368 : K)) = (((2768742 : K) + (-4907628 : K) + (-170586 : K)) / 2)
    norm_num
  · change ((((187110 : K) / 2) + ((-210924 : K) / 2) + ((78246 : K) / 2)) - (13608 : K)) + ((((187110 : K) / 2) + ((-210924 : K) / 2) + ((78246 : K) / 2)) - (13608 : K)) = (((187110 : K) + (-210924 : K) + (78246 : K)) / 2)
    norm_num
  · change ((((-2970 : K) / 2) + ((3348 : K) / 2) + ((-1242 : K) / 2)) - (-216 : K)) + ((((-2970 : K) / 2) + ((3348 : K) / 2) + ((-1242 : K) / 2)) - (-216 : K)) = (((-2970 : K) + (3348 : K) + (-1242 : K)) / 2)
    norm_num
  · change ((((54 : K) / 2) + ((1188 : K) / 2) + ((-378 : K) / 2)) - (216 : K)) + ((((54 : K) / 2) + ((1188 : K) / 2) + ((-378 : K) / 2)) - (216 : K)) = (((54 : K) + (1188 : K) + (-378 : K)) / 2)
    norm_num
  · change ((((198 : K) / 2) + ((180 : K) / 2) + ((-90 : K) / 2)) - (72 : K)) + ((((198 : K) / 2) + ((180 : K) / 2) + ((-90 : K) / 2)) - (72 : K)) = (((198 : K) + (180 : K) + (-90 : K)) / 2)
    norm_num
  · change ((((432 : K) / 2) + ((-378 : K) / 2) + ((54 : K) / 2)) - (27 : K)) + ((((432 : K) / 2) + ((-378 : K) / 2) + ((54 : K) / 2)) - (27 : K)) = (((432 : K) + (-378 : K) + (54 : K)) / 2)
    norm_num
  · change ((((38 : K) / 2) + ((-70 : K) / 2) + ((28 : K) / 2)) - (-1 : K)) + ((((38 : K) / 2) + ((-70 : K) / 2) + ((28 : K) / 2)) - (-1 : K)) = (((38 : K) + (-70 : K) + (28 : K)) / 2)
    norm_num
  · change ((((24 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (6 : K)) + ((((24 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (6 : K)) = (((24 : K) + (0 : K) + (0 : K)) / 2)
    norm_num
  · change ((((-2 : K) / 2) + ((-20 : K) / 2) + ((-10 : K) / 2)) - (-8 : K)) + ((((-2 : K) / 2) + ((-20 : K) / 2) + ((-10 : K) / 2)) - (-8 : K)) = (((-2 : K) + (-20 : K) + (-10 : K)) / 2)
    norm_num
  · change ((((-18 : K) / 2) + ((12 : K) / 2) + ((6 : K) / 2)) - (0 : K)) + ((((-18 : K) / 2) + ((12 : K) / 2) + ((6 : K) / 2)) - (0 : K)) = (((-18 : K) + (12 : K) + (6 : K)) / 2)
    norm_num
  · change ((((6 : K) / 2) + ((-12 : K) / 2) + ((6 : K) / 2)) - (0 : K)) + ((((6 : K) / 2) + ((-12 : K) / 2) + ((6 : K) / 2)) - (0 : K)) = (((6 : K) + (-12 : K) + (6 : K)) / 2)
    norm_num
  · change ((((-8 : K) / 2) + ((22 : K) / 2) + ((14 : K) / 2)) - (7 : K)) + ((((-8 : K) / 2) + ((22 : K) / 2) + ((14 : K) / 2)) - (7 : K)) = (((-8 : K) + (22 : K) + (14 : K)) / 2)
    norm_num
  · change ((((0 : K) / 2) + ((6 : K) / 2) + ((6 : K) / 2)) - (3 : K)) + ((((0 : K) / 2) + ((6 : K) / 2) + ((6 : K) / 2)) - (3 : K)) = (((0 : K) + (6 : K) + (6 : K)) / 2)
    norm_num
  · change ((((6 : K) / 2) + ((0 : K) / 2) + ((-6 : K) / 2)) - (0 : K)) + ((((6 : K) / 2) + ((0 : K) / 2) + ((-6 : K) / 2)) - (0 : K)) = (((6 : K) + (0 : K) + (-6 : K)) / 2)
    norm_num
  · change ((((2 : K) / 2) + ((2 : K) / 2) + ((-8 : K) / 2)) - (-1 : K)) + ((((2 : K) / 2) + ((2 : K) / 2) + ((-8 : K) / 2)) - (-1 : K)) = (((2 : K) + (2 : K) + (-8 : K)) / 2)
    norm_num
  · change ((((-10 : K) / 2) + ((2 : K) / 2) + ((4 : K) / 2)) - (-1 : K)) + ((((-10 : K) / 2) + ((2 : K) / 2) + ((4 : K) / 2)) - (-1 : K)) = (((-10 : K) + (2 : K) + (4 : K)) / 2)
    norm_num
  · change ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) + ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) = (((0 : K) + (0 : K) + (0 : K)) / 2)
    norm_num
  · change ((((2 : K) / 2) + ((0 : K) / 2) + ((-2 : K) / 2)) - (0 : K)) + ((((2 : K) / 2) + ((0 : K) / 2) + ((-2 : K) / 2)) - (0 : K)) = (((2 : K) + (0 : K) + (-2 : K)) / 2)
    norm_num
  · change ((((0 : K) / 2) + ((-2 : K) / 2) + ((2 : K) / 2)) - (0 : K)) + ((((0 : K) / 2) + ((-2 : K) / 2) + ((2 : K) / 2)) - (0 : K)) = (((0 : K) + (-2 : K) + (2 : K)) / 2)
    norm_num
  · change ((((4 : K) / 2) + ((-2 : K) / 2) + ((2 : K) / 2)) - (1 : K)) + ((((4 : K) / 2) + ((-2 : K) / 2) + ((2 : K) / 2)) - (1 : K)) = (((4 : K) + (-2 : K) + (2 : K)) / 2)
    norm_num
  · change ((((0 : K) / 2) + ((-2 : K) / 2) + ((-2 : K) / 2)) - (-1 : K)) + ((((0 : K) / 2) + ((-2 : K) / 2) + ((-2 : K) / 2)) - (-1 : K)) = (((0 : K) + (-2 : K) + (-2 : K)) / 2)
    norm_num
  · change ((((-2 : K) / 2) + ((0 : K) / 2) + ((2 : K) / 2)) - (0 : K)) + ((((-2 : K) / 2) + ((0 : K) / 2) + ((2 : K) / 2)) - (0 : K)) = (((-2 : K) + (0 : K) + (2 : K)) / 2)
    norm_num
  · change ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) + ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) = (((0 : K) + (0 : K) + (0 : K)) / 2)
    norm_num
  · change ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) + ((((0 : K) / 2) + ((0 : K) / 2) + ((0 : K) / 2)) - (0 : K)) = (((0 : K) + (0 : K) + (0 : K)) / 2)
    norm_num
  · change ((((2 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (1 : K)) + ((((2 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (1 : K)) = (((2 : K) + (2 : K) + (0 : K)) / 2)
    norm_num
  · change ((((-2 : K) / 2) + ((-2 : K) / 2) + ((0 : K) / 2)) - (-1 : K)) + ((((-2 : K) / 2) + ((-2 : K) / 2) + ((0 : K) / 2)) - (-1 : K)) = (((-2 : K) + (-2 : K) + (0 : K)) / 2)
    norm_num
  · change ((((0 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (-negativePowerSum E)) + ((((0 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (-positivePowerSum E)) = (((0 : K) + (2 : K) + (0 : K)) / 2)
    norm_num
    linear_combination h
  · change ((((0 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (-positivePowerSum E)) + ((((0 : K) / 2) + ((2 : K) / 2) + ((0 : K) / 2)) - (-negativePowerSum E)) = (((0 : K) + (2 : K) + (0 : K)) / 2)
    norm_num
    linear_combination h
  · change ((((-2 : K) / 2) + ((0 : K) / 2) + ((-2 : K) / 2)) - (-1 : K)) + ((((-2 : K) / 2) + ((0 : K) / 2) + ((-2 : K) / 2)) - (-1 : K)) = (((-2 : K) + (0 : K) + (-2 : K)) / 2)
    norm_num

/-- A finite witness on the fixed transcription. Its type's historical name
does not assert that this development export is the canonical supplement. -/
def literalV3Binding (E : PrimitiveTwentyNineEncoding K) :
    CanonicalSupplementV3Binding E where
  restrictionRows := literalV3Rows E
  rawPacket := literalV3RawPacket E
  symmetrised_rows_eq := literalV3Rows_symmetrised E

@[simp]
theorem literalV3Binding_restrictionRows (E : PrimitiveTwentyNineEncoding K) :
    (literalV3Binding E).restrictionRows = literalV3Rows E := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3Rows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
