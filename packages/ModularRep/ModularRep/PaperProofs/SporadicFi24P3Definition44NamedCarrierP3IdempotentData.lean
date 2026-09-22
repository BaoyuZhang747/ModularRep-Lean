import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! Full inverse character row94 and centralizer orders in the F3+ table.
The column indices are conjugacy classes, distinct from ordinary row indices.
Specified modular-idempotent coefficients remain a separate explicit binding. -/
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IdempotentData
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def inverseCharacterValues : Fin 108 → ℤ :=
  ![178514751987, -2814669, 124659, 0, 0, 0, 0, 0, 243,
    -405, 99, 162, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, -9, -9, -9, -9,
    3, 0, 0, 0, 0, 0, 0, 6, -6,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 3, 3, 0,
    0, 0, 1, -1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, -2, 0, 0, 0, 0,
    0, -1, -1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0]

def centralizerOrders : Fin 108 → ℕ :=
  ![1255205709190661721292800, 258247006617600, 160526499840, 44569618329600, 2424391326720, 14285134080, 153055008, 38211264, 39813120,
    5806080, 294912, 907200, 78382080, 19595520, 10077696, 2985984, 2239488, 559872,
    69984, 69984, 62208, 23328, 5184, 17640, 2058, 2304, 1536,
    768, 472392, 262440, 209952, 59049, 13122, 972, 2400, 960,
    132, 124416, 31104, 13824, 8640, 5184, 3888, 2592, 1152,
    864, 864, 576, 432, 144, 234, 168, 42, 5400,
    405, 270, 32, 17, 2592, 1296, 648, 648, 162,
    108, 108, 108, 120, 80, 252, 63, 42, 42,
    44, 23, 23, 288, 288, 72, 72, 48, 48,
    48, 26, 81, 81, 81, 28, 29, 29, 120,
    30, 33, 33, 35, 432, 432, 108, 36, 117,
    117, 117, 117, 84, 42, 42, 45, 45, 60]

theorem bad_centralizer_value_divisible (c : Fin 108) :
    3 ∣ centralizerOrders c → (3 : ℤ) ∣ inverseCharacterValues c := by
  fin_cases c <;> decide

theorem coefficient_denominator_prime_to_three : ¬ 3 ∣ 7031383654400 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IdempotentData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
