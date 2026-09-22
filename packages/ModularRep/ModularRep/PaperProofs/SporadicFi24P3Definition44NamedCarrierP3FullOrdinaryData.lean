import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Literal Fi24 prime-three ordinary degrees and block labels. Indices are
zero-based: row 93 is CTblLib row 94. These closed calculations do not
identify this table with any particular group or set of characters. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData

def degrees : Fin 108 → ℕ :=
  ![1, 8671, 57477, 249458, 555611, 1603525, 1603525, 1666833, 4864431,
    32715683, 35873145, 40536925, 48893768, 74837400, 74837400, 79452373, 112168056, 159402880,
    281380736, 415098112, 635618984, 1069551175, 1112333222, 1264015025, 1337276304, 1540153692, 2346900864,
    3178094920, 3208653525, 3283490925, 5005499499, 5775278080, 6471756928, 7150713570, 8529641472, 9100908180,
    9441555200, 10169903744, 10776585600, 10776585600, 13904165275, 13904165275, 14507059905, 17068369920, 17161712568,
    18481844304, 18481844304, 25027497495, 27808330550, 29444114700, 35594663104, 36858678129, 37337059200, 38641860608,
    40043995992, 44493328880, 45049495491, 46602926370, 54234085491, 54481627200, 54481627200, 55616661100, 63831063582,
    65393917952, 65393917952, 67331776512, 71189326208, 74887473024, 77007684600, 77007684600, 77108871168, 77379702400,
    102385217025, 111233322200, 111233322200, 118588933386, 132390354096, 132390354096, 139317477376, 140095612800, 140095612800,
    142169187069, 142378652416, 145650089984, 150201655296, 151397207325, 151397207325, 156321775827, 156321775827, 160313753600,
    164572397352, 164572397352, 169598100672, 178514751987, 184117100544, 190685695200, 197813862400, 197813862400, 200219979960,
    200219979960, 205353825600, 205353825600, 205940550816, 222758961152, 225247477455, 250274974950, 282049015248, 336033532800]

def blockLabels : Fin 108 → Fin 3 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 1, 0,
    1, 1, 0, 2, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem full_part_dvd_degree_iff (r : Fin 108) :
    43046721 ∣ degrees r ↔ r = 93 := by
  fin_cases r <;> decide

theorem block_label_two_iff (r : Fin 108) :
    blockLabels r = 2 ↔ r = 93 := by
  fin_cases r <;> decide

theorem ordProj_three_of_exact_power {n : ℕ} (hn : n ≠ 0)
    (hdvd : 3 ^ 16 ∣ n) (hnot : ¬ 3 ^ 17 ∣ n) :
    ordProj[3] n = 43046721 := by
  have hp : Nat.Prime 3 := by decide
  have hlo : 16 ≤ n.factorization 3 :=
    (hp.pow_dvd_iff_le_factorization hn).mp hdvd
  have hhi : n.factorization 3 < 17 :=
    Nat.lt_of_not_ge (fun h => hnot ((hp.pow_dvd_iff_le_factorization hn).mpr h))
  have heq : n.factorization 3 = 16 :=
    Nat.le_antisymm (Nat.le_of_lt_succ hhi) hlo
  rw [heq]
  norm_num

theorem group_order_three_part :
    ordProj[3] 1255205709190661721292800 = 43046721 :=
  ordProj_three_of_exact_power (by decide) (by norm_num) (by norm_num)

theorem selected_degree_three_part : ordProj[3] (degrees 93) = 43046721 :=
  ordProj_three_of_exact_power (by decide) (by decide) (by decide)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
