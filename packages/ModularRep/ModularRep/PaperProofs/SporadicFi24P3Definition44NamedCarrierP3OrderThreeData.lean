import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Literal degrees of CTblLib O8+(3).3.2, the published order-three
normalizer quotient. Only arithmetic is certified here; actual quotient and
character-degree coverage are separate specified inputs. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrderThreeData

def quotientDegrees : Fin 125 → ℕ :=
  ![1, 1, 2, 780, 780, 780, 780, 300, 300, 600,
    2457, 2457, 2275, 2275, 4550, 6825, 6825, 2808, 2808, 5616,
    16380, 16380, 16380, 16380, 9450, 9450, 18900, 17550, 17550, 35100,
    18200, 18200, 36400, 18200, 18200, 36400, 54600, 54600, 70200, 70200,
    70200, 70200, 24192, 24192, 48384, 27300, 27300, 54600, 87360, 87360,
    87360, 87360, 122850, 122850, 122850, 122850, 139776, 139776, 147420, 147420,
    147420, 147420, 54600, 54600, 109200, 163800, 163800, 163800, 163800, 199017,
    199017, 491400, 491400, 184275, 184275, 368550, 552825, 552825, 568620, 568620,
    568620, 568620, 218700, 218700, 437400, 698880, 698880, 698880, 698880, 245700,
    245700, 491400, 786240, 786240, 786240, 786240, 291200, 291200, 582400, 291200,
    291200, 582400, 873600, 873600, 332800, 332800, 665600, 998400, 998400, 1257984,
    1257984, 1397760, 1397760, 491400, 491400, 982800, 531441, 531441, 1062882, 716800,
    716800, 1433600, 716800, 716800, 1433600]

theorem full_part_not_dvd_degree :
    ∀ r : Fin 125, ¬ 1594323 ∣ quotientDegrees r := by
  decide

theorem quotient_order_three_part :
    ordProj[3] 29713078886400 = 1594323 := by
  have hp : Nat.Prime 3 := by decide
  have hn : (29713078886400 : ℕ) ≠ 0 := by decide
  have hdvd : 3 ^ 13 ∣ (29713078886400 : ℕ) := by norm_num
  have hnot : ¬ 3 ^ 14 ∣ (29713078886400 : ℕ) := by norm_num
  have hlo : 13 ≤ (29713078886400 : ℕ).factorization 3 :=
    (hp.pow_dvd_iff_le_factorization hn).mp hdvd
  have hhi : (29713078886400 : ℕ).factorization 3 < 14 :=
    Nat.lt_of_not_ge (fun h => hnot ((hp.pow_dvd_iff_le_factorization hn).mpr h))
  have heq : (29713078886400 : ℕ).factorization 3 = 13 :=
    Nat.le_antisymm (Nat.le_of_lt_succ hhi) hlo
  rw [heq]
  norm_num

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrderThreeData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
