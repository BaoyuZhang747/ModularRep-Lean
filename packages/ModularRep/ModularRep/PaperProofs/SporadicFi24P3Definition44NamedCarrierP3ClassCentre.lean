import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IdempotentDefect
import Mathlib.Tactic.FinCases

/-! The retained complete class and centralizer data force a trivial centre.
No new class realization or centreless premise is introduced. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ClassCentre
open SporadicFi24P3Definition44NamedCarrierP3IdempotentData
open SporadicFi24P3Definition44NamedCarrierP3IdempotentDefect
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem centralizerOrders_eq_full_iff (c : Fin 108) :
    centralizerOrders c = 1255205709190661721292800 ↔ c = 0 := by
  fin_cases c <;> decide

theorem center_eq_bot_of_full_centralizer_table
    {G : Type*} [Group G]
    (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (orders : ∀ c, Nat.card (Subgroup.centralizer ({rep c} : Set G)) =
      centralizerOrders c)
    (hcard : Nat.card G = 1255205709190661721292800) :
    Subgroup.center G = ⊥ := by
  have hcentral (x : G) (hx : x ∈ Subgroup.center G) :
      Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
    have ht : Subgroup.centralizer ({x} : Set G) = ⊤ := by
      apply top_unique
      intro a _
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hx a)
    rw [ht, Subgroup.card_top]
  have hindex (x : G) (hx : x ∈ Subgroup.center G)
      (c : Fin 108) (a : G) (ha : x = a * rep c * a⁻¹) : c = 0 := by
    apply (centralizerOrders_eq_full_iff c).mp
    have hc := centralizer_card_map (MulAut.conj a) (rep c)
    change Nat.card (Subgroup.centralizer ({a * rep c * a⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({rep c} : Set G)) at hc
    rw [← ha, hcentral x hx] at hc
    exact (orders c).symm.trans (hc.symm.trans hcard)
  obtain ⟨c, a, ha⟩ := cover (1 : G)
  have hc := hindex 1 (Subgroup.center G).one_mem c a ha
  subst c
  have hrep : rep 0 = 1 := by
    apply (MulAut.conj a).injective
    simpa only [MulAut.conj_apply, mul_one, mul_inv_cancel] using ha.symm
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  obtain ⟨c, a, ha⟩ := cover x
  have hc := hindex x hx c a ha
  simpa only [hc, hrep, mul_one, mul_inv_cancel] using ha

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ClassCentre


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
