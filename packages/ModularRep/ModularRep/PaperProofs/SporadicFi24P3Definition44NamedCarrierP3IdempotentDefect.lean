import ModularRep.BlockCentralBrauerImage
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IdempotentData
import Mathlib.GroupTheory.Index

/-! Trivial intrinsic defect from the full literal modular idempotent coefficients.
All class representatives, centralizer orders and coefficient values are actual
carrier data. The vanishing of Brauer restriction is derived here. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IdempotentDefect
open ModularRep
open SporadicFi24P3Definition44NamedCarrierP3IdempotentData

theorem centralizer_card_map {G : Type*} [Group G] (e : MulAut G) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have h (u : G) : u ∈ Subgroup.centralizer ({x} : Set G) ↔
      e u ∈ Subgroup.centralizer ({e x} : Set G) := by
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hu
      simpa only [map_mul] using congrArg e hu
    · intro hu
      apply e.injective
      simpa only [map_mul] using hu
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv h)).symm

theorem restriction_bot_ne_zero {k G : Type*} [Field k] [Group G]
    (z : GroupAlgebraCenter k G) (hne : (z : k[G]) ≠ 0) :
    centralBrauerRestriction (⊥ : Subgroup G) z ≠ 0 := by
  intro h
  apply hne
  ext x
  let c : centralizerOf (⊥ : Subgroup G) := ⟨x, by
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    have hq' : q = 1 := Subgroup.mem_bot.mp hq
    simp [hq']⟩
  exact congrArg (fun w : GroupAlgebraCenter k (centralizerOf (⊥ : Subgroup G)) =>
    (w : k[centralizerOf (⊥ : Subgroup G)]).coeff c) h

theorem restriction_zero_of_centralizer_coefficients
    {p : ℕ} {k G : Type*} [Field k] [Group G] [Fact p.Prime]
    (z : GroupAlgebraCenter k G)
    (hcoeff : ∀ x : G, p ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) →
      (z : k[G]).coeff x = 0)
    (P : Subgroup G) (hP : IsPGroup p P) (hne : P ≠ ⊥) :
    centralBrauerRestriction P z = 0 := by
  have hpP : p ∣ Nat.card P := hP.card_eq_or_dvd.resolve_left
    (fun h => hne (Subgroup.card_eq_one.mp h))
  apply Subtype.ext
  ext x
  change (z : k[G]).coeff (x : G) = 0
  apply hcoeff
  exact hpP.trans (Subgroup.card_dvd_of_le (by
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp x.property q hq)))

theorem defect_bot_of_full_coefficient_table
    {k G Block : Type*} [Field k] [Group G] [Finite G] [CharP k 3]
    [Fintype Block] {e : Block → k[G]}
    (blocks : BlockIdempotentDecomposition e) (B : Block)
    (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (orders : ∀ c, Nat.card (Subgroup.centralizer ({rep c} : Set G)) =
      centralizerOrders c)
    (coefficients : ∀ c, (e B).coeff (rep c) =
      (inverseCharacterValues c : k) / (7031383654400 : k)) :
    IsMaximalCentralBrauerDefect (p := 3) blocks B (⊥ : Subgroup G) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hzero (x : G) (hx : 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G))) :
      (e B).coeff x = 0 := by
    obtain ⟨c, a, rfl⟩ := cover x
    have hcard := centralizer_card_map (MulAut.conj a) (rep c)
    change Nat.card (Subgroup.centralizer ({a * rep c * a⁻¹} : Set G)) = _ at hcard
    rw [hcard, orders c] at hx
    have hv := bad_centralizer_value_divisible c hx
    obtain ⟨n, hn⟩ := hv
    have hthree : (3 : k) = 0 := CharP.cast_eq_zero k 3
    have hcast : (inverseCharacterValues c : k) = 0 := by
      rw [hn, Int.cast_mul]
      norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
      rw [hthree, zero_mul]
    rw [← blocks.blockIdempotentInCenter_coe B]
    rw [GroupAlgebraCenter.coeff_conjugate, blocks.blockIdempotentInCenter_coe,
      coefficients c, hcast, zero_div]
  refine ⟨IsPGroup.of_bot,
    restriction_bot_ne_zero (blocks.blockIdempotentInCenter B) (blocks.primitive B).ne_zero, ?_⟩
  intro P hP hnonzero _
  by_contra h
  exact hnonzero (restriction_zero_of_centralizer_coefficients
    (blocks.blockIdempotentInCenter B) hzero P hP (Ne.symm h))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IdempotentDefect


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
