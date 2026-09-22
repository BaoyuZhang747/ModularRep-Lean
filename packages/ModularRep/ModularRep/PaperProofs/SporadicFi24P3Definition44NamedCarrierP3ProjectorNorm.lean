import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IdempotentData
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The full class cover and literal selected values determine the ordinary
character norm. Neither class distinctness nor a splitting-field premise is
assumed: the class sizes prove the former, and the norm gives scalar intertwiners. -/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorNorm
open SporadicFi24P3Definition44NamedCarrierP3IdempotentData

theorem class_sizes_sum :
    (∑ c : Fin 108, 1255205709190661721292800 / centralizerOrders c) =
      1255205709190661721292800 := by decide

theorem weighted_inverse_values_square_sum :
    (∑ c : Fin 108, ((1255205709190661721292800 / centralizerOrders c : ℕ) : ℤ) *
      inverseCharacterValues c ^ 2) = (1255205709190661721292800 : ℤ) := by decide

theorem conjugacyClass_nat_card {G : Type*} [Group G] [Fintype G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier =
      Nat.card G / Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  let : Fintype (ConjClasses.mk x).carrier := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer (ConjAct G) x) := Fintype.ofFinite _
  have hc : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (MulAction.stabilizer (ConjAct G) x) := by
    apply Nat.card_congr
    exact (ConjAct.toConjAct (G := G)).toEquiv.subtypeEquiv
      (fun y => by rw [Subgroup.centralizer_eq_comap_stabilizer]; rfl)
  calc
    Nat.card (ConjClasses.mk x).carrier = Fintype.card (ConjClasses.mk x).carrier :=
      Nat.card_eq_fintype_card
    _ = Fintype.card G / Fintype.card (MulAction.stabilizer (ConjAct G) x) :=
      ConjClasses.card_carrier x
    _ = Nat.card G / Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, ← hc]

theorem class_projection_bijective {G : Type*} [Group G] [Fintype G]
    (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (orders : ∀ c, Nat.card (Subgroup.centralizer ({rep c} : Set G)) = centralizerOrders c)
    (horder : Nat.card G = 1255205709190661721292800) :
    Function.Bijective
      (fun s : (Σ c : Fin 108, (ConjClasses.mk (rep c)).carrier) => s.2.val) := by
  classical
  let : ∀ c : Fin 108, Fintype (ConjClasses.mk (rep c)).carrier :=
    fun c => Fintype.ofFinite _
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro x
    obtain ⟨c, a, hx⟩ := cover x
    refine ⟨⟨c, ⟨x, ?_⟩⟩, rfl⟩
    change IsConj (rep c) x
    exact isConj_iff.mpr ⟨a, hx.symm⟩
  · rw [Fintype.card_sigma]
    calc
      (∑ c, Fintype.card (ConjClasses.mk (rep c)).carrier) =
          ∑ c : Fin 108, 1255205709190661721292800 / centralizerOrders c := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← Nat.card_eq_fintype_card, conjugacyClass_nat_card, horder, orders c]
      _ = 1255205709190661721292800 := class_sizes_sum
      _ = Fintype.card G := by rw [← Nat.card_eq_fintype_card, horder]

theorem sum_of_full_class_cover
    {K G : Type*} [Field K] [Group G] [Fintype G]
    (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (orders : ∀ c, Nat.card (Subgroup.centralizer ({rep c} : Set G)) = centralizerOrders c)
    (horder : Nat.card G = 1255205709190661721292800)
    (f : G → K) (hf : ∀ c a, f (a * rep c * a⁻¹) = f (rep c)) :
    (∑ x : G, f x) = ∑ c : Fin 108,
      ((1255205709190661721292800 / centralizerOrders c : ℕ) : K) * f (rep c) := by
  classical
  let : ∀ c : Fin 108, Fintype (ConjClasses.mk (rep c)).carrier :=
    fun c => Fintype.ofFinite _
  have hb := class_projection_bijective rep cover orders horder
  calc
    (∑ x : G, f x) =
        ∑ s : (Σ c : Fin 108, (ConjClasses.mk (rep c)).carrier), f s.2.val :=
      (hb.sum_comp f).symm
    _ = ∑ c : Fin 108, ∑ x : (ConjClasses.mk (rep c)).carrier, f x.val :=
      Fintype.sum_sigma _
    _ = ∑ c : Fin 108,
        ((1255205709190661721292800 / centralizerOrders c : ℕ) : K) * f (rep c) := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        (∑ x : (ConjClasses.mk (rep c)).carrier, f x.val) =
            ∑ _x : (ConjClasses.mk (rep c)).carrier, f (rep c) := by
          apply Finset.sum_congr rfl
          intro x _
          have hx : IsConj (rep c) x.val := x.property
          obtain ⟨a, ha⟩ := isConj_iff.mp hx
          rw [← ha]
          exact hf c a
        _ = (Fintype.card (ConjClasses.mk (rep c)).carrier : K) * f (rep c) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ((1255205709190661721292800 / centralizerOrders c : ℕ) : K) * f (rep c) := by
          rw [← Nat.card_eq_fintype_card, conjugacyClass_nat_card, horder, orders c]

theorem selected_character_norm
    {K G V : Type*} [Field K] [Group G] [Fintype G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K G V) (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (orders : ∀ c, Nat.card (Subgroup.centralizer ({rep c} : Set G)) = centralizerOrders c)
    (horder : Nat.card G = 1255205709190661721292800)
    (values : ∀ c, rho.character (rep c) = (inverseCharacterValues c : K))
    (inverseValues : ∀ c, rho.character ((rep c)⁻¹) = (inverseCharacterValues c : K)) :
    (∑ x : G, rho.character x * rho.character x⁻¹) = (Nat.card G : K) := by
  have hsum := sum_of_full_class_cover rep cover orders horder
    (fun x => rho.character x * rho.character x⁻¹) (by
      intro c a
      have hi : (a * rep c * a⁻¹)⁻¹ = a * (rep c)⁻¹ * a⁻¹ := by
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [hi, Representation.char_conj, Representation.char_conj])
  rw [horder]
  calc
    (∑ x : G, rho.character x * rho.character x⁻¹) =
        ∑ c : Fin 108,
          ((1255205709190661721292800 / centralizerOrders c : ℕ) : K) *
            (rho.character (rep c) * rho.character ((rep c)⁻¹)) := hsum
    _ = ∑ c : Fin 108,
        ((1255205709190661721292800 / centralizerOrders c : ℕ) : K) *
          (inverseCharacterValues c : K) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [values c, inverseValues c, pow_two]
    _ = (1255205709190661721292800 : K) := by
      have h := congrArg (fun n : ℤ => (n : K)) weighted_inverse_values_square_sum
      simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow,
        Int.cast_natCast, Int.cast_ofNat] using h

theorem selected_intertwining_finrank_one
    {K G V : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K G V) (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (orders : ∀ c, Nat.card (Subgroup.centralizer ({rep c} : Set G)) = centralizerOrders c)
    (horder : Nat.card G = 1255205709190661721292800)
    (values : ∀ c, rho.character (rep c) = (inverseCharacterValues c : K))
    (inverseValues : ∀ c, rho.character ((rep c)⁻¹) = (inverseCharacterValues c : K)) :
    Module.finrank K (Representation.IntertwiningMap rho rho) = 1 := by
  have hN : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let := invertibleOfNonzero hN
  have hnorm := selected_character_norm rho rep cover orders horder values inverseValues
  have hd := Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho rho
  rw [hnorm, inv_mul_cancel₀ hN] at hd
  apply (Nat.cast_injective (R := K))
  simpa only [Nat.cast_one] using hd.symm

theorem selected_scalar_intertwining
    {K G V : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K G V) (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (orders : ∀ c, Nat.card (Subgroup.centralizer ({rep c} : Set G)) = centralizerOrders c)
    (horder : Nat.card G = 1255205709190661721292800)
    (values : ∀ c, rho.character (rep c) = (inverseCharacterValues c : K))
    (inverseValues : ∀ c, rho.character ((rep c)⁻¹) = (inverseCharacterValues c : K)) :
    ∀ f : Representation.IntertwiningMap rho rho, ∃ c : K, f = c • 1 := by
  have hd := selected_intertwining_finrank_one rho rep cover orders horder values inverseValues
  let : Nontrivial (Representation.IntertwiningMap rho rho) :=
    Module.nontrivial_of_finrank_eq_succ hd
  intro f
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (1 : Representation.IntertwiningMap rho rho) one_ne_zero).mp hd f
  exact ⟨c, hc.symm⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorNorm


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
