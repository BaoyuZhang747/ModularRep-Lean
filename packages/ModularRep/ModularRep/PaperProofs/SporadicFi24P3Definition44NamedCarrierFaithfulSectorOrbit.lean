import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Faithful central characters form one automorphism orbit in the small
centre cases used by the manuscript. Faithfulness derives cyclicity and
primitive-root coverage; inversion is retained as the exact group input. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit

open MulOpposite
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers

theorem coprime_small_exponent {n i : ℕ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6)
    (hi : i < n) (hc : i.Coprime n) : i = 1 ∨ i = n - 1 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  all_goals interval_cases i <;> norm_num at *

theorem faithfulHom_eq_or_eq_inv_of_small_card
    {Z k : Type*} [Group Z] [Finite Z] [Field k]
    (nu mu : Z →* kˣ) (hnu : Function.Injective nu)
    (hmu : Function.Injective mu)
    (hcard : Nat.card Z = 1 ∨ Nat.card Z = 2 ∨
      Nat.card Z = 3 ∨ Nat.card Z = 4 ∨ Nat.card Z = 6) :
    mu = nu ∨ mu = nu⁻¹ := by
  let : IsCyclic Z :=
    isCyclic_of_injective_ringHom ((Units.coeHom k).comp nu)
      (Units.val_injective.comp hnu)
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := Z)
  have hnpos : 0 < Nat.card Z := by
    rcases hcard with h | h | h | h | h <;> omega
  let : NeZero (Nat.card Z) := ⟨hnpos.ne'⟩
  have hzorder : orderOf z = Nat.card Z := orderOf_eq_card_of_forall_mem_zpowers hz
  have hnr : IsPrimitiveRoot (nu z) (Nat.card Z) :=
    IsPrimitiveRoot.iff_orderOf.mpr ((orderOf_injective nu hnu z).trans hzorder)
  have hmr : IsPrimitiveRoot (mu z) (Nat.card Z) :=
    IsPrimitiveRoot.iff_orderOf.mpr ((orderOf_injective mu hmu z).trans hzorder)
  obtain ⟨i, hi, hc, he⟩ := hnr.isPrimitiveRoot_iff'.mp hmr
  rcases coprime_small_exponent hcard hi hc with hi | hi
  · left
    apply (MonoidHom.eq_iff_eq_on_generator hz mu nu).mpr
    simpa only [hi, pow_one] using he.symm
  · right
    apply (MonoidHom.eq_iff_eq_on_generator hz mu (nu⁻¹)).mpr
    change mu z = (nu z)⁻¹
    have hpow : (nu z) ^ (Nat.card Z - 1) = (nu z)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ Nat.card Z from hnpos), hnr.pow_eq_one]
    calc
      mu z = (nu z)^i := he.symm
      _ = (nu z)^(Nat.card Z - 1) := congrArg (fun j : ℕ => (nu z)^j) hi
      _ = (nu z)⁻¹ := hpow

theorem hom_inv_eq_self_of_card_one_or_two
    {Z k : Type*} [Group Z] [Finite Z] [Field k]
    (nu : Z →* kˣ) (hcard : Nat.card Z = 1 ∨ Nat.card Z = 2) : nu⁻¹ = nu := by
  apply MonoidHom.ext
  intro z
  change (nu z)⁻¹ = nu z
  have hz2 : z ^ 2 = 1 := by
    rcases hcard with h | h
    · have hz : z = 1 := by
        simpa only [h, pow_one] using (pow_card_eq_one' (x := z))
      rw [hz, one_pow]
    · simpa only [h] using (pow_card_eq_one' (x := z))
  have hzInv : z⁻¹ = z :=
    (eq_inv_of_mul_eq_one_left (by simpa only [pow_two] using hz2)).symm
  rw [← map_inv, hzInv]

theorem faithfulHom_unique_of_card_one_or_two
    {Z k : Type*} [Group Z] [Finite Z] [Field k]
    (nu mu : Z →* kˣ) (hnu : Function.Injective nu)
    (hmu : Function.Injective mu)
    (hcard : Nat.card Z = 1 ∨ Nat.card Z = 2) : mu = nu := by
  have hc : Nat.card Z = 1 ∨ Nat.card Z = 2 ∨
      Nat.card Z = 3 ∨ Nat.card Z = 4 ∨ Nat.card Z = 6 := by
    rcases hcard with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rcases faithfulHom_eq_or_eq_inv_of_small_card nu mu hnu hmu hc with h | h
  · exact h
  · exact h.trans (hom_inv_eq_self_of_card_one_or_two nu hcard)

universe u
variable {k G : Type u} [Field k] [Group G] [Finite G]

def FaithfulSectorOrbitCases : Prop :=
  Nat.card (Subgroup.center G) = 1 ∨ Nat.card (Subgroup.center G) = 2 ∨
  ((Nat.card (Subgroup.center G) = 3 ∨ Nat.card (Subgroup.center G) = 4 ∨
    Nat.card (Subgroup.center G) = 6) ∧
    ∃ tau : MulAut G, ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹)

theorem faithfulSector_orbit
    (nu0 : FaithfulSector (k := k) (X := G))
    (hcase : FaithfulSectorOrbitCases (G := G))
    (nu : FaithfulSector (k := k) (X := G)) :
    ∃ a : (MulAut G)ᵐᵒᵖ, a • nu0 = nu := by
  rcases hcase with h | h | ⟨hc, tau, hinverts⟩
  · have he : nu = nu0 := Subtype.ext
      (faithfulHom_unique_of_card_one_or_two nu0.1 nu.1 nu0.2 nu.2 (Or.inl h))
    exact ⟨1, by simpa only [one_smul] using he.symm⟩
  · have he : nu = nu0 := Subtype.ext
      (faithfulHom_unique_of_card_one_or_two nu0.1 nu.1 nu0.2 nu.2 (Or.inr h))
    exact ⟨1, by simpa only [one_smul] using he.symm⟩
  · have hc' : Nat.card (Subgroup.center G) = 1 ∨ Nat.card (Subgroup.center G) = 2 ∨
        Nat.card (Subgroup.center G) = 3 ∨ Nat.card (Subgroup.center G) = 4 ∨
        Nat.card (Subgroup.center G) = 6 := Or.inr (Or.inr hc)
    rcases faithfulHom_eq_or_eq_inv_of_small_card nu0.1 nu.1 nu0.2 nu.2 hc' with he | he
    · have hsector : nu = nu0 := Subtype.ext he
      exact ⟨1, by simpa only [one_smul] using hsector.symm⟩
    · refine ⟨op tau, ?_⟩
      apply Subtype.ext
      change (op tau) • nu0.1 = nu.1
      rw [he]
      apply MonoidHom.ext
      intro z
      change nu0.1 (Representation.centerAutomorphism tau z) = (nu0.1 z)⁻¹
      have hz : Representation.centerAutomorphism tau z = z⁻¹ := by
        apply Subtype.ext
        exact hinverts z
      rw [hz, map_inv]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
