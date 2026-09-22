import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover
import Mathlib.GroupTheory.Abelianization.Defs

/-! Retain an actual universal full cover when its kernel has prime-to-p
order. Perfectness and maximality follow from the stored universal property.
The commutator cancellation below is a neutral elementary proof. -/

noncomputable section
open scoped commutatorElement

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts

open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

universe u

theorem perfect_of_universalCentralExtension
    {X S : Type u} [Group X] [Group S]
    (q : X →* S) (hq : IsUniversalCentralExtension q) : commutator X = ⊤ := by
  let f : S × Abelianization X →* S := MonoidHom.fst _ _
  have hf : IsCentralExtension f := by
    constructor
    · intro s
      exact ⟨(s, 1), rfl⟩
    · rintro ⟨s, a⟩ h
      change s = 1 at h
      subst s
      rw [Subgroup.mem_center_iff]
      intro y
      apply Prod.ext
      · change y.1 * 1 = 1 * y.1
        simp
      · change y.2 * a = a * y.2
        exact mul_comm _ _
  obtain ⟨l, hl, unique⟩ := hq.2 (S × Abelianization X) f hf
  have heq : q.prod (Abelianization.of : X →* Abelianization X) =
      q.prod (1 : X →* Abelianization X) :=
    (unique _ (by ext x; rfl)).trans (unique _ (by ext x; rfl)).symm
  rw [← Abelianization.ker_of X]
  apply top_unique
  intro x _
  change Abelianization.of x = 1
  exact congrArg Prod.snd (DFunLike.congr_fun heq x)

theorem ker_eq_center_of_simple_quotient
    {X S : Type u} [Group X] [Group S]
    (q : X →* S) (hq : IsCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S) :
    q.ker = Subgroup.center X := by
  apply le_antisymm hq.2
  intro z hz
  have hzS : q z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨x, rfl⟩ := hq.1 s
    simpa only [map_mul] using congrArg q (Subgroup.mem_center_iff.mp hz x)
  change q z = 1
  rw [center_eq_bot_of_nonabelian_simple hs hna] at hzS
  exact Subgroup.mem_bot.mp hzS

theorem lift_surjective_of_central_comp
    {U D S : Type u} [Group U] [Group D] [Group S]
    (f : D →* S) (lift : U →* D)
    (hcomp : Function.Surjective (f.comp lift))
    (hcentral : f.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤) : Function.Surjective lift := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← hperfect, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨ux, hux⟩ := hcomp (f x)
  obtain ⟨uy, huy⟩ := hcomp (f y)
  change f (lift ux) = f x at hux
  change f (lift uy) = f y at huy
  have hx : (lift ux)⁻¹ * x ∈ Subgroup.center D :=
    hcentral ((MonoidHom.eq_iff f).mp hux.symm)
  have hy : (lift uy)⁻¹ * y ∈ Subgroup.center D :=
    hcentral ((MonoidHom.eq_iff f).mp huy.symm)
  have hxcomm : Commute ((lift ux)⁻¹ * x) y :=
    (Subgroup.mem_center_iff.mp hx y).symm
  have hycomm : Commute (lift ux) ((lift uy)⁻¹ * y) :=
    Subgroup.mem_center_iff.mp hy (lift ux)
  refine ⟨⁅ux, uy⁆, ?_⟩
  rw [map_commutatorElement]
  symm
  calc
    ⁅x, y⁆ = ⁅lift ux * ((lift ux)⁻¹ * x), y⁆ := by rw [mul_inv_cancel_left]
    _ = ⁅lift ux, y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hxcomm.commutator_eq]
      simp
    _ = ⁅lift ux, lift uy * ((lift uy)⁻¹ * y)⁆ := by rw [mul_inv_cancel_left]
    _ = ⁅lift ux, lift uy⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hycomm.commutator_eq]
      simp

def ellPrimeCover_of_fullCover
    {p : ℕ} {X S : Type u} [Group X] [Fintype X] [Group S] [Fintype S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hpker : ¬ p ∣ Nat.card q.ker) : EllPrimeCoverSource p X where
  S := S
  quotient := q
  quotient_surjective := hq.1.1
  quotient_kernel := ker_eq_center_of_simple_quotient q hq.1 hs hna
  perfect := perfect_of_universalCentralExtension q hq
  simple := hs
  nonabelian := hna
  centerPrimeTo := by rwa [← ker_eq_center_of_simple_quotient q hq.1 hs hna]
  maximal := by
    intro D _ _ f hf hz hperfect _
    obtain ⟨l, hl, _⟩ := hq.2 D f ⟨hf, hz⟩
    have hcomp : Function.Surjective (f.comp l) := by
      rw [hl]
      exact hq.1.1
    exact ⟨l, lift_surjective_of_central_comp f l hcomp hz hperfect, hl⟩

def ellPrimeCover_of_fullCover_kernel_two
    {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2)
    {X S : Type u} [Group X] [Fintype X] [Group S] [Fintype S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 2) : EllPrimeCoverSource p X :=
  ellPrimeCover_of_fullCover q hq hs hna (by
    rw [hkernel]
    exact fun h => hpne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
