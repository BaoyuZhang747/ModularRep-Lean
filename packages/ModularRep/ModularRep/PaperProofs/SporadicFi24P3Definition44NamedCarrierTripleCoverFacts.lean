import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterKernel
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts

/-! Elementary order-three cover consequences on the original map and
centre action, including nontriviality of an automorphism inverting it. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTripleCoverFacts

open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts

universe u

theorem movesCenter_of_card_three_of_inverts
    {X : Type u} [Group X] (tau : MulAut X)
    (hcard : Nat.card (Subgroup.center X) = 3)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹) :
    ∃ z : Subgroup.center X, tau (z : X) ≠ z := by
  let : Finite (Subgroup.center X) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Nontrivial (Subgroup.center X) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center X)
  refine ⟨z, ?_⟩
  intro hfixed
  have hinv : z⁻¹ = z := Subtype.ext ((hinverts z).symm.trans hfixed)
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    calc
      z * z = z⁻¹ * z := congrArg (fun w : Subgroup.center X => w * z) hinv.symm
      _ = 1 := inv_mul_cancel z
  have hz3 : z ^ 3 = 1 := by
    simpa only [hcard] using (pow_card_eq_one' (x := z))
  apply hz
  calc
    z = z ^ 2 * z := by rw [hz2, one_mul]
    _ = z ^ 3 := (pow_succ z 2).symm
    _ = 1 := hz3

theorem center_card_three_of_fullCover
    {X S : Type u} [Group X] [Group S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3) :
    Nat.card (Subgroup.center X) = 3 := by
  rw [← ker_eq_center_of_simple_quotient q hq.1 hs hna]
  exact hkernel

def ellPrimeCover_of_fullCover_kernel_three
    {p : ℕ} (hp : p.Prime) (hpne : p ≠ 3)
    {X S : Type u} [Group X] [Fintype X] [Group S] [Fintype S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3) : EllPrimeCoverSource p X :=
  ellPrimeCover_of_fullCover q hq hs hna (by
    rw [hkernel]
    exact fun h => hpne ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTripleCoverFacts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
