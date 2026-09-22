import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! The specified prime-centre split, derived from the kernel dichotomy. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorSplit

theorem hom_eq_one_or_injective_of_prime_card
    {G M : Type*} [Group G] [Monoid M]
    (hcard : (Nat.card G).Prime) (nu : G →* M) :
    nu = 1 ∨ Function.Injective nu := by
  let _ : Fact (Nat.card G).Prime := ⟨hcard⟩
  rcases nu.ker.eq_bot_or_eq_top_of_prime_card with h | h
  · exact Or.inr ((MonoidHom.ker_eq_bot_iff nu).mp h)
  · exact Or.inl (MonoidHom.ker_eq_top_iff.mp h)

theorem injective_ne_one_of_prime_card
    {G M : Type*} [Group G] [Monoid M]
    (hcard : (Nat.card G).Prime) (nu : G →* M)
    (hnu : Function.Injective nu) : nu ≠ 1 := by
  intro h
  let _ : Subsingleton G := ⟨fun x y => hnu (by rw [h]; rfl)⟩
  exact hcard.ne_one (Nat.card_unique (α := G))

theorem injective_iff_ne_one_of_prime_card
    {G M : Type*} [Group G] [Monoid M]
    (hcard : (Nat.card G).Prime) (nu : G →* M) :
    Function.Injective nu ↔ nu ≠ 1 := by
  constructor
  · exact injective_ne_one_of_prime_card hcard nu
  · intro h
    exact (hom_eq_one_or_injective_of_prime_card hcard nu).resolve_left h

open SporadicFi24CentralSectorAssemblyLemma56Actual

universe u
theorem centralSector_smul_one {k G : Type u} [Field k] [Group G]
    (a : (MulAut G)ᵐᵒᵖ) :
    a • (1 : CentralSector (k := k) (X := G)) = 1 := by
  ext z
  rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorSplit


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
