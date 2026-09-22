import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralStabilizer
import Mathlib.RingTheory.IntegralDomain

/-! For a faithful scalar sector, an outer automorphism inverting a centre
of order greater than two cannot stabilize its Brauer character. Literal
outer order two therefore makes the full character stabilizer inner.
The ambient group remains the original group, including its centre. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCenterAmbient

open ModularRep
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierFaithfulCentralStabilizer

universe u

theorem movesCenter_of_faithfulScalar_of_inverts
    {G k : Type u} [Group G] [Finite G] [Field k]
    (nu : Subgroup.center G →* kˣ) (hnu : Function.Injective nu)
    (tau : MulAut G) (hcard : 2 < Nat.card (Subgroup.center G))
    (hinverts : ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹) :
    ∃ z : Subgroup.center G, tau (z : G) ≠ z := by
  let : IsCyclic (Subgroup.center G) :=
    isCyclic_of_injective_ringHom ((Units.coeHom k).comp nu)
      (Units.val_injective.comp hnu)
  obtain ⟨z, hz⟩ := exists_pow_ne_one_of_isCyclic
    (G := Subgroup.center G) (k := 2) (by decide) hcard
  refine ⟨z, ?_⟩
  intro hfixed
  have hinv : z⁻¹ = z := Subtype.ext ((hinverts z).symm.trans hfixed)
  apply hz
  calc
    z ^ 2 = z * z := pow_two z
    _ = z⁻¹ * z := congrArg (fun w : Subgroup.center G => w * z) hinv.symm
    _ = 1 := inv_mul_cancel z

theorem outer_decomposition_of_card_two_of_movesCenter
    {G : Type u} [Group G]
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (tau : MulAut G)
    (movesCenter : ∃ z : Subgroup.center G, tau (z : G) ≠ z) :
    ∀ alpha : MulAut G, ∃ x : G,
      alpha = MulAut.conj x ∨ alpha = MulAut.conj x * tau := by
  let q : (MulAut G)ᵐᵒᵖ →* LiteralOuterQuotient G :=
    QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range
  have htau : q (MulOpposite.op tau) ≠ 1 := by
    intro h
    have hm : MulOpposite.op tau ∈
        (RepresentationWeight.innerInverseOpHom (G := G)).range :=
      (QuotientGroup.eq_one_iff (MulOpposite.op tau)).mp h
    obtain ⟨x, hx⟩ := hm
    have hx' : MulAut.conj x⁻¹ = tau := congrArg MulOpposite.unop hx
    obtain ⟨z, hz⟩ := movesCenter
    apply hz
    rw [← hx']
    change x⁻¹ * (z : G) * (x⁻¹)⁻¹ = (z : G)
    rw [Subgroup.mem_center_iff.mp z.2 x⁻¹, mul_inv_cancel_right]
  intro alpha
  by_cases ha : q (MulOpposite.op alpha) = 1
  · have hm : MulOpposite.op alpha ∈
        (RepresentationWeight.innerInverseOpHom (G := G)).range :=
      (QuotientGroup.eq_one_iff (MulOpposite.op alpha)).mp ha
    obtain ⟨x, hx⟩ := hm
    exact ⟨x⁻¹, Or.inl (congrArg MulOpposite.unop hx).symm⟩
  · have hsame : q (MulOpposite.op alpha) = q (MulOpposite.op tau) :=
      ((Nat.card_eq_two_iff' (1 : LiteralOuterQuotient G)).mp hOuter).unique ha htau
    have hm : (MulOpposite.op tau)⁻¹ * MulOpposite.op alpha ∈
        (RepresentationWeight.innerInverseOpHom (G := G)).range := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ((MulOpposite.op tau)⁻¹ * MulOpposite.op alpha) = 1
      rw [map_mul, map_inv, hsame, inv_mul_cancel]
    obtain ⟨x, hx⟩ := hm
    have hx' : MulAut.conj x⁻¹ = alpha * tau⁻¹ := congrArg MulOpposite.unop hx
    exact ⟨x⁻¹, Or.inr ((mul_inv_eq_iff_eq_mul).mp hx'.symm)⟩

theorem centralKernel_eq_bot_of_faithful_scalar
    {k G U : Type u}
    [Field k] [Group G] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [IsAlgClosed k]
    (rho : Representation k G U) [rho.IsIrreducible]
    (nu : Subgroup.center G →* kˣ)
    (hnu : Function.Injective nu)
    (hscalar : ∀ z : Subgroup.center G,
      rho z.1 = (nu z : k) • (1 : Module.End k U)) :
    Subgroup.center G ⊓ rho.ker = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  let z : Subgroup.center G := ⟨x, hx.1⟩
  have hrho : rho z.1 = 1 := hx.2
  have hs : (nu z : k) • (1 : Module.End k U) = 1 :=
    (hscalar z).symm.trans hrho
  have hv : (nu z : k) = 1 := by
    apply (Representation.scalarIntertwiningEquiv rho).injective
    apply Representation.IntertwiningMap.toLinearMap_injective rho rho
    simpa only [Representation.scalarIntertwiningEquiv_toLinearMap,
      one_smul, Module.End.one_eq_id] using hs
  have hnu1 : nu z = nu 1 := by
    apply Units.ext
    simpa only [map_one, Units.val_one] using hv
  exact congrArg Subtype.val (hnu hnu1)

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [Group G] [Fintype G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (nu : Subgroup.center G →* kˣ) (phi : ScalarBrauerSector iota nu)

theorem chosen_centralKernel_eq_bot (hnu : Function.Injective nu) :
    Subgroup.center G ⊓ (chosenIBrRepresentation iota phi.1).ρ.ker = ⊥ := by
  let : Representation.IsIrreducible (chosenIBrRepresentation iota phi.1).ρ :=
    (Classical.choose_spec phi.1.2).1
  exact centralKernel_eq_bot_of_faithful_scalar
    (chosenIBrRepresentation iota phi.1).ρ nu hnu phi.2

theorem stabilizer_inner
    (hnu : Function.Injective nu)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (tau : MulAut G) (hcard : 2 < Nat.card (Subgroup.center G))
    (hinverts : ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹)
    (a : ActualAutAmbient iota phi.1) :
    ∃ x : G, a.1.unop = MulAut.conj x := by
  have hfixed : IrreducibleBrauerCharacter.twist iota phi.1 a.1.unop = phi.1 := a.2
  have hfixCenter : ∀ z : Subgroup.center G, a.1.unop z.1 = z.1 := by
    apply fixes_center_of_faithful_brauer_fixed iota
      (chosenIBrRepresentation iota phi.1) (Classical.choose_spec phi.1.2).1
      (chosen_centralKernel_eq_bot iota nu phi hnu) a.1.unop
    rw [← chosenIBrRepresentation_character iota phi.1]
    exact congrArg Subtype.val hfixed
  have hm := movesCenter_of_faithfulScalar_of_inverts nu hnu tau hcard hinverts
  exact inner_of_center_fixed_of_outer_decomposition tau
    (outer_decomposition_of_card_two_of_movesCenter hOuter tau hm) hm a.1.unop hfixCenter

/-- The original group's conjugation action realizes the full Brauer
stabilizer. This is a surjection; the original centre is retained. -/
theorem originalAmbient_surjective
    (hnu : Function.Injective nu)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (tau : MulAut G) (hcard : 2 < Nat.card (Subgroup.center G))
    (hinverts : ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹) :
    Function.Surjective (innerEmbedding iota phi.1) := by
  intro a
  obtain ⟨x, hx⟩ := stabilizer_inner iota nu phi hnu hOuter tau hcard hinverts a
  refine ⟨x⁻¹, ?_⟩
  apply Subtype.ext
  change MulOpposite.op (MulAut.conj ((x⁻¹)⁻¹)) = a.1
  simpa only [inv_inv, MulOpposite.op_unop] using congrArg MulOpposite.op hx.symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCenterAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
