import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
import Mathlib.SetTheory.Cardinal.Finite

/-! The selected outer representative supplies the two actions from the
actual outer quotient of order two. Its square is not an extra hypothesis. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterRepresentativeDecomposition

open ModularRep
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

universe u

theorem two_cosets_of_outer_card_two
    {G : Type u} [Group G]
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (tau : MulAut G)
    (htau : QuotientGroup.mk'
      (RepresentationWeight.innerInverseOpHom (G := G)).range
      (MulOpposite.op tau) ≠ 1) :
    ∀ alpha : MulAut G, ∃ x : G,
      alpha = MulAut.conj x ∨ alpha = MulAut.conj x * tau := by
  let q : (MulAut G)ᵐᵒᵖ →* LiteralOuterQuotient G :=
    QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range
  intro alpha
  by_cases ha : q (MulOpposite.op alpha) = 1
  · obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff (MulOpposite.op alpha)).mp ha
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

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterRepresentativeDecomposition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
