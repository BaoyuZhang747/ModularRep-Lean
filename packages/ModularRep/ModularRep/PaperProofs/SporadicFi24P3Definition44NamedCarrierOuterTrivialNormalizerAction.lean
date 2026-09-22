import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPairComparison

/-! The original normalizer realizes the full action range when the actual
outer quotient is trivial. No faithful-sector or centre-size input is needed. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialNormalizerAction

open ModularRep
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction
open SporadicFi24P3Definition44NamedCarrierOriginalPairComparison

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G]

theorem normalizerAction_mem_range_iff_of_outer_card_one
    (iota : PrimeRegularRootEmbedding p k K G) (chi : IBr iota)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1)
    (Q : Subgroup G) (alpha : MulAut G) :
    alpha ∈ (normalizerAction Q).range ↔
      (∀ z : Subgroup.center G, alpha z.val = z.val) ∧
      Q.comap alpha.toMonoidHom = Q ∧ MulOpposite.op alpha • chi = chi := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨?_, normalizer_stable Q d, inner_brauer_fixed iota chi d.val⟩
    intro z
    change d.val * z.val * d.val⁻¹ = z.val
    rw [Subgroup.mem_center_iff.mp z.property d.val, mul_inv_cancel_right]
  · rintro ⟨_, hQ, hfixed⟩
    let a0 : ActualAutAmbient iota chi :=
      ⟨(MulOpposite.op alpha)⁻¹,
        (MulAction.stabilizer (MulAut G)ᵐᵒᵖ chi).inv_mem hfixed⟩
    have hsurj : Function.Surjective (innerEmbedding iota chi) :=
      originalAmbient_surjective_of_outer_card_one iota chi hOuter
    obtain ⟨x, hx⟩ := hsurj a0
    have hxaut : MulAut.conj x = alpha := by
      have h := congrArg (actualConjugation iota chi) hx
      rw [actualConjugation_inner] at h
      change MulAut.conj x = (alpha⁻¹)⁻¹ at h
      simpa only [inv_inv] using h
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := by
      apply (mem_normalizer_iff_stable Q x).mpr
      rw [hxaut]
      exact hQ
    exact ⟨⟨x, hxQ⟩, hxaut⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialNormalizerAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
