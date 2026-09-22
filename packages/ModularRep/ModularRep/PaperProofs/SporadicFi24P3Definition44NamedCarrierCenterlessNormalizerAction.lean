import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison

/-! The actual centreless normalizer action and its full automorphism range.
The range uses only the original character, subgroup and trivial centre. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessNormalizerAction

open ModularRep ModularRep.CharacterWeight
open CyclicOuterLemma37Concrete
open TypeBCentralKernelNormalizerInertia
open TypeBCentralKernelWeightTransport (localMk)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
open SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance
  (stableNormalizerAut stableNormalizerAut_coe)

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G]
variable (iota : PrimeRegularRootEmbedding p k K G) (chi : IBr iota)

def normalizerAction (Q : Subgroup G) :
    embeddedNormalizer (innerEmbedding iota chi) Q →* MulAut G :=
  (actualConjugation iota chi).comp (embeddedNormalizer (innerEmbedding iota chi) Q).subtype

theorem mem_normalizer_iff_stable (hcenter : Subgroup.center G = ⊥)
    (Q : Subgroup G) (a : ActualAutAmbient iota chi) :
    a ∈ embeddedNormalizer (innerEmbedding iota chi) Q ↔
      Q.comap (actualConjugation iota chi a).toMonoidHom = Q := by
  let : Fintype G := Fintype.ofFinite G
  constructor
  · intro ha
    exact embedded_radical_stable iota chi hcenter Q ⟨a, ha⟩
  · exact mem_embeddedNormalizer_of_actualConjugation_stable iota chi Q a

theorem normalizerAction_mem_range_iff (hcenter : Subgroup.center G = ⊥)
    (Q : Subgroup G) (alpha : MulAut G) :
    alpha ∈ (normalizerAction iota chi Q).range ↔
      (∀ z : Subgroup.center G, alpha z.val = z.val) ∧
      Q.comap alpha.toMonoidHom = Q ∧ MulOpposite.op alpha • chi = chi := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨?_, embedded_radical_stable iota chi hcenter Q d,
      actualConjugation_brauer_fixed iota chi d.val⟩
    intro z
    have hz : z.val = 1 := Subgroup.mem_bot.mp (hcenter ▸ z.property)
    rw [hz, map_one]
  · rintro ⟨_, hQ, hfixed⟩
    let a : ActualAutAmbient iota chi :=
      ⟨(MulOpposite.op alpha)⁻¹,
        (MulAction.stabilizer (MulAut G)ᵐᵒᵖ chi).inv_mem hfixed⟩
    have ha : actualConjugation iota chi a = alpha := by
      change (alpha⁻¹)⁻¹ = alpha
      exact inv_inv alpha
    have hmem : a ∈ embeddedNormalizer (innerEmbedding iota chi) Q := by
      apply (mem_normalizer_iff_stable iota chi hcenter Q a).mpr
      rw [ha]
      exact hQ
    exact ⟨⟨a, hmem⟩, ha⟩

theorem embedded_center_central (hcenter : Subgroup.center G = ⊥) :
    (Subgroup.center G).map (innerEmbedding iota chi) ≤
      Subgroup.center (ActualAutAmbient iota chi) := by
  rw [hcenter, Subgroup.map_bot]
  exact bot_le

theorem ordinary_quotient_conjugation (hcenter : Subgroup.center G = ⊥)
    (Q : Subgroup G) (d : embeddedNormalizer (innerEmbedding iota chi) Q)
    (n : Subgroup.normalizer (Q : Set G)) :
    localAut Q (actualConjugation iota chi d.val)
        (embedded_radical_stable iota chi hcenter Q d) (localMk Q n) =
      localMk Q ((normalizerBaseEquiv (innerEmbedding iota chi)
        (innerEmbedding_injective iota chi hcenter) Q).symm
          (MulAut.conjNormal d (normalizerBaseEquiv (innerEmbedding iota chi)
            (innerEmbedding_injective iota chi hcenter) Q n))) := by
  rw [localAut_mk]
  apply congrArg (localMk Q)
  apply (normalizerBaseEquiv (innerEmbedding iota chi)
    (innerEmbedding_injective iota chi hcenter) Q).injective
  rw [MulEquiv.apply_symm_apply]
  have hn : normalizerAut Q (actualConjugation iota chi d.val)
      (embedded_radical_stable iota chi hcenter Q d) n =
      stableNormalizerAut Q (actualConjugation iota chi d.val)
        (embedded_radical_stable iota chi hcenter Q d) n := by
    apply Subtype.ext
    rw [normalizerAut_coe, stableNormalizerAut_coe]
  rw [hn]
  exact normalizerBaseEquiv_conjugation iota chi hcenter Q d n

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessNormalizerAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
