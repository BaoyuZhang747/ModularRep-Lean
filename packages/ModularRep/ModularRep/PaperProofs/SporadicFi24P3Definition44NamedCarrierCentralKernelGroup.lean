import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Central faithfulness after quotienting by the actual central kernel.
The three centre lemmas are narrow copies of CompleteCollapseRelative;
no block-collapse or abstract certification endpoint is imported. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralKernelGroup

theorem map_center_le_center_of_surjective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    (Subgroup.center G).map f ≤ Subgroup.center H := by
  rintro _ ⟨z, hz, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨x, rfl⟩ := hf y
  simpa only [map_mul] using congrArg f (Subgroup.mem_center_iff.mp hz x)

theorem center_eq_of_central_quotient_centerless
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    (hK : K ≤ Subgroup.center G)
    (hcenter : Subgroup.center (G ⧸ K) = ⊥) :
    Subgroup.center G = K := by
  apply le_antisymm
  · intro z hz
    have hzmap : QuotientGroup.mk' K z ∈ Subgroup.center (G ⧸ K) :=
      map_center_le_center_of_surjective (QuotientGroup.mk' K)
        (QuotientGroup.mk'_surjective K) ⟨z, hz, rfl⟩
    rw [hcenter, Subgroup.mem_bot] at hzmap
    exact (QuotientGroup.eq_one_iff z).mp hzmap
  · exact hK

theorem center_eq_map_center_of_le_center
    {G : Type*} [Group G] [Group.IsPerfect G]
    (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center G) :
    Subgroup.center (G ⧸ Z0) =
      (Subgroup.center G).map (QuotientGroup.mk' Z0) := by
  let K : Subgroup (G ⧸ Z0) := (Subgroup.center G).map (QuotientGroup.mk' Z0)
  let : (Subgroup.center G).Normal := Subgroup.normal_of_characteristic (Subgroup.center G)
  let : K.Normal := (show (Subgroup.center G).Normal from inferInstance).map
    (QuotientGroup.mk' Z0) (QuotientGroup.mk'_surjective Z0)
  have hK : K ≤ Subgroup.center (G ⧸ Z0) :=
    map_center_le_center_of_surjective (QuotientGroup.mk' Z0)
      (QuotientGroup.mk'_surjective Z0)
  apply center_eq_of_central_quotient_centerless K hK
  let e : ((G ⧸ Z0) ⧸ K) ≃* (G ⧸ Subgroup.center G) :=
    QuotientGroup.quotientQuotientEquivQuotient Z0 (Subgroup.center G) hZ0
  apply le_antisymm
  · intro z hz
    have hez : e z ∈ Subgroup.center (G ⧸ Subgroup.center G) :=
      map_center_le_center_of_surjective e.toMonoidHom e.surjective ⟨z, hz, rfl⟩
    rw [Group.IsPerfect.center_quotient_center_eq_bot G, Subgroup.mem_bot] at hez
    rw [Subgroup.mem_bot]
    exact e.injective (hez.trans e.map_one.symm)
  · exact bot_le

theorem centralFaithful_of_factorization
    {G M : Type*} [Group G] [Group.IsPerfect G] [Monoid M]
    (rho : G →* M) (Z0 : Subgroup G) [Z0.Normal]
    (hZ0 : Z0 = Subgroup.center G ⊓ rho.ker)
    (rhoBar : G ⧸ Z0 →* M)
    (hfactor : ∀ x : G, rhoBar (QuotientGroup.mk' Z0 x) = rho x) :
    Subgroup.center (G ⧸ Z0) ⊓ rhoBar.ker = ⊥ := by
  have hZ0central : Z0 ≤ Subgroup.center G := by
    rw [hZ0]
    exact inf_le_left
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro z hz
  have hzimage : z ∈ (Subgroup.center G).map (QuotientGroup.mk' Z0) := by
    rw [← center_eq_map_center_of_le_center Z0 hZ0central]
    exact hz.1
  rcases hzimage with ⟨x, hxcenter, rfl⟩
  apply (QuotientGroup.eq_one_iff x).mpr
  rw [hZ0]
  refine ⟨hxcenter, ?_⟩
  exact MonoidHom.mem_ker.mpr ((hfactor x).symm.trans (MonoidHom.mem_ker.mp hz.2))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralKernelGroup



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
