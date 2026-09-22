import ModularRep.NormalCoreTransport

/-!
# Subgroups under a central prime-to-p quotient

The map is injective on p-subgroups. Centrality makes each such subgroup
normal in the full preimage of its image, so equal images imply equality.
The canonical inverse is the p-core of the full preimage, mapped upstairs.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups

open ModularRep

universe u

theorem injOn_pSubgroup_of_primeTo_ker
    {p : ℕ} (hp : p.Prime) {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hker : ¬ p ∣ Nat.card f.ker)
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Set.InjOn f Q := by
  apply (Set.injOn_iff_map_eq_one f Q).mpr
  intro a ha hfa
  obtain ⟨n, hn⟩ := hQ.exists_orderOf_dvd_pow (⟨a, ha⟩ : Q)
  have hpn : orderOf a ∣ p ^ n := by
    simpa only [Subgroup.orderOf_mk] using hn
  have hkn : orderOf a ∣ Nat.card f.ker := by
    rw [Subgroup.orderOf_coe (⟨a, hfa⟩ : f.ker)]
    exact orderOf_dvd_natCard (⟨a, hfa⟩ : f.ker)
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    ((hp.coprime_iff_not_dvd.mpr hker).symm.pow_right n) hkn hpn

theorem normal_in_image_preimage
    {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hcentral : f.ker ≤ Subgroup.center G)
    (Q : Subgroup G) :
    (Q.subgroupOf ((Q.map f).comap f)).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  rw [Subgroup.comap_map_eq]
  exact sup_le Q.le_normalizer
    (hcentral.trans (Subgroup.center_le_normalizer (Q : Set G)))

theorem map_pSubgroup_injective
    {p : ℕ} (hp : p.Prime) {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hcentral : f.ker ≤ Subgroup.center G)
    (hker : ¬ p ∣ Nat.card f.ker)
    (Q R : Subgroup G) (hQ : IsPGroup p Q) (hR : IsPGroup p R)
    (hmap : Q.map f = R.map f) : Q = R := by
  let T := (Q.map f).comap f
  have hQT : Q ≤ T := Subgroup.le_comap_map f Q
  have hRT : R ≤ T := by
    simpa only [T, hmap] using Subgroup.le_comap_map f R
  let _ : (Q.subgroupOf T).Normal := normal_in_image_preimage f hcentral Q
  let _ : (R.subgroupOf T).Normal := by
    change (R.subgroupOf ((Q.map f).comap f)).Normal
    rw [hmap]
    exact normal_in_image_preimage f hcentral R
  let P := (pCore p T).map T.subtype
  have hQP : Q ≤ P := by
    intro x hx
    exact ⟨⟨x, hQT hx⟩,
      normal_pSubgroup_le_pCore p (Q.subgroupOf T) hQ.comap_subtype hx, rfl⟩
  have hRP : R ≤ P := by
    intro x hx
    exact ⟨⟨x, hRT hx⟩,
      normal_pSubgroup_le_pCore p (R.subgroupOf T) hR.comap_subtype hx, rfl⟩
  have hinj := injOn_pSubgroup_of_primeTo_ker hp f hker P
    ((pCore_isPGroup p T).map T.subtype)
  ext x
  constructor
  · intro hx
    have hfx : f x ∈ R.map f := by rw [← hmap]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hfx
    have hxy : x = y := hinj (hQP hx) (hRP hy) heq.symm
    rwa [hxy]
  · intro hx
    have hfx : f x ∈ Q.map f := by rw [hmap]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hfx
    have hxy : x = y := hinj (hRP hx) (hQP hy) heq.symm
    rwa [hxy]

theorem exists_pSubgroup_lift
    {p : ℕ} [Fact p.Prime] {G H : Type u}
    [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (R : Subgroup H) (hR : IsPGroup p R) :
    ∃ Q : Subgroup G, IsPGroup p Q ∧ Q.map f = R := by
  classical
  let T := R.comap f
  let fR : T →* R := {
    toFun := fun x => ⟨f x.1, x.2⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun x y => Subtype.ext (map_mul f x.1 y.1) }
  have hfR : Function.Surjective fR := by
    intro r
    obtain ⟨x, hx⟩ := hf r.1
    have hxT : x ∈ T := by
      change f x ∈ R
      rw [hx]
      exact r.2
    exact ⟨⟨x, hxT⟩, Subtype.ext hx⟩
  let S : Sylow p T := default
  have htop : (S : Subgroup T).map fR = ⊤ :=
    ((S.mapSurjective hfR).is_maximal' (hR.to_subgroup ⊤) le_top).symm
  refine ⟨(S : Subgroup T).map T.subtype, S.isPGroup'.map T.subtype, ?_⟩
  ext y
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    exact t.2
  · intro hy
    have hm : (⟨y, hy⟩ : R) ∈ (S : Subgroup T).map fR := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨t, ht, heq⟩ := hm
    exact ⟨t.1, ⟨t, ht, rfl⟩, congrArg Subtype.val heq⟩

def pSubgroupLift
    (p : ℕ) {G H : Type u} [Group G] [Group H]
    (f : G →* H) (R : Subgroup H) : Subgroup G :=
  (pCore p (R.comap f)).map (R.comap f).subtype

theorem pSubgroupLift_isPGroup
    (p : ℕ) {G H : Type u} [Group G] [Group H]
    (f : G →* H) (R : Subgroup H) :
    IsPGroup p (pSubgroupLift p f R) :=
  (pCore_isPGroup p (R.comap f)).map (R.comap f).subtype

theorem pSubgroupLift_map
    {p : ℕ} [Fact p.Prime] {G H : Type u}
    [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G)
    (R : Subgroup H) (hR : IsPGroup p R) :
    (pSubgroupLift p f R).map f = R := by
  obtain ⟨Q, hQ, hmap⟩ := exists_pSubgroup_lift f hf R hR
  have hQT : Q ≤ R.comap f := by
    rw [← hmap]
    exact Subgroup.le_comap_map f Q
  let _ : (Q.subgroupOf (R.comap f)).Normal := by
    rw [← hmap]
    exact normal_in_image_preimage f hcentral Q
  have hQle : Q ≤ pSubgroupLift p f R := by
    intro x hx
    exact ⟨⟨x, hQT hx⟩,
      normal_pSubgroup_le_pCore p (Q.subgroupOf (R.comap f)) hQ.comap_subtype hx,
      rfl⟩
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr (Subgroup.map_subtype_le _)
  · calc
      R = Q.map f := hmap.symm
      _ ≤ (pSubgroupLift p f R).map f := Subgroup.map_mono hQle

theorem existsUnique_pSubgroup_lift
    {p : ℕ} [hp : Fact p.Prime] {G H : Type u}
    [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G) (hker : ¬ p ∣ Nat.card f.ker)
    (R : Subgroup H) (hR : IsPGroup p R) :
    ∃! Q : Subgroup G, IsPGroup p Q ∧ Q.map f = R := by
  refine ⟨pSubgroupLift p f R,
    ⟨pSubgroupLift_isPGroup p f R, pSubgroupLift_map f hf hcentral R hR⟩, ?_⟩
  intro Q hQ
  exact map_pSubgroup_injective hp.out f hcentral hker Q (pSubgroupLift p f R)
    hQ.1 (pSubgroupLift_isPGroup p f R)
    (hQ.2.trans (pSubgroupLift_map f hf hcentral R hR).symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
