import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups
import ModularRep.PaperProofs.NavarroTiep23cFixedCentralQuotientSource

/-!
# Normalizers and radicality under a central prime-to-p quotient

All group transport is derived from the literal homomorphism. The final
constructor discharges both fields of the existing fixed-subgroup packet.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals

open ModularRep
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups

universe u

theorem map_conj_naturality
    {G H : Type u} [Group G] [Group H]
    (f : G →* H) (Q : Subgroup G) (g : G) :
    (Q.map (MulAut.conj g)).map f =
      (Q.map f).map (MulAut.conj (f g)) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun k : G →* H => Q.map k)
  ext x
  simp

theorem normalizer_comap_of_central_primeTo
    {p : ℕ} (hp : p.Prime) {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hcentral : f.ker ≤ Subgroup.center G)
    (hker : ¬ p ∣ Nat.card f.ker) (Q : Subgroup G) (hQ : IsPGroup p Q) :
    (Subgroup.normalizer (Q.map f : Set H)).comap f =
      Subgroup.normalizer (Q : Set G) := by
  ext g
  change f g ∈ Subgroup.normalizer (Q.map f : Set H) ↔
    g ∈ Subgroup.normalizer (Q : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro hg
    exact map_pSubgroup_injective hp f hcentral hker
      (Q.map (MulAut.conj g)) Q (hQ.map (MulAut.conj g).toMonoidHom) hQ
      ((map_conj_naturality f Q g).trans hg)
  · intro hg
    rw [← map_conj_naturality, hg]

theorem normalizerMap_surjective_of_central_primeTo
    {p : ℕ} (hp : p.Prime) {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G) (hker : ¬ p ∣ Nat.card f.ker)
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Function.Surjective (normalizerMap f Q) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.1
  have hxN : x ∈ Subgroup.normalizer (Q : Set G) := by
    rw [← normalizer_comap_of_central_primeTo hp f hcentral hker Q hQ]
    change f x ∈ Subgroup.normalizer (Q.map f : Set H)
    rw [hx]
    exact y.2
  exact ⟨⟨x, hxN⟩, Subtype.ext hx⟩

theorem pCore_map_of_central_primeTo
    {p : ℕ} [hp : Fact p.Prime] {G H : Type u}
    [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G) (hker : ¬ p ∣ Nat.card f.ker) :
    (pCore p G).map f = pCore p H := by
  let Q := pSubgroupLift p f (pCore p H)
  have hQp : IsPGroup p Q := pSubgroupLift_isPGroup p f _
  have hQmap : Q.map f = pCore p H :=
    pSubgroupLift_map f hf hcentral _ (pCore_isPGroup p H)
  let _ : Q.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    rw [← normalizer_comap_of_central_primeTo hp.out f hcentral hker Q hQp,
      hQmap, Subgroup.normalizer_eq_top, Subgroup.comap_top]
  apply le_antisymm
  · let _ : ((pCore p G).map f).Normal := (pCore_normal p G).map f hf
    exact normal_pSubgroup_le_pCore p _ ((pCore_isPGroup p G).map f)
  · rw [← hQmap]
    exact Subgroup.map_mono (normal_pSubgroup_le_pCore p Q hQp)

theorem normalizerPCore_map_of_central_primeTo
    {p : ℕ} [hp : Fact p.Prime] {G H : Type u}
    [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G) (hker : ¬ p ∣ Nat.card f.ker)
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    (normalizerPCore p Q).map f = normalizerPCore p (Q.map f) := by
  let N := Subgroup.normalizer (Q : Set G)
  let Nbar := Subgroup.normalizer (Q.map f : Set H)
  let fN : N →* Nbar := normalizerMap f Q
  have hfN : Function.Surjective fN :=
    normalizerMap_surjective_of_central_primeTo hp.out f hf hcentral hker Q hQ
  have hk : fN.ker = f.ker.subgroupOf N := by
    ext x
    change fN x = 1 ↔ f x.1 = 1
    exact Subtype.ext_iff
  have hcN : fN.ker ≤ Subgroup.center N := by
    intro x hx
    have hxk : x.1 ∈ f.ker := by rw [hk] at hx; exact hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral hxk) y.1
  have hcard : Nat.card fN.ker = Nat.card f.ker := by
    rw [hk]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (hcentral.trans (Subgroup.center_le_normalizer (Q : Set G)))).toEquiv
  have hkN : ¬ p ∣ Nat.card fN.ker := by rwa [hcard]
  have hcore : (pCore p N).map fN = pCore p Nbar :=
    pCore_map_of_central_primeTo fN hfN hcN hkN
  unfold normalizerPCore
  rw [Subgroup.map_map, ← hcore, Subgroup.map_map]
  congr 1

theorem radical_iff_map_of_central_primeTo
    {p : ℕ} [hp : Fact p.Prime] {G H : Type u}
    [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G) (hker : ¬ p ∣ Nat.card f.ker)
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    IsRadicalSubgroup p Q ↔ IsRadicalSubgroup p (Q.map f) := by
  have hc := normalizerPCore_map_of_central_primeTo f hf hcentral hker Q hQ
  constructor
  · intro hr
    change Q.map f = normalizerPCore p (Q.map f)
    rw [← hc, ← hr]
  · intro hr
    change Q = normalizerPCore p Q
    apply map_pSubgroup_injective hp.out f hcentral hker Q (normalizerPCore p Q) hQ
      ((pCore_isPGroup p (Subgroup.normalizer (Q : Set G))).map
        (Subgroup.normalizer (Q : Set G)).subtype)
    exact hr.trans hc.symm

theorem fixedCentralQuotientSource
    {p : ℕ} [hp : Fact p.Prime] {X : Type u} [Group X] [Finite X]
    (Z0 : Subgroup X) [Z0.Normal]
    (hcentral : Z0 ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup p Q) :
    NavarroTiep23cFixedCentralQuotientSource Z0 hcentral hprimeTo Q hQ := by
  let f := QuotientGroup.mk' Z0
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective Z0
  have hc : f.ker ≤ Subgroup.center X := by
    simpa only [f, QuotientGroup.ker_mk'] using hcentral
  have hk : ¬ p ∣ Nat.card f.ker := by
    simpa only [f, QuotientGroup.ker_mk'] using hprimeTo
  refine {
    radical_image :=
      (radical_iff_map_of_central_primeTo f hf hc hk Q hQ.isPGroup).mp hQ
    normalizer_image := ?_ }
  apply Subgroup.comap_injective hf
  rw [Subgroup.comap_map_eq_self
      (hc.trans (Subgroup.center_le_normalizer (Q : Set X))),
    normalizer_comap_of_central_primeTo hp.out f hc hk Q hQ.isPGroup]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
