import ModularRep.WeightTransport
import Mathlib.GroupTheory.Nilpotent

/-!
# Passage through a normal p-core

This file proves the group-theoretic and local representation parts of the
normal-core passage used in manuscript Lemma 2.6.  Every radical subgroup of
a finite group contains its p-core.  More generally, a surjective homomorphism
with p-group kernel induces a correspondence of radical subgroups containing
the kernel and an equivalence of their normaliser quotients.

The final section uses these results to send an actual representation theoretic
weight of `G` to one of `G / O_p(G)`.  Inflation of principal-block Brauer
characters, block induction, and modular character-triple isomorphisms are
deliberately not asserted here.
-/

noncomputable section

open CategoryTheory Module

namespace ModularRep

universe u v w

variable {p : ℕ} {G : Type v} {H : Type w} [Group G] [Group H]

/-- The p-core maps onto the p-core under a surjective homomorphism whose
kernel is a p-group. -/
theorem pCore_map_surjective_of_ker_isPGroup
    (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) :
    (pCore p G).map f = pCore p H := by
  apply le_antisymm
  · let _ : ((pCore p G).map f).Normal := (pCore_normal p G).map f hf
    exact normal_pSubgroup_le_pCore p _ ((pCore_isPGroup p G).map f)
  · intro y hy
    obtain ⟨x, rfl⟩ := hf y
    let R : Subgroup G := (pCore p H).comap f
    let _ : R.Normal := (pCore_normal p H).comap f
    have hR : IsPGroup p R :=
      (pCore_isPGroup p H).comap_of_ker_isPGroup f hker
    have hRle : R ≤ pCore p G := normal_pSubgroup_le_pCore p R hR
    exact ⟨x, hRle hy, rfl⟩

/-- Every radical p-subgroup of a finite group contains its p-core. -/
theorem pCore_le_of_isRadicalSubgroup [Finite G]
    (hp : p.Prime) (Q : Subgroup G) (hQ : IsRadicalSubgroup p Q) :
    pCore p G ≤ Q := by
  let P : Subgroup G := pCore p G
  let K : Subgroup G := P ⊔ Q
  let QK : Subgroup K := Q.comap K.subtype
  have hQleK : Q ≤ K := le_sup_right
  have hQmap : QK.map K.subtype = Q := by
    apply Subgroup.map_comap_eq_self
    simpa [Subgroup.range_subtype] using hQleK
  by_contra hnot
  have hQKne : QK ≠ ⊤ := by
    intro htop
    apply hnot
    intro x hx
    have hxK : x ∈ K := (show P ≤ K from le_sup_left) hx
    have hxQK : (⟨x, hxK⟩ : K) ∈ QK := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hxQK
  have hP : IsPGroup p P := pCore_isPGroup p G
  have hK : IsPGroup p K := hP.to_sup_of_normal_left hQ.isPGroup
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Group.IsNilpotent K := hK.isNilpotent
  have hlt : QK < Subgroup.normalizer (QK : Set K) :=
    Group.normalizerCondition_of_isNilpotent QK
      (lt_top_iff_ne_top.mpr hQKne)
  obtain ⟨x, hxNorm, hxNotQ⟩ := SetLike.exists_of_lt hlt
  have hxAmbientNorm : (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
    have hxMap : (x : G) ∈
        (Subgroup.normalizer (QK : Set K)).map K.subtype :=
      ⟨x, hxNorm, rfl⟩
    have hle := Subgroup.le_normalizer_map (H := QK) K.subtype hxMap
    rwa [hQmap] at hle
  obtain ⟨y, hyP, z, hzQ, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := P) (t := Q)).mp x.property
  have hzNorm : z ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer hzQ
  have hyNorm : y ∈ Subgroup.normalizer (Q : Set G) := by
    have hyEq : y = (x : G) * z⁻¹ := by
      rw [← hyz]
      simp
    rw [hyEq]
    exact (Subgroup.normalizer (Q : Set G)).mul_mem hxAmbientNorm
      ((Subgroup.normalizer (Q : Set G)).inv_mem hzNorm)
  let R : Subgroup (Subgroup.normalizer (Q : Set G)) :=
    P.comap (Subgroup.normalizer (Q : Set G)).subtype
  let _ : R.Normal := (pCore_normal p G).comap _
  have hR : IsPGroup p R := hP.comap_subtype
  have hRle : R ≤ pCore p (Subgroup.normalizer (Q : Set G)) :=
    normal_pSubgroup_le_pCore p R hR
  have hyR : (⟨y, hyNorm⟩ : Subgroup.normalizer (Q : Set G)) ∈ R :=
    hyP
  have hyCore := hRle hyR
  have hyNormalizerCore : y ∈ normalizerPCore p Q :=
    ⟨⟨y, hyNorm⟩, hyCore, rfl⟩
  have hyQ : y ∈ Q := by rwa [hQ]
  apply hxNotQ
  change (x : G) ∈ Q
  rw [← hyz]
  exact Q.mul_mem hyQ hzQ

/-- A surjection whose kernel is contained in `Q` maps the normaliser of
`Q` onto the normaliser of its image. -/
theorem map_normalizer_eq_of_surjective_of_ker_le
    (f : G →* H) (hf : Function.Surjective f)
    (Q : Subgroup G) (hker : f.ker ≤ Q) :
    (Subgroup.normalizer (Q : Set G)).map f =
      Subgroup.normalizer ((Q.map f : Subgroup H) : Set H) := by
  apply Subgroup.comap_injective hf
  rw [Subgroup.comap_normalizer_eq_of_surjective _ hf,
    Subgroup.comap_map_eq_self hker]
  exact Subgroup.comap_map_eq_self
    (hker.trans Subgroup.le_normalizer)

/-- Restriction of a homomorphism to the normalisers of a subgroup and its
image. -/
def normalizerMap (f : G →* H) (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →*
      Subgroup.normalizer ((Q.map f : Subgroup H) : Set H) :=
  (f.domRestrict (Subgroup.normalizer (Q : Set G))).codRestrict _ fun x =>
    Subgroup.le_normalizer_map f ⟨x, x.2, rfl⟩

@[simp]
theorem normalizerMap_coe (f : G →* H) (Q : Subgroup G)
    (x : Subgroup.normalizer (Q : Set G)) :
    (normalizerMap f Q x : H) = f x :=
  rfl

theorem normalizerMap_surjective
    (f : G →* H) (hf : Function.Surjective f)
    (Q : Subgroup G) (hker : f.ker ≤ Q) :
    Function.Surjective (normalizerMap f Q) := by
  intro y
  have hy : (y : H) ∈
      (Subgroup.normalizer (Q : Set G)).map f := by
    rw [map_normalizer_eq_of_surjective_of_ker_le f hf Q hker]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem normalizerMap_ker_isPGroup
    (f : G →* H) (Q : Subgroup G)
    (hker : IsPGroup p f.ker) :
    IsPGroup p (normalizerMap f Q).ker := by
  have hcomap :
      (normalizerMap f Q).ker =
        f.ker.comap (Subgroup.normalizer (Q : Set G)).subtype := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, normalizerMap]
    rw [Subtype.ext_iff]
    rfl
  rw [hcomap]
  exact hker.comap_subtype

/-- Naturality of the p-core of a normaliser under a surjection with p-group
kernel contained in the subgroup. -/
theorem normalizerPCore_map_surjective_of_ker_le
    (f : G →* H) (hf : Function.Surjective f)
    (Q : Subgroup G) (hkerLe : f.ker ≤ Q)
    (hkerP : IsPGroup p f.ker) :
    (normalizerPCore p Q).map f = normalizerPCore p (Q.map f) := by
  let fN := normalizerMap f Q
  have hfN : Function.Surjective fN :=
    normalizerMap_surjective f hf Q hkerLe
  have hkerN : IsPGroup p fN.ker :=
    normalizerMap_ker_isPGroup f Q hkerP
  have hpCore :
      (pCore p (Subgroup.normalizer (Q : Set G))).map fN =
        pCore p (Subgroup.normalizer ((Q.map f : Subgroup H) : Set H)) :=
    pCore_map_surjective_of_ker_isPGroup fN hfN hkerN
  unfold normalizerPCore
  rw [Subgroup.map_map, ← hpCore, Subgroup.map_map]
  congr 1

/-- Radicality is equivalent before and after a surjection with p-group
kernel, provided the kernel is contained in the subgroup. -/
theorem isRadicalSubgroup_iff_map_surjective_of_ker_le
    (f : G →* H) (hf : Function.Surjective f)
    (Q : Subgroup G) (hkerLe : f.ker ≤ Q)
    (hkerP : IsPGroup p f.ker) :
    IsRadicalSubgroup p Q ↔ IsRadicalSubgroup p (Q.map f) := by
  constructor
  · intro hQ
    rw [IsRadicalSubgroup,
      ← normalizerPCore_map_surjective_of_ker_le f hf Q hkerLe hkerP,
      ← hQ]
  · intro hbar
    have hnormal := normalizerPCore_map_surjective_of_ker_le
      (p := p) f hf Q hkerLe hkerP
    have hkerCore : f.ker ≤ normalizerPCore p Q := by
      intro x hx
      have hxNorm : x ∈ Subgroup.normalizer (Q : Set G) :=
        Subgroup.le_normalizer (hkerLe hx)
      let R : Subgroup (Subgroup.normalizer (Q : Set G)) :=
        f.ker.comap (Subgroup.normalizer (Q : Set G)).subtype
      let _ : R.Normal := (MonoidHom.normal_ker f).comap _
      have hR : IsPGroup p R := hkerP.comap_subtype
      have hRle : R ≤ pCore p (Subgroup.normalizer (Q : Set G)) :=
        normal_pSubgroup_le_pCore p R hR
      exact ⟨⟨x, hxNorm⟩, hRle hx, rfl⟩
    apply Subgroup.map_injective_of_ker_le f hkerLe hkerCore
    rw [hbar, hnormal]

/-- The local normaliser quotients are equivalent under a surjection whose
kernel is contained in the subgroup. -/
def normalizerQuotientEquivOfSurjectiveOfKerLE
    (f : G →* H) (hf : Function.Surjective f)
    (Q : Subgroup G) (hkerLe : f.ker ≤ Q) :
    NormalizerQuotient Q ≃* NormalizerQuotient (Q.map f) := by
  let NG := Subgroup.normalizer (Q : Set G)
  let NH := Subgroup.normalizer ((Q.map f : Subgroup H) : Set H)
  let R : Subgroup NG := Q.subgroupOf NG
  let S : Subgroup NH := (Q.map f).subgroupOf NH
  let fN : NG →* NH := normalizerMap f Q
  have hfN : Function.Surjective fN := normalizerMap_surjective f hf Q hkerLe
  have hcomap : S.comap fN = R := by
    ext x
    change f (x : G) ∈ Q.map f ↔ (x : G) ∈ Q
    rw [← Subgroup.mem_comap]
    rw [Subgroup.comap_map_eq_self hkerLe]
  let induced : NG ⧸ R →* NH ⧸ S :=
    QuotientGroup.map R S fN (by rw [hcomap])
  have hindSurj : Function.Surjective induced := by
    apply QuotientGroup.map_surjective_of_surjective R S fN
    exact QuotientGroup.mk_surjective.comp hfN
  have hindInj : Function.Injective induced := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [QuotientGroup.ker_map, hcomap]
    exact QuotientGroup.map_mk'_self R
  exact MulEquiv.ofBijective induced ⟨hindInj, hindSurj⟩

namespace RepresentationWeight

variable {K : Type u} [Field K] [CharZero K] [Finite G]

/-- A weight defined by a representation descends through the p-core. Its
subgroup is mapped by the quotient homomorphism, and its local representation
is transported through the proved isomorphism of normaliser quotients. -/
def quotientPCore (W : RepresentationWeight p K G) :
    RepresentationWeight p K (G ⧸ pCore p G) where
  prime := W.prime
  subgroup := W.subgroup.map (QuotientGroup.mk' (pCore p G))
  radical := by
    apply (isRadicalSubgroup_iff_map_surjective_of_ker_le
      (QuotientGroup.mk' (pCore p G)) (QuotientGroup.mk'_surjective _)
      W.subgroup ?_ (by
        rw [QuotientGroup.ker_mk']
        exact pCore_isPGroup p G)).mp W.radical
    rw [QuotientGroup.ker_mk']
    exact pCore_le_of_isRadicalSubgroup W.prime W.subgroup W.radical
  localRepresentation :=
    fdRepMapEquiv
      (normalizerQuotientEquivOfSurjectiveOfKerLE
        (QuotientGroup.mk' (pCore p G)) (QuotientGroup.mk'_surjective _)
        W.subgroup (by
          rw [QuotientGroup.ker_mk']
          exact pCore_le_of_isRadicalSubgroup W.prime W.subgroup W.radical))
      W.localRepresentation
  irreducible := by
    let _ : Simple W.localRepresentation := W.irreducible
    exact fdRepMapEquiv_simple _ W.localRepresentation
  defectZero :=
    fdRepMapEquiv_defectZero _ W.localRepresentation W.defectZero

@[simp]
theorem quotientPCore_subgroup (W : RepresentationWeight p K G) :
    W.quotientPCore.subgroup =
      W.subgroup.map (QuotientGroup.mk' (pCore p G)) :=
  rfl

/-- A representation theoretic weight of the p-core quotient lifts to `G`.
The subgroup is the full preimage under the quotient map and the local
representation is transported through the inverse normaliser quotient
equivalence. -/
def liftFromQuotientPCore
    (W : RepresentationWeight p K (G ⧸ pCore p G)) :
    RepresentationWeight p K G := by
  let f : G →* G ⧸ pCore p G := QuotientGroup.mk' (pCore p G)
  let Q : Subgroup G := W.subgroup.comap f
  have hker : f.ker ≤ Q := Subgroup.ker_le_comap f W.subgroup
  have hmap : Q.map f = W.subgroup := by
    apply Subgroup.map_comap_eq_self
    exact fun x _ ↦ ⟨(QuotientGroup.mk'_surjective (pCore p G) x).choose,
      (QuotientGroup.mk'_surjective (pCore p G) x).choose_spec⟩
  let e : NormalizerQuotient W.subgroup ≃* NormalizerQuotient Q := by
    rw [← hmap]
    exact (normalizerQuotientEquivOfSurjectiveOfKerLE f
      (QuotientGroup.mk'_surjective _) Q hker).symm
  exact
    { prime := W.prime
      subgroup := Q
      radical := by
        apply (isRadicalSubgroup_iff_map_surjective_of_ker_le f
          (QuotientGroup.mk'_surjective _) Q hker ?_).mpr
        · simpa [hmap] using W.radical
        · change IsPGroup p (QuotientGroup.mk' (pCore p G)).ker
          rw [QuotientGroup.ker_mk']
          exact pCore_isPGroup p G
      localRepresentation := fdRepMapEquiv e W.localRepresentation
      irreducible := by
        let _ : Simple W.localRepresentation := W.irreducible
        exact fdRepMapEquiv_simple e W.localRepresentation
      defectZero := fdRepMapEquiv_defectZero e W.localRepresentation W.defectZero }

@[simp]
theorem liftFromQuotientPCore_subgroup
    (W : RepresentationWeight p K (G ⧸ pCore p G)) :
    W.liftFromQuotientPCore.subgroup =
      W.subgroup.comap (QuotientGroup.mk' (pCore p G)) :=
  rfl

end RepresentationWeight

namespace ManuscriptVerification.NormalCoreTransport

/-- Source-shaped form of the modular character-triple lifting theorem used
in Martínez--Rizo--Rossi, Lemma 3.14.  It lifts an individual downstairs
triple isomorphism after specified global and local inflation maps.  It does
not assert the existence of an iBAW correspondence upstairs. -/
structure ModularCharacterTripleLifting
    (DownGlobal DownLocal UpGlobal UpLocal : Type*) where
  DownstairsTripleIsomorphism : DownGlobal → DownLocal → Prop
  UpstairsTripleIsomorphism : UpGlobal → UpLocal → Prop
  inflateGlobal : DownGlobal → UpGlobal
  inflateLocal : DownLocal → UpLocal
  lift : ∀ global localData,
    DownstairsTripleIsomorphism global localData →
      UpstairsTripleIsomorphism (inflateGlobal global) (inflateLocal localData)

end ManuscriptVerification.NormalCoreTransport

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
