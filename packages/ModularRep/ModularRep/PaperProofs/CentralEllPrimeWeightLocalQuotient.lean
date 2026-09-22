import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import ModularRep.PaperProofs.NavarroTiep23cFixedCentralQuotientSource

/-!
# Central prime-to-`ell` local normaliser quotient map

This experimental module supplies only the group carrier needed in the
central-quotient step of the sporadic argument.  For `L = N_X(Q)`, it builds

`qW : L / Q -> N_(X / Z0)(Q Z0 / Z0) / (Q Z0 / Z0)`

For arbitrary normal `Z0`, its raw kernel is the local intersection induced
by `(Z0 ⊔ Q).subgroupOf L`, hence customarily `(L ∩ QZ0) / Q`.  Under the
centrality hypothesis used by the manuscript this becomes the lifted central
image, hence `(QZ0) / Q`.  The auxiliary projection through the local
intersection is private; no general tower API is exported here.

All constructions before the final two theorems are source-neutral group
theory.  Those theorems use the existing fixed-`Q` Navarro--Tiep packet only
to obtain restricted-normaliser surjectivity.  There is no assumption
`Z0 <= Q`, no use of the kernel-containment normaliser-quotient shortcut, and
no character, representation, block, weight, BAW, iBAW, or final manuscript
conclusion.
-/

namespace ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

universe u v

section Generic

variable {G : Type u} {H : Type v} [Group G] [Group H]

private noncomputable def quotientEquivOfSurjectiveOfComapEq
    (f : G →* H) (hf : Function.Surjective f)
    (N : Subgroup G) [N.Normal]
    (M : Subgroup H) [M.Normal]
    (hcomap : M.comap f = N) :
    G ⧸ N ≃* H ⧸ M := by
  let induced : G ⧸ N →* H ⧸ M :=
    QuotientGroup.map N M f (by rw [hcomap])
  have hindSurj : Function.Surjective induced := by
    apply QuotientGroup.map_surjective_of_surjective N M f
    exact QuotientGroup.mk_surjective.comp hf
  have hindInj : Function.Injective induced := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [QuotientGroup.ker_map, hcomap]
    exact QuotientGroup.map_mk'_self N
  exact MulEquiv.ofBijective induced ⟨hindInj, hindSurj⟩

private theorem ordProj_card_eq_of_surjective_of_ker_card_not_dvd
    {ell : Nat} {A : Type u} {B : Type v}
    [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hker : ¬ ell ∣ Nat.card f.ker) :
    ordProj[ell] (Nat.card A) = ordProj[ell] (Nat.card B) := by
  have hcard : Nat.card A = Nat.card B * Nat.card f.ker := by
    calc
      Nat.card A = Nat.card (A ⧸ f.ker) * Nat.card f.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
      _ = Nat.card B * Nat.card f.ker := by
        rw [Nat.card_congr
          (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  rw [hcard, Nat.ordProj_mul ell Nat.card_pos.ne' Nat.card_pos.ne',
    show ordProj[ell] (Nat.card f.ker) = 1 by
      rw [Nat.factorization_eq_zero_of_not_dvd hker, pow_zero],
    mul_one]

end Generic

section Core

variable {X : Type u} [Group X]

/-- The literal local normaliser `N_X(Q)`. -/
private abbrev localNormalizer (Q : Subgroup X) : Subgroup X :=
  Subgroup.normalizer (Q : Set X)

/-- The literal copy of `Q` inside its normaliser. -/
private abbrev localQ (Q : Subgroup X) : Subgroup (localNormalizer Q) :=
  Q.subgroupOf (localNormalizer Q)

/-- The central kernel restricted to the local normaliser. -/
private abbrev localCentralKernel (Z0 Q : Subgroup X) :
    Subgroup (localNormalizer Q) :=
  Z0.subgroupOf (localNormalizer Q)

/-- The restriction, or local intersection, of `Z0 ⊔ Q` with the local
normaliser. -/
private abbrev localCentralProduct (Z0 Q : Subgroup X) :
    Subgroup (localNormalizer Q) :=
  (Z0 ⊔ Q).subgroupOf (localNormalizer Q)

/-- The image of `Q` in the central quotient. -/
private abbrev quotientRadical (Z0 Q : Subgroup X) [Z0.Normal] :
    Subgroup (X ⧸ Z0) :=
  Q.map (QuotientGroup.mk' Z0)

/-- The normaliser of the image of `Q` in the central quotient. -/
private abbrev quotientNormalizer (Z0 Q : Subgroup X) [Z0.Normal] :
    Subgroup (X ⧸ Z0) :=
  Subgroup.normalizer
    ((quotientRadical Z0 Q : Subgroup (X ⧸ Z0)) : Set (X ⧸ Z0))

/-- The image of `Q`, regarded inside its quotient-side normaliser. -/
private abbrev quotientDenominator (Z0 Q : Subgroup X) [Z0.Normal] :
    Subgroup (quotientNormalizer Z0 Q) :=
  (quotientRadical Z0 Q).subgroupOf (quotientNormalizer Z0 Q)

/-- The central quotient restricted to the two literal normalisers. -/
private abbrev quotientNormalizerMap (Z0 Q : Subgroup X) [Z0.Normal] :
    localNormalizer Q →* quotientNormalizer Z0 Q :=
  normalizerMap (QuotientGroup.mk' Z0) Q

private theorem central_le_localNormalizer
    (Z0 Q : Subgroup X) (hZ0central : Z0 ≤ Subgroup.center X) :
    Z0 ≤ localNormalizer Q :=
  hZ0central.trans (Subgroup.center_le_normalizer (Q : Set X))

private theorem localQ_le_localCentralProduct (Z0 Q : Subgroup X) :
    localQ Q ≤ localCentralProduct Z0 Q :=
  Subgroup.subgroupOf_mono (localNormalizer Q) le_sup_right

private theorem localCentralProduct_eq_sup
    (Z0 Q : Subgroup X) (hZ0central : Z0 ≤ Subgroup.center X) :
    localCentralProduct Z0 Q =
      localCentralKernel Z0 Q ⊔ localQ Q :=
  Subgroup.subgroupOf_sup
    (central_le_localNormalizer Z0 Q hZ0central) Q.le_normalizer

/-- The local intersection is canonically normal inside `N_X(Q)`. -/
private theorem localCentralProduct_normal
    (Z0 Q : Subgroup X) [Z0.Normal] :
    (localCentralProduct Z0 Q).Normal := by
  change ((Z0 ⊔ Q).subgroupOf
    (Subgroup.normalizer (Q : Set X))).Normal
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  simpa only [sup_comm] using
    (Subgroup.normalizer_le_normalizer_sup_normal
      (H := Q) (K := Z0))

private theorem quotientDenominator_comap_quotientNormalizerMap
    (Z0 Q : Subgroup X) [Z0.Normal] :
    (quotientDenominator Z0 Q).comap
        (quotientNormalizerMap Z0 Q) =
      localCentralProduct Z0 Q := by
  ext x
  change
    (QuotientGroup.mk' Z0 (x : X)) ∈
        Q.map (QuotientGroup.mk' Z0) ↔
      (x : X) ∈ Z0 ⊔ Q
  change
    (x : X) ∈
        (Q.map (QuotientGroup.mk' Z0)).comap
          (QuotientGroup.mk' Z0) ↔
      (x : X) ∈ Z0 ⊔ Q
  rw [QuotientGroup.comap_map_mk']

private theorem localQ_le_quotientDenominator_comap_quotientNormalizerMap
    (Z0 Q : Subgroup X) [Z0.Normal] :
    localQ Q ≤
      (quotientDenominator Z0 Q).comap
        (quotientNormalizerMap Z0 Q) := by
  rw [quotientDenominator_comap_quotientNormalizerMap]
  exact localQ_le_localCentralProduct Z0 Q

/-- The canonical map on local normaliser quotients.  It is a homomorphism,
not an equivalence. -/
noncomputable def qW
    (Z0 Q : Subgroup X) [Z0.Normal] :
    NormalizerQuotient Q →*
      NormalizerQuotient (Q.map (QuotientGroup.mk' Z0)) := by
  exact QuotientGroup.map
    (localQ Q)
    (quotientDenominator Z0 Q)
    (quotientNormalizerMap Z0 Q)
    (localQ_le_quotientDenominator_comap_quotientNormalizerMap Z0 Q)

/-- Pointwise quotient formula for `qW`. -/
@[simp]
private theorem qW_mk
    (Z0 Q : Subgroup X) [Z0.Normal]
    (x : localNormalizer Q) :
    qW Z0 Q (QuotientGroup.mk x) =
      QuotientGroup.mk (quotientNormalizerMap Z0 Q x) :=
  rfl

/-- The hom-level quotient square defining `qW`. -/
theorem qW_quotient_square
    (Z0 Q : Subgroup X) [Z0.Normal] :
    (QuotientGroup.mk'
      ((Q.map (QuotientGroup.mk' Z0)).subgroupOf
        (Subgroup.normalizer
          ((Q.map (QuotientGroup.mk' Z0) : Subgroup (X ⧸ Z0)) :
            Set (X ⧸ Z0))))).comp
        (normalizerMap (QuotientGroup.mk' Z0) Q) =
      (qW Z0 Q).comp
        (QuotientGroup.mk'
          (Q.subgroupOf (Subgroup.normalizer (Q : Set X)))) := by
  ext x
  rfl

/-- The image in `L / Q` of the local intersection of `Z0 ⊔ Q` with `L`. -/
private abbrev qWKernel
    (Z0 Q : Subgroup X) [Z0.Normal] :
    Subgroup (NormalizerQuotient Q) :=
  (localCentralProduct Z0 Q).map
    (QuotientGroup.mk' (localQ Q))

/-- The exact raw kernel of `qW` is the image of that local intersection. -/
private theorem qW_ker
    (Z0 Q : Subgroup X) [Z0.Normal] :
    (qW Z0 Q).ker = qWKernel Z0 Q := by
  change
    (QuotientGroup.map
      (localQ Q)
      (quotientDenominator Z0 Q)
      (quotientNormalizerMap Z0 Q)
      (localQ_le_quotientDenominator_comap_quotientNormalizerMap Z0 Q)).ker =
        (localCentralProduct Z0 Q).map
          (QuotientGroup.mk' (localQ Q))
  rw [QuotientGroup.ker_map,
    quotientDenominator_comap_quotientNormalizerMap]

private theorem qW_surjective_of_normalizerMap_surjective
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hSurj : Function.Surjective (quotientNormalizerMap Z0 Q)) :
    Function.Surjective (qW Z0 Q) := by
  change Function.Surjective
    (QuotientGroup.map
      (localQ Q)
      (quotientDenominator Z0 Q)
      (quotientNormalizerMap Z0 Q)
      (localQ_le_quotientDenominator_comap_quotientNormalizerMap Z0 Q))
  exact QuotientGroup.map_surjective_of_surjective
    (localQ Q)
    (quotientDenominator Z0 Q)
    (quotientNormalizerMap Z0 Q)
    (QuotientGroup.mk_surjective.comp hSurj)
    (localQ_le_quotientDenominator_comap_quotientNormalizerMap Z0 Q)

/-- The auxiliary projection `L / Q -> L / (L ∩ Q Z0)`. -/
private noncomputable def rW
    (Z0 Q : Subgroup X) [Z0.Normal] :
    letI : (localCentralProduct Z0 Q).Normal :=
      localCentralProduct_normal Z0 Q
    NormalizerQuotient Q →*
      localNormalizer Q ⧸ localCentralProduct Z0 Q := by
  letI : (localCentralProduct Z0 Q).Normal :=
    localCentralProduct_normal Z0 Q
  exact QuotientGroup.map
    (localQ Q)
    (localCentralProduct Z0 Q)
    (MonoidHom.id (localNormalizer Q))
    (by
      simpa only [Subgroup.comap_id] using
        localQ_le_localCentralProduct Z0 Q)

private theorem rW_ker
    (Z0 Q : Subgroup X) [Z0.Normal] :
    letI : (localCentralProduct Z0 Q).Normal :=
      localCentralProduct_normal Z0 Q
    (rW Z0 Q).ker = qWKernel Z0 Q := by
  letI : (localCentralProduct Z0 Q).Normal :=
    localCentralProduct_normal Z0 Q
  change
    (QuotientGroup.map
      (localQ Q)
      (localCentralProduct Z0 Q)
      (MonoidHom.id (localNormalizer Q)) _).ker =
        (localCentralProduct Z0 Q).map
          (QuotientGroup.mk' (localQ Q))
  rw [QuotientGroup.ker_map, Subgroup.comap_id]

/-- The canonical corrected equivalence from the quotient by the local
intersection to `N_(X/Z0)(Q Z0/Z0) / (Q Z0/Z0)`. -/
private noncomputable def correctedNormalizerQuotientEquivOfSurjective
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hSurj : Function.Surjective (quotientNormalizerMap Z0 Q)) :
    letI : (localCentralProduct Z0 Q).Normal :=
      localCentralProduct_normal Z0 Q
    localNormalizer Q ⧸ localCentralProduct Z0 Q ≃*
      NormalizerQuotient (quotientRadical Z0 Q) := by
  letI : (localCentralProduct Z0 Q).Normal :=
    localCentralProduct_normal Z0 Q
  exact quotientEquivOfSurjectiveOfComapEq
    (quotientNormalizerMap Z0 Q) hSurj
    (localCentralProduct Z0 Q) (quotientDenominator Z0 Q)
    (quotientDenominator_comap_quotientNormalizerMap Z0 Q)

/-- The auxiliary factorisation of `qW` through the local-intersection
quotient. -/
private theorem qW_eq_correctedNormalizerQuotientEquiv_comp_rW
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hSurj : Function.Surjective (quotientNormalizerMap Z0 Q)) :
    letI : (localCentralProduct Z0 Q).Normal :=
      localCentralProduct_normal Z0 Q
    qW Z0 Q =
      (correctedNormalizerQuotientEquivOfSurjective
        Z0 Q hSurj).toMonoidHom.comp (rW Z0 Q) := by
  letI : (localCentralProduct Z0 Q).Normal :=
    localCentralProduct_normal Z0 Q
  apply MonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

private theorem qWKernel_eq_localCentralKernel_map
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X) :
    qWKernel Z0 Q =
      (localCentralKernel Z0 Q).map
        (QuotientGroup.mk' (localQ Q)) := by
  change
    (localCentralProduct Z0 Q).map
        (QuotientGroup.mk' (localQ Q)) =
      (localCentralKernel Z0 Q).map
        (QuotientGroup.mk' (localQ Q))
  rw [localCentralProduct_eq_sup Z0 Q hZ0central,
    Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]

/-- The exact `qW` kernel, written as the image of the central subgroup in
the local normaliser. -/
theorem qW_ker_eq_localCentralKernel_map
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X) :
    (qW Z0 Q).ker =
      (Z0.subgroupOf (Subgroup.normalizer (Q : Set X))).map
        (QuotientGroup.mk'
          (Q.subgroupOf (Subgroup.normalizer (Q : Set X)))) := by
  rw [qW_ker, qWKernel_eq_localCentralKernel_map
    Z0 Q hZ0central]

/-- The order of the exact `qW` kernel divides the order of `Z0`. -/
private theorem qW_ker_card_dvd_Z0
    {X : Type u} [Group X] [Finite X]
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X) :
    Nat.card (qW Z0 Q).ker ∣ Nat.card Z0 := by
  rw [qW_ker_eq_localCentralKernel_map Z0 Q hZ0central]
  have hdiv := Subgroup.card_map_dvd
    (localCentralKernel Z0 Q)
    (QuotientGroup.mk' (localQ Q))
  rw [Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe
      (central_le_localNormalizer Z0 Q hZ0central)).toEquiv] at hdiv
  exact hdiv

/-- A central prime-to-`ell` kernel gives a prime-to-`ell` kernel for `qW`. -/
theorem qW_ker_card_not_dvd
    {ell : Nat} {X : Type u} [Group X] [Finite X]
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0) :
    ¬ ell ∣ Nat.card (qW Z0 Q).ker := by
  intro hdiv
  exact hZ0PrimeTo
    (dvd_trans hdiv (qW_ker_card_dvd_Z0 Z0 Q hZ0central))

private theorem qW_ordProj_card_eq_of_surjective
    {ell : Nat} {X : Type u} [Group X] [Finite X]
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0)
    (hSurj : Function.Surjective (qW Z0 Q)) :
    ordProj[ell] (Nat.card (NormalizerQuotient Q)) =
      ordProj[ell]
        (Nat.card
          (NormalizerQuotient
            (Q.map (QuotientGroup.mk' Z0)))) :=
  ordProj_card_eq_of_surjective_of_ker_card_not_dvd
    (qW Z0 Q) hSurj
    (qW_ker_card_not_dvd Z0 Q hZ0central hZ0PrimeTo)

end Core

section NavarroTiep

/-- The live Navarro--Tiep normaliser-image source makes the canonical local
quotient map surjective. -/
theorem qW_surjective_ofNavarroTiep
    {ell : Nat} {X : Type u}
    [Group X] [Finite X] [Fact ell.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup ell Q)
    (S : NavarroTiep23cFixedCentralQuotientSource
      Z0 hZ0central hZ0PrimeTo Q hQ) :
    Function.Surjective (qW Z0 Q) :=
  qW_surjective_of_normalizerMap_surjective Z0 Q
    (_root_.ModularRep.centralQuotientNormalizerMap_surjective
      Z0 hZ0central hZ0PrimeTo Q hQ S)

/-- The two local group orders have the same `ell`-part under the live
Navarro--Tiep source. -/
theorem qW_ordProj_card_eq_ofNavarroTiep
    {ell : Nat} {X : Type u}
    [Group X] [Finite X] [Fact ell.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0central : Z0 ≤ Subgroup.center X)
    (hZ0PrimeTo : ¬ ell ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup ell Q)
    (S : NavarroTiep23cFixedCentralQuotientSource
      Z0 hZ0central hZ0PrimeTo Q hQ) :
    ordProj[ell] (Nat.card (NormalizerQuotient Q)) =
      ordProj[ell]
        (Nat.card
          (NormalizerQuotient
            (Q.map (QuotientGroup.mk' Z0)))) :=
  qW_ordProj_card_eq_of_surjective
    Z0 Q hZ0central hZ0PrimeTo
    (qW_surjective_ofNavarroTiep
      Z0 hZ0central hZ0PrimeTo Q hQ S)

end NavarroTiep

end ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
