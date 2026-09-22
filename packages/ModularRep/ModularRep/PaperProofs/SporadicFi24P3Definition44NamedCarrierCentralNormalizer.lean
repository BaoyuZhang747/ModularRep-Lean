import ModularRep.PaperProofs.NavarroTiep23cFixedCentralQuotientSource
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual normalizer quotient for a central quotient.
The kernel is the restricted central subgroup. Only surjectivity uses
the Navarro--Tiep source; no containment of that kernel in Q is assumed. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralNormalizer

open ModularRep

universe u
variable {X : Type u} [Group X]

theorem centralNormalizerMap_ker (Z0 Q : Subgroup X) [Z0.Normal] :
    (normalizerMap (QuotientGroup.mk' Z0) Q).ker =
      Z0.subgroupOf (Subgroup.normalizer (Q : Set X)) := by
  ext x
  change normalizerMap (QuotientGroup.mk' Z0) Q x = 1 ↔ (x : X) ∈ Z0
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' Z0 (x : X) = 1 ↔ (x : X) ∈ Z0
  exact QuotientGroup.eq_one_iff (x : X)

def centralNormalizerEquivOfSurjective
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hsurj : Function.Surjective (normalizerMap (QuotientGroup.mk' Z0) Q)) :
    (Subgroup.normalizer (Q : Set X) ⧸
      Z0.subgroupOf (Subgroup.normalizer (Q : Set X))) ≃*
        Subgroup.normalizer (Q.map (QuotientGroup.mk' Z0) : Set (X ⧸ Z0)) :=
  (QuotientGroup.quotientMulEquivOfEq
    (centralNormalizerMap_ker Z0 Q).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (normalizerMap (QuotientGroup.mk' Z0) Q) hsurj)

theorem centralNormalizerEquivOfSurjective_mk
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hsurj : Function.Surjective (normalizerMap (QuotientGroup.mk' Z0) Q))
    (x : Subgroup.normalizer (Q : Set X)) :
    centralNormalizerEquivOfSurjective Z0 Q hsurj
      (QuotientGroup.mk' (Z0.subgroupOf (Subgroup.normalizer (Q : Set X))) x) =
        normalizerMap (QuotientGroup.mk' Z0) Q x := rfl

theorem centralNormalizerEquivOfSurjective_mk_coe
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hsurj : Function.Surjective (normalizerMap (QuotientGroup.mk' Z0) Q))
    (x : Subgroup.normalizer (Q : Set X)) :
    (centralNormalizerEquivOfSurjective Z0 Q hsurj
      (QuotientGroup.mk' (Z0.subgroupOf (Subgroup.normalizer (Q : Set X))) x) : X ⧸ Z0) =
        QuotientGroup.mk' Z0 (x : X) := rfl

theorem centralNormalizerEquivOfSurjective_square
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hsurj : Function.Surjective (normalizerMap (QuotientGroup.mk' Z0) Q)) :
    (centralNormalizerEquivOfSurjective Z0 Q hsurj).toMonoidHom.comp
      (QuotientGroup.mk' (Z0.subgroupOf (Subgroup.normalizer (Q : Set X)))) =
        normalizerMap (QuotientGroup.mk' Z0) Q := by
  ext x
  rfl

theorem centralNormalizerEquivOfSurjective_symm_map
    (Z0 Q : Subgroup X) [Z0.Normal]
    (hsurj : Function.Surjective (normalizerMap (QuotientGroup.mk' Z0) Q))
    (x : Subgroup.normalizer (Q : Set X)) :
    (centralNormalizerEquivOfSurjective Z0 Q hsurj).symm
      (normalizerMap (QuotientGroup.mk' Z0) Q x) =
        QuotientGroup.mk' (Z0.subgroupOf (Subgroup.normalizer (Q : Set X))) x := by
  apply (centralNormalizerEquivOfSurjective Z0 Q hsurj).injective
  rw [MulEquiv.apply_symm_apply, centralNormalizerEquivOfSurjective_mk]

def centralNormalizerEquivOfNavarroTiep
    {p : ℕ} [Finite X] [Fact p.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hcentral : Z0 ≤ Subgroup.center X)
    (hprimeTo : ¬ p ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup p Q)
    (source : NavarroTiep23cFixedCentralQuotientSource Z0 hcentral hprimeTo Q hQ) :
    (Subgroup.normalizer (Q : Set X) ⧸
      Z0.subgroupOf (Subgroup.normalizer (Q : Set X))) ≃*
        Subgroup.normalizer (Q.map (QuotientGroup.mk' Z0) : Set (X ⧸ Z0)) :=
  centralNormalizerEquivOfSurjective Z0 Q
    (centralQuotientNormalizerMap_surjective Z0 hcentral hprimeTo Q hQ source)

theorem centralNormalizerEquivOfNavarroTiep_square
    {p : ℕ} [Finite X] [Fact p.Prime]
    (Z0 : Subgroup X) [Z0.Normal]
    (hcentral : Z0 ≤ Subgroup.center X)
    (hprimeTo : ¬ p ∣ Nat.card Z0)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup p Q)
    (source : NavarroTiep23cFixedCentralQuotientSource Z0 hcentral hprimeTo Q hQ) :
    (centralNormalizerEquivOfNavarroTiep Z0 hcentral hprimeTo Q hQ source).toMonoidHom.comp
      (QuotientGroup.mk' (Z0.subgroupOf (Subgroup.normalizer (Q : Set X)))) =
        normalizerMap (QuotientGroup.mk' Z0) Q :=
  centralNormalizerEquivOfSurjective_square Z0 Q _

def localCentralKernelEquiv
    (Z0 Q : Subgroup X) (hcentral : Z0 ≤ Subgroup.center X) :
    Z0.subgroupOf (Subgroup.normalizer (Q : Set X)) ≃* Z0 :=
  Subgroup.subgroupOfEquivOfLe
    (hcentral.trans (Subgroup.center_le_normalizer (Q : Set X)))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralNormalizer



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
