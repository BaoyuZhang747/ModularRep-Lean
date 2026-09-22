import ModularRep.WeightTransport
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses

/-! The actual local quotient square when an automorphism moves Q.
Only a commuting quotient square is needed; Q need not be stable. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalTwist

open ModularRep
open CentralEllPrimeWeightLocalQuotient
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses

universe u

theorem quotient_cast_mk {X : Type u} [Group X]
    {Q R : Subgroup X} (h : Q = R)
    (n : Subgroup.normalizer (Q : Set X)) :
    MulEquiv.cast (M := fun S : Subgroup X => NormalizerQuotient S) h
        (QuotientGroup.mk n) =
      QuotientGroup.mk
        (MulEquiv.cast (M := fun S : Subgroup X =>
          Subgroup.normalizer (S : Set X)) h n) := by
  subst R
  rfl

theorem normalizer_cast_coe {X : Type u} [Group X]
    {Q R : Subgroup X} (h : Q = R)
    (n : Subgroup.normalizer (Q : Set X)) :
    ((MulEquiv.cast (M := fun S : Subgroup X =>
      Subgroup.normalizer (S : Set X)) h n :
        Subgroup.normalizer (R : Set X)) : X) = n := by
  subst R
  rfl

theorem qW_mk {X : Type u} [Group X]
    (Z Q : Subgroup X) [Z.Normal]
    (n : Subgroup.normalizer (Q : Set X)) :
    qW Z Q (QuotientGroup.mk n) =
      QuotientGroup.mk (normalizerMap (QuotientGroup.mk' Z) Q n) := rfl

theorem qW_rightNormalizerQuotientEquiv {X : Type u} [Group X]
    (Z Q : Subgroup X) [Z.Normal]
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) =
      beta (QuotientGroup.mk' Z x))
    (x : NormalizerQuotient (Q.comap alpha.toMonoidHom)) :
    qW Z Q (rightNormalizerQuotientEquiv alpha Q x) =
      rightNormalizerQuotientEquiv beta (Q.map (QuotientGroup.mk' Z))
        (MulEquiv.cast (M := fun S : Subgroup (X ⧸ Z) => NormalizerQuotient S)
          (subgroup_map_comap_of_square (QuotientGroup.mk' Z) alpha beta square Q)
          (qW Z (Q.comap alpha.toMonoidHom) x)) := by
  refine Quotient.inductionOn x ?_
  intro n
  rw [rightNormalizerQuotientEquiv_mk, qW_mk, qW_mk,
    quotient_cast_mk, rightNormalizerQuotientEquiv_mk]
  apply congrArg (fun y => QuotientGroup.mk y)
  apply Subtype.ext
  simpa only [normalizerMap_coe, rightNormalizerEquiv_coe,
    normalizer_cast_coe] using square n.val

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalTwist


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
