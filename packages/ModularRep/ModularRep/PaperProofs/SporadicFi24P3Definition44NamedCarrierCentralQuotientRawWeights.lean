import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalTwist
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToLocalOrdinaryEquiv

/-! Intrinsic ordinary-character descent of raw weights trivial on the
local quotient kernel. Moving-radical covariance is derived from the actual
quotient square and ordinary character uniqueness. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights

open ModularRep ModularRep.CharacterWeight
open CentralEllPrimeWeightLocalQuotient
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryEquiv
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToLocalOrdinaryEquiv
open SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalTwist

universe u

theorem castLocalCharacter_symm_apply
    {K G : Type u} [Field K] [CharZero K] [Group G]
    {Q R : Subgroup G} (h : Q = R)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient R))
    (x : NormalizerQuotient Q) :
    castLocalCharacter h.symm chi x =
      chi (MulEquiv.cast (M := fun S : Subgroup G => NormalizerQuotient S) h x) := by
  subst R
  rfl

theorem factorisation_rightTwist
    {K X : Type u} [Field K] [CharZero K] [Group X]
    (Z Q : Subgroup X) [Z.Normal]
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (theta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (eta : OrdinaryIrreducibleCharacter.Irr K
      (NormalizerQuotient (Q.map (QuotientGroup.mk' Z))))
    (factor : ∀ x, theta x = eta (qW Z Q x))
    (x : NormalizerQuotient (Q.comap alpha.toMonoidHom)) :
    OrdinaryIrreducibleCharacter.mapEquiv theta
        (rightNormalizerQuotientEquiv alpha Q).symm x =
      castLocalCharacter
        (subgroup_map_comap_of_square (QuotientGroup.mk' Z) alpha beta square Q).symm
        (OrdinaryIrreducibleCharacter.mapEquiv eta
          (rightNormalizerQuotientEquiv beta (Q.map (QuotientGroup.mk' Z))).symm)
        (qW Z (Q.comap alpha.toMonoidHom) x) := by
  rw [castLocalCharacter_symm_apply
    (subgroup_map_comap_of_square (QuotientGroup.mk' Z) alpha beta square Q)]
  change theta (rightNormalizerQuotientEquiv alpha Q x) = _
  exact (factor (rightNormalizerQuotientEquiv alpha Q x)).trans
    (congrArg eta (qW_rightNormalizerQuotientEquiv Z Q alpha beta square x))

variable {p : ℕ} {K X : Type u}
variable [Field K] [CharZero K] [Group X] [Finite X]
variable (Z : Subgroup X) [Z.Normal]

def KernelConstant (W : CharacterWeight p K X) : Prop :=
  ∀ x : (qW Z W.subgroup).ker,
    W.localCharacter (x : NormalizerQuotient W.subgroup) = W.localCharacter 1

variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

def rawDescent (W : CharacterWeight p K X) (hkernel : KernelConstant Z W) :
    CharacterWeight p K (X ⧸ Z) := by
  letI : Fact p.Prime := ⟨W.prime⟩
  let eta := qWDefectZeroEquiv (p := p) (K := K) Z hcentral hprimeTo
    W.subgroup W.radical ⟨⟨W.localCharacter, W.defectZero⟩, hkernel⟩
  exact ⟨W.prime, W.subgroup.map (QuotientGroup.mk' Z),
    (fixedCentralQuotientSource Z hcentral hprimeTo W.subgroup W.radical).radical_image,
    eta.1, eta.2⟩

theorem rawDescent_subgroup (W : CharacterWeight p K X) (hkernel : KernelConstant Z W) :
    (rawDescent Z hcentral hprimeTo W hkernel).subgroup =
      W.subgroup.map (QuotientGroup.mk' Z) := rfl

theorem rawDescent_character (W : CharacterWeight p K X) (hkernel : KernelConstant Z W)
    (x : NormalizerQuotient W.subgroup) :
    (rawDescent Z hcentral hprimeTo W hkernel).localCharacter (qW Z W.subgroup x) =
      W.localCharacter x := by
  let _ : Fact p.Prime := ⟨W.prime⟩
  exact defectZeroInflationDescentEquiv_apply (qW Z W.subgroup)
    (qW_surjective_ofNavarroTiep Z hcentral hprimeTo W.subgroup W.radical
      (fixedCentralQuotientSource Z hcentral hprimeTo W.subgroup W.radical))
    (qW_ker_card_not_dvd Z W.subgroup hcentral hprimeTo)
    ⟨⟨W.localCharacter, W.defectZero⟩, hkernel⟩ x

theorem rawDescent_unique (W : CharacterWeight p K X) (hkernel : KernelConstant Z W)
    (U : CharacterWeight p K (X ⧸ Z))
    (hQ : U.subgroup = W.subgroup.map (QuotientGroup.mk' Z))
    (hfactor : ∀ x : NormalizerQuotient W.subgroup,
      W.localCharacter x = castLocalCharacter hQ U.localCharacter (qW Z W.subgroup x)) :
    U = rawDescent Z hcentral hprimeTo W hkernel := by
  let _ : Fact p.Prime := ⟨W.prime⟩
  apply CharacterWeight.eq_of_isomorphic
  refine ⟨hQ, ?_⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro y
  obtain ⟨x, rfl⟩ := qW_surjective_ofNavarroTiep Z hcentral hprimeTo
    W.subgroup W.radical (fixedCentralQuotientSource Z hcentral hprimeTo W.subgroup W.radical) y
  exact (hfactor x).symm.trans (rawDescent_character Z hcentral hprimeTo W hkernel x).symm

include hcentral hprimeTo in
theorem kernelConstant_rightTwist (W : CharacterWeight p K X) (hkernel : KernelConstant Z W)
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) :
    KernelConstant Z (W.rightTwist alpha) := by
  let hQ := subgroup_map_comap_of_square (QuotientGroup.mk' Z) alpha beta square W.subgroup
  let etaTw := castLocalCharacter hQ.symm
    ((rawDescent Z hcentral hprimeTo W hkernel).rightTwist beta).localCharacter
  have factor (x : NormalizerQuotient (W.rightTwist alpha).subgroup) :
      (W.rightTwist alpha).localCharacter x =
        etaTw (qW Z (W.rightTwist alpha).subgroup x) :=
    factorisation_rightTwist Z W.subgroup alpha beta square
    W.localCharacter (rawDescent Z hcentral hprimeTo W hkernel).localCharacter
    (fun x => (rawDescent_character Z hcentral hprimeTo W hkernel x).symm)
    x
  intro x
  change (W.rightTwist alpha).localCharacter x.val = (W.rightTwist alpha).localCharacter 1
  rw [factor x.val, factor 1, MonoidHom.mem_ker.mp x.property, map_one]

theorem rawDescent_rightTwist (W : CharacterWeight p K X) (hkernel : KernelConstant Z W)
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) :
    rawDescent Z hcentral hprimeTo (W.rightTwist alpha)
        (kernelConstant_rightTwist Z hcentral hprimeTo W hkernel alpha beta square) =
      (rawDescent Z hcentral hprimeTo W hkernel).rightTwist beta := by
  symm
  apply rawDescent_unique Z hcentral hprimeTo (W.rightTwist alpha)
    (kernelConstant_rightTwist Z hcentral hprimeTo W hkernel alpha beta square)
    ((rawDescent Z hcentral hprimeTo W hkernel).rightTwist beta)
    (subgroup_map_comap_of_square (QuotientGroup.mk' Z) alpha beta square W.subgroup).symm
  exact factorisation_rightTwist Z W.subgroup alpha beta square
    W.localCharacter (rawDescent Z hcentral hprimeTo W hkernel).localCharacter
    (fun x => (rawDescent_character Z hcentral hprimeTo W hkernel x).symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
