import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient
import ModularRep.PaperProofs.TypeBCentralKernelNormalizerInertia

/-!
# Literal local automorphism squares and ordinary fixedness

Image stability is derived from the ambient square. The qW square uses
only normality of Z; surjectivity and factorization reflect fixedness.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction

open ModularRep
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
open CentralEllPrimeWeightLocalQuotient
open TypeBCentralKernelWeightTransport TypeBCentralKernelNormalizerInertia

universe u

theorem image_stable {X Y : Type u} [Group X] [Group Y]
    (f : X →* Y) (sigma : MulAut X) (beta : MulAut Y)
    (square : ∀ x, f (sigma x) = beta (f x)) (Q : Subgroup X)
    (stableU : Q.comap sigma.toMonoidHom = Q) :
    (Q.map f).comap beta.toMonoidHom = Q.map f :=
  (subgroup_map_comap_of_square f sigma beta square Q).symm.trans
    (congrArg (fun R : Subgroup X => R.map f) stableU)

theorem normalizerAut_map_square {X Y : Type u} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (sigma : MulAut X) (beta : MulAut Y)
    (square : ∀ x, f (sigma x) = beta (f x)) (Q : Subgroup X)
    (stableU : Q.comap sigma.toMonoidHom = Q)
    (stableD : (Q.map f).comap beta.toMonoidHom = Q.map f)
    (n : Subgroup.normalizer (Q : Set X)) :
    normalizerMap f Q (normalizerAut Q sigma stableU n) =
      normalizerAut (Q.map f) beta stableD (normalizerMap f Q n) := by
  apply Subtype.ext
  simp only [normalizerMap_coe, normalizerAut_coe]
  exact square n.1

theorem qW_localAut_square {X : Type u} [Group X] [Finite X]
    (Z Q : Subgroup X) [Z.Normal] (sigma : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (sigma x) = beta (QuotientGroup.mk' Z x))
    (stableU : Q.comap sigma.toMonoidHom = Q) (x : NormalizerQuotient Q) :
    qW Z Q (localAut Q sigma stableU x) =
      localAut (Q.map (QuotientGroup.mk' Z)) beta
        (image_stable (QuotientGroup.mk' Z) sigma beta square Q stableU) (qW Z Q x) := by
  let Qbar := Q.map (QuotientGroup.mk' Z)
  let stableD : Qbar.comap beta.toMonoidHom = Qbar :=
    image_stable (QuotientGroup.mk' Z) sigma beta square Q stableU
  have hm (n : Subgroup.normalizer (Q : Set X)) :
      qW Z Q (localMk Q n) = localMk Qbar (normalizerMap (QuotientGroup.mk' Z) Q n) :=
    (DFunLike.congr_fun (qW_quotient_square Z Q) n).symm
  refine Quotient.inductionOn x ?_
  intro n
  change qW Z Q (localAut Q sigma stableU (localMk Q n)) =
    localAut Qbar beta stableD (qW Z Q (localMk Q n))
  rw [localAut_mk, hm, hm, localAut_mk]
  exact congrArg (localMk Qbar)
    (normalizerAut_map_square (QuotientGroup.mk' Z) sigma beta square Q stableU stableD n)

theorem ordinary_fixed_iff_of_factorisation {K A B : Type u}
    [Field K] [CharZero K] [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (alpha : MulAut A) (beta : MulAut B) (square : ∀ x, f (alpha x) = beta (f x))
    (theta : OrdinaryIrreducibleCharacter.Irr K A) (eta : OrdinaryIrreducibleCharacter.Irr K B)
    (factor : ∀ x, theta x = eta (f x)) :
    OrdinaryIrreducibleCharacter.twist K A theta alpha = theta ↔
      OrdinaryIrreducibleCharacter.twist K B eta beta = eta := by
  constructor
  · intro h
    apply OrdinaryIrreducibleCharacter.ext
    intro y
    obtain ⟨x, rfl⟩ := hf y
    calc
      eta (beta (f x)) = eta (f (alpha x)) := congrArg eta (square x).symm
      _ = theta (alpha x) := (factor (alpha x)).symm
      _ = theta x := congrArg (fun chi : OrdinaryIrreducibleCharacter.Irr K A => chi x) h
      _ = eta (f x) := factor x
  · intro h
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    change theta (alpha x) = theta x
    rw [factor (alpha x), factor x, square x]
    exact congrArg (fun chi : OrdinaryIrreducibleCharacter.Irr K B => chi (f x)) h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
