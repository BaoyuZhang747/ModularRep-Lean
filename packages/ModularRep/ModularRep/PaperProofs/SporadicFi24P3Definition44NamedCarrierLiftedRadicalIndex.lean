import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses

/-! # The computed radical lift transports an exhaustive conjugacy index -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiftedRadicalIndex

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses

universe u v
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

def fixedRadicalClassEquiv : RadicalConjugacyClass (p := p) (G := X) ≃
    RadicalConjugacyClass (p := p) (G := X ⧸ Z) := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  exact radicalConjugacyEquiv (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    (by simpa only [QuotientGroup.ker_mk'] using hcentral)
    (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)

@[simp]
theorem fixedRadicalClassEquiv_mk (Q : RadicalSubgroup (p := p) (G := X)) :
    fixedRadicalClassEquiv iota Z hcentral hprimeTo (Quotient.mk'' Q) =
      Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo Q) := rfl

@[simp]
theorem fixedRadicalClassEquiv_symm_mk (R : RadicalSubgroup (p := p) (G := X ⧸ Z)) :
    (fixedRadicalClassEquiv iota Z hcentral hprimeTo).symm (Quotient.mk'' R) =
      Quotient.mk'' ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm R) := rfl

@[simp]
theorem fixedRadicalEquiv_symm_apply_val (R : RadicalSubgroup (p := p) (G := X ⧸ Z)) :
    ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm R).1 =
      SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups.pSubgroupLift
        p (QuotientGroup.mk' Z) R.1 := rfl

def liftedRadicalIndexEquiv {I : Type v}
    (Qd : I → RadicalSubgroup (p := p) (G := X ⧸ Z))
    (hbij : Function.Bijective
      (fun i => (Quotient.mk'' (Qd i) : RadicalConjugacyClass (p := p) (G := X ⧸ Z)))) :
    I ≃ RadicalConjugacyClass (p := p) (G := X) :=
  (Equiv.ofBijective
    (fun i => (Quotient.mk'' (Qd i) : RadicalConjugacyClass (p := p) (G := X ⧸ Z))) hbij).trans
      (fixedRadicalClassEquiv iota Z hcentral hprimeTo).symm

@[simp]
theorem liftedRadicalIndexEquiv_apply {I : Type v}
    (Qd : I → RadicalSubgroup (p := p) (G := X ⧸ Z))
    (hbij : Function.Bijective
      (fun i => (Quotient.mk'' (Qd i) : RadicalConjugacyClass (p := p) (G := X ⧸ Z)))) (i : I) :
    liftedRadicalIndexEquiv iota Z hcentral hprimeTo Qd hbij i =
      Quotient.mk'' ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm (Qd i)) := rfl

theorem liftedRadicalRepresentative_bijective {I : Type v}
    (Qd : I → RadicalSubgroup (p := p) (G := X ⧸ Z))
    (hbij : Function.Bijective
      (fun i => (Quotient.mk'' (Qd i) : RadicalConjugacyClass (p := p) (G := X ⧸ Z)))) :
    Function.Bijective (fun i => (Quotient.mk''
      ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm (Qd i)) :
        RadicalConjugacyClass (p := p) (G := X))) :=
  (liftedRadicalIndexEquiv iota Z hcentral hprimeTo Qd hbij).bijective

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiftedRadicalIndex


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
