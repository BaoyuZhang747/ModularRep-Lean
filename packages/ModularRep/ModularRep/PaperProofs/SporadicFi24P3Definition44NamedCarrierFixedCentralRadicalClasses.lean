import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre

/-! # The representative radical image and its conjugacy class transport -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

def fixedRadicalEquiv : RadicalSubgroup (p := p) (G := X) ≃
    RadicalSubgroup (p := p) (G := X ⧸ Z) := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  exact radicalSubgroupEquiv (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    (by simpa only [QuotientGroup.ker_mk'] using hcentral)
    (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)

@[simp]
theorem fixedRadicalEquiv_apply (Q : RadicalSubgroup (p := p) (G := X)) :
    fixedRadicalEquiv iota Z hcentral hprimeTo Q =
      fixedRadicalImage iota Z hcentral hprimeTo Q := by
  apply Subtype.ext
  rfl

@[simp]
theorem fixedRadicalImage_lift (R : RadicalSubgroup (p := p) (G := X ⧸ Z)) :
    fixedRadicalImage iota Z hcentral hprimeTo
        ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm R) = R :=
  (fixedRadicalEquiv_apply iota Z hcentral hprimeTo _).symm.trans
    ((fixedRadicalEquiv iota Z hcentral hprimeTo).apply_symm_apply R)

theorem fixedRadicalImage_class_eq_iff (Q R : RadicalSubgroup (p := p) (G := X)) :
    (Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo Q) :
      RadicalConjugacyClass (p := p) (G := X ⧸ Z)) =
        Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo R) ↔
    (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' R := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  let E := radicalConjugacyEquiv (p := p)
    (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    (by simpa only [QuotientGroup.ker_mk'] using hcentral)
    (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)
  change E (Quotient.mk'' Q) = E (Quotient.mk'' R) ↔ Quotient.mk'' Q = Quotient.mk'' R
  exact E.injective.eq_iff

theorem fixedRadicalImage_class_fixed_iff (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (Q : RadicalSubgroup (p := p) (G := X)) :
    MulOpposite.op alpha •
        (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' Q ↔
    MulOpposite.op beta •
        (Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo Q) :
          RadicalConjugacyClass (p := p) (G := X ⧸ Z)) =
      Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo Q) := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  exact radicalConjugacyEquiv_fixed_iff
    (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    (by simpa only [QuotientGroup.ker_mk'] using hcentral)
    (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)
    alpha beta square (Quotient.mk'' Q)

theorem fixedRadicalLift_class_fixed (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (R : RadicalSubgroup (p := p) (G := X ⧸ Z))
    (hfixed : MulOpposite.op beta •
        (Quotient.mk'' R : RadicalConjugacyClass (p := p) (G := X ⧸ Z)) = Quotient.mk'' R) :
    MulOpposite.op alpha •
        (Quotient.mk'' ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm R) :
          RadicalConjugacyClass (p := p) (G := X)) =
      Quotient.mk'' ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm R) := by
  apply (fixedRadicalImage_class_fixed_iff iota Z hcentral hprimeTo alpha beta square _).mpr
  simpa only [fixedRadicalImage_lift] using hfixed

theorem fixedRadicalLift_classes_ne (R S : RadicalSubgroup (p := p) (G := X ⧸ Z))
    (hne : (Quotient.mk'' R : RadicalConjugacyClass (p := p) (G := X ⧸ Z)) ≠ Quotient.mk'' S) :
    (Quotient.mk'' ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm R) :
      RadicalConjugacyClass (p := p) (G := X)) ≠
        Quotient.mk'' ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm S) := by
  intro h
  apply hne
  have himage := (fixedRadicalImage_class_eq_iff iota Z hcentral hprimeTo
    ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm R)
    ((fixedRadicalEquiv iota Z hcentral hprimeTo).symm S)).mpr h
  simpa only [fixedRadicalImage_lift] using himage

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
