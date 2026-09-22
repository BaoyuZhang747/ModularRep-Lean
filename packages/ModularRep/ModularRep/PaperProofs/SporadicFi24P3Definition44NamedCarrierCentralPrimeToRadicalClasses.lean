import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
import ModularRep.CharacterWeightRadicalProjection

/-!
# Radical conjugacy classes across a central prime-to-p surjection

The inverse uses the p-core of the full preimage. Naturality uses the
literal commuting automorphism square, and passes to conjugacy classes.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals

universe u

theorem subgroup_map_comap_of_square
    {G H : Type u} [Group G] [Group H]
    (f : G →* H) (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g)) (Q : Subgroup G) :
    (Q.comap alpha.toMonoidHom).map f = (Q.map f).comap beta.toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change beta (f x) ∈ Q.map f
    exact ⟨alpha x, hx, square x⟩
  · intro hy
    change beta y ∈ Q.map f at hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨alpha.symm x, ?_, ?_⟩
    · change alpha (alpha.symm x) ∈ Q
      rw [MulEquiv.apply_symm_apply]
      exact hx
    · apply beta.injective
      calc
        beta (f (alpha.symm x)) = f (alpha (alpha.symm x)) :=
          (square (alpha.symm x)).symm
        _ = f x := congrArg f (alpha.apply_symm_apply x)
        _ = beta y := hxy

variable {p : ℕ} [hp : Fact p.Prime]
variable {G H : Type u} [Group G] [Group H] [Finite G]
variable (f : G →* H) (hf : Function.Surjective f)
variable (hcentral : f.ker ≤ Subgroup.center G) (hker : ¬ p ∣ Nat.card f.ker)

def radicalSubgroupEquiv :
    RadicalSubgroup (p := p) (G := G) ≃ RadicalSubgroup (p := p) (G := H) where
  toFun Q := ⟨Q.1.map f,
    (radical_iff_map_of_central_primeTo f hf hcentral hker Q.1 Q.2.isPGroup).mp Q.2⟩
  invFun R := ⟨pSubgroupLift p f R.1, by
    apply (radical_iff_map_of_central_primeTo f hf hcentral hker _
      (pSubgroupLift_isPGroup p f R.1)).mpr
    rw [pSubgroupLift_map f hf hcentral R.1 R.2.isPGroup]
    exact R.2⟩
  left_inv Q := by
    apply Subtype.ext
    apply map_pSubgroup_injective hp.out f hcentral hker _ _
      (pSubgroupLift_isPGroup p f (Q.1.map f)) Q.2.isPGroup
    exact pSubgroupLift_map f hf hcentral (Q.1.map f) (Q.2.isPGroup.map f)
  right_inv R := Subtype.ext (pSubgroupLift_map f hf hcentral R.1 R.2.isPGroup)

@[simp]
theorem radicalSubgroupEquiv_apply_val (Q : RadicalSubgroup (p := p) (G := G)) :
    (radicalSubgroupEquiv f hf hcentral hker Q).1 = Q.1.map f := rfl

@[simp]
theorem radicalSubgroupEquiv_symm_apply_val (R : RadicalSubgroup (p := p) (G := H)) :
    ((radicalSubgroupEquiv f hf hcentral hker).symm R).1 = pSubgroupLift p f R.1 := rfl

theorem radicalSubgroupEquiv_rightTwist
    (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g)) (Q : RadicalSubgroup (p := p) (G := G)) :
    radicalSubgroupEquiv f hf hcentral hker (Q.rightTwist alpha) =
      (radicalSubgroupEquiv f hf hcentral hker Q).rightTwist beta := by
  apply Subtype.ext
  exact subgroup_map_comap_of_square f alpha beta square Q.1

theorem radicalSubgroupEquiv_conjugation (g : G) (Q : RadicalSubgroup (p := p) (G := G)) :
    radicalSubgroupEquiv f hf hcentral hker (g • Q) =
      f g • radicalSubgroupEquiv f hf hcentral hker Q := by
  change radicalSubgroupEquiv f hf hcentral hker (Q.rightTwist (MulAut.conj g⁻¹)) =
    (radicalSubgroupEquiv f hf hcentral hker Q).rightTwist (MulAut.conj (f g)⁻¹)
  apply radicalSubgroupEquiv_rightTwist f hf hcentral hker
  intro x
  rw [MulAut.conj_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv]

theorem radical_orbitRel_iff (Q R : RadicalSubgroup (p := p) (G := G)) :
    MulAction.orbitRel G _ Q R ↔
      MulAction.orbitRel H _ (radicalSubgroupEquiv f hf hcentral hker Q)
        (radicalSubgroupEquiv f hf hcentral hker R) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨f g, (radicalSubgroupEquiv_conjugation f hf hcentral hker g R).symm⟩
  · rintro ⟨h, hh⟩
    obtain ⟨g, rfl⟩ := hf h
    refine ⟨g, (radicalSubgroupEquiv f hf hcentral hker).injective ?_⟩
    rw [radicalSubgroupEquiv_conjugation]
    exact hh

def radicalConjugacyEquiv :
    RadicalConjugacyClass (p := p) (G := G) ≃
      RadicalConjugacyClass (p := p) (G := H) :=
  Quotient.congr (radicalSubgroupEquiv f hf hcentral hker)
    (radical_orbitRel_iff f hf hcentral hker)

@[simp]
theorem radicalConjugacyEquiv_mk (Q : RadicalSubgroup (p := p) (G := G)) :
    radicalConjugacyEquiv f hf hcentral hker (Quotient.mk'' Q) =
      Quotient.mk'' (radicalSubgroupEquiv f hf hcentral hker Q) := rfl

@[simp]
theorem radicalConjugacyEquiv_symm_mk (R : RadicalSubgroup (p := p) (G := H)) :
    (radicalConjugacyEquiv f hf hcentral hker).symm (Quotient.mk'' R) =
      Quotient.mk'' ((radicalSubgroupEquiv f hf hcentral hker).symm R) := rfl

@[simp]
theorem radicalConjugacyEquiv_mk_lift (R : RadicalSubgroup (p := p) (G := H)) :
    radicalConjugacyEquiv f hf hcentral hker
        (Quotient.mk'' ((radicalSubgroupEquiv f hf hcentral hker).symm R)) =
      Quotient.mk'' R := by
  rw [radicalConjugacyEquiv_mk, Equiv.apply_symm_apply]

theorem radicalConjugacyEquiv_rightTwist
    (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (c : RadicalConjugacyClass (p := p) (G := G)) :
    radicalConjugacyEquiv f hf hcentral hker (RadicalConjugacyClass.rightTwist alpha c) =
      RadicalConjugacyClass.rightTwist beta (radicalConjugacyEquiv f hf hcentral hker c) := by
  refine Quotient.inductionOn c ?_
  intro Q
  change Quotient.mk'' (radicalSubgroupEquiv f hf hcentral hker (Q.rightTwist alpha)) =
    Quotient.mk'' ((radicalSubgroupEquiv f hf hcentral hker Q).rightTwist beta)
  rw [radicalSubgroupEquiv_rightTwist f hf hcentral hker alpha beta square Q]

theorem radicalConjugacyEquiv_op_smul
    (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (c : RadicalConjugacyClass (p := p) (G := G)) :
    radicalConjugacyEquiv f hf hcentral hker (MulOpposite.op alpha • c) =
      MulOpposite.op beta • radicalConjugacyEquiv f hf hcentral hker c :=
  radicalConjugacyEquiv_rightTwist f hf hcentral hker alpha beta square c

theorem radicalConjugacyEquiv_fixed_iff
    (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (c : RadicalConjugacyClass (p := p) (G := G)) :
    MulOpposite.op alpha • c = c ↔
      MulOpposite.op beta • radicalConjugacyEquiv f hf hcentral hker c =
        radicalConjugacyEquiv f hf hcentral hker c := by
  rw [← radicalConjugacyEquiv_op_smul f hf hcentral hker alpha beta square c]
  exact (radicalConjugacyEquiv f hf hcentral hker).injective.eq_iff.symm

theorem lifted_radical_class_fixed
    (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (R : RadicalSubgroup (p := p) (G := H))
    (hfixed : MulOpposite.op beta •
        (Quotient.mk'' R : RadicalConjugacyClass (p := p) (G := H)) = Quotient.mk'' R) :
    MulOpposite.op alpha •
        (Quotient.mk'' ((radicalSubgroupEquiv f hf hcentral hker).symm R) :
          RadicalConjugacyClass (p := p) (G := G)) =
      Quotient.mk'' ((radicalSubgroupEquiv f hf hcentral hker).symm R) := by
  apply (radicalConjugacyEquiv f hf hcentral hker).injective
  simpa only [radicalConjugacyEquiv_op_smul f hf hcentral hker alpha beta square,
    radicalConjugacyEquiv_mk_lift] using hfixed

theorem lifted_radical_classes_ne (R S : RadicalSubgroup (p := p) (G := H))
    (hne : (Quotient.mk'' R : RadicalConjugacyClass (p := p) (G := H)) ≠ Quotient.mk'' S) :
    (Quotient.mk'' ((radicalSubgroupEquiv f hf hcentral hker).symm R) :
      RadicalConjugacyClass (p := p) (G := G)) ≠
        Quotient.mk'' ((radicalSubgroupEquiv f hf hcentral hker).symm S) := by
  intro h
  apply hne
  have hmap := congrArg (radicalConjugacyEquiv f hf hcentral hker) h
  simpa only [radicalConjugacyEquiv_mk_lift] using hmap

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
