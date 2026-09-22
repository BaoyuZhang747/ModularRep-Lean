import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights

/-! Raw-character descent is independent of conjugate representatives.
The downstairs conjugator is the image of the original conjugator. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses

open ModularRep ModularRep.CharacterWeight
open CentralEllPrimeWeightLocalQuotient
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights

universe u
variable {p : ℕ} {K X : Type u}
variable [Field K] [CharZero K] [Group X] [Finite X]

def rawClass (W : CharacterWeight p K X) :
    ConjugacyClass (p := p) (K := K) (G := X) :=
  Quotient.mk'' (Quotient.mk'' W)

theorem rawClass_surjective :
    Function.Surjective (rawClass (p := p) (K := K) (X := X)) := by
  intro w
  obtain ⟨v, rfl⟩ := Quotient.exists_rep w
  obtain ⟨W, rfl⟩ := Quotient.exists_rep v
  exact ⟨W, rfl⟩

theorem rawClass_eq_iff (W V : CharacterWeight p K X) :
    rawClass W = rawClass V ↔
      ∃ g : X, W = V.rightTwist (MulAut.conj g⁻¹) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    change (Quotient.mk'' (V.rightTwist (MulAut.conj g⁻¹)) :
      IsoClass (p := p) (K := K) (G := X)) = Quotient.mk'' W at hg
    exact ⟨g, (CharacterWeight.eq_of_isomorphic
      (Quotient.exact (s := CharacterWeight.isomorphicSetoid) hg)).symm⟩
  · rintro ⟨g, rfl⟩
    exact Quotient.sound ⟨g, rfl⟩

theorem rawClass_rightTwist (W : CharacterWeight p K X) (alpha : MulAut X) :
    rawClass (W.rightTwist alpha) = MulOpposite.op alpha • rawClass W := rfl

omit [Finite X] in
theorem inner_square {Y : Type u} [Group Y] (q : X →* Y) (g x : X) :
    q (MulAut.conj g⁻¹ x) = MulAut.conj (q g)⁻¹ (q x) := by
  simp

variable (Z : Subgroup X) [Z.Normal]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

theorem rawDescent_class_congr (W V : CharacterWeight p K X)
    (hW : KernelConstant Z W) (hV : KernelConstant Z V)
    (hclass : rawClass W = rawClass V) :
    rawClass (rawDescent Z hcentral hprimeTo W hW) =
      rawClass (rawDescent Z hcentral hprimeTo V hV) := by
  obtain ⟨g, rfl⟩ := (rawClass_eq_iff W V).mp hclass
  apply (rawClass_eq_iff _ _).mpr
  refine ⟨QuotientGroup.mk' Z g, ?_⟩
  exact rawDescent_rightTwist Z hcentral hprimeTo V hV
    (MulAut.conj g⁻¹) (MulAut.conj (QuotientGroup.mk' Z g)⁻¹)
    (fun x => inner_square (QuotientGroup.mk' Z) g x)

theorem kernelConstant_of_factorisation (W : CharacterWeight p K X)
    (eta : OrdinaryIrreducibleCharacter.Irr K
      (NormalizerQuotient (W.subgroup.map (QuotientGroup.mk' Z))))
    (factor : ∀ x, W.localCharacter x = eta (qW Z W.subgroup x)) :
    KernelConstant Z W := by
  intro x
  rw [factor x.val, factor 1, MonoidHom.mem_ker.mp x.property, map_one]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
