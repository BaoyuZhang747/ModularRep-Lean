import ModularRep.ExactGrothendieckGroup
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Prod

open CategoryTheory

namespace ModularRep.ModuleCategoryKZeroTrivial

universe u

variable {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- The countable product of copies of `M` absorbs one further copy. -/
private def shiftEquiv : (M × (ℕ → M)) ≃ₗ[R] (ℕ → M) where
  toFun x
    | 0 => x.1
    | n + 1 => x.2 n
  invFun f := (f 0, fun n => f (n + 1))
  left_inv x := by
    rcases x with ⟨x, f⟩
    ext n <;> simp
  right_inv f := by
    ext n
    cases n <;> rfl
  map_add' x y := by
    ext n
    cases n <;> rfl
  map_smul' r x := by
    ext n
    cases n <;> rfl

/-- The standard split short exact sequence `M ⟶ M × N ⟶ N`. -/
private def splitShortComplex : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk
    (LinearMap.inl R M (ℕ → M))
    (LinearMap.snd R M (ℕ → M))
    (by ext; simp)

private theorem splitShortComplex_shortExact :
    (splitShortComplex (R := R) (M := M)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · rw [LinearMap.exact_iff]
    change
      LinearMap.ker (LinearMap.snd R M (ℕ → M)) =
        LinearMap.range (LinearMap.inl R M (ℕ → M))
    exact LinearMap.ker_snd R M (ℕ → M)
  · change Function.Injective (LinearMap.inl R M (ℕ → M))
    exact LinearMap.inl_injective
  · change Function.Surjective (LinearMap.snd R M (ℕ → M))
    exact LinearMap.snd_surjective

/-- The exact `K₀` presentation of the category of all modules is trivial. -/
theorem classOf_eq_zero :
    ModularRep.ExactGrothendieckGroup.classOf (ModuleCat.{u} R)
      (ModuleCat.of R M) = 0 := by
  have h := ModularRep.ExactGrothendieckGroup.classOf_middle_eq
    (ModuleCat.{u} R) (splitShortComplex (R := R) (M := M))
      (splitShortComplex_shortExact (R := R) (M := M))
  have hi := ModularRep.ExactGrothendieckGroup.classOf_iso
    (ModuleCat.{u} R) (LinearEquiv.toModuleIso (shiftEquiv (R := R) (M := M)))
  apply add_right_cancel (b :=
    ModularRep.ExactGrothendieckGroup.classOf (ModuleCat.{u} R)
      (ModuleCat.of R (ℕ → M)))
  rw [zero_add]
  exact h.symm.trans hi

/-- Consequently the whole exact `K₀` presentation of the category of all
modules is a subsingleton. -/
theorem kZero_subsingleton :
    Subsingleton
      (ModularRep.ExactGrothendieckGroup.KZero (ModuleCat.{u} R)) := by
  constructor
  intro x y
  have all_eq_zero :
      ∀ z : ModularRep.ExactGrothendieckGroup.KZero (ModuleCat.{u} R), z = 0 := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
      (ModularRep.ExactGrothendieckGroup.shortExactRelationSubgroup
        (ModuleCat.{u} R)) z
    induction a using FreeAbelianGroup.induction_on with
    | zero => rfl
    | of X =>
        have h := classOf_eq_zero (R := R)
          (M := (CategoryTheory.fromSkeleton (ModuleCat.{u} R)).obj X)
        simpa [ModularRep.ExactGrothendieckGroup.classOf,
          CategoryTheory.toSkeleton_fromSkeleton_obj] using h
    | neg X h => simpa using congrArg Neg.neg h
    | add x y hx hy =>
        have hx' :
            (x : ModularRep.ExactGrothendieckGroup.KZero (ModuleCat.{u} R)) = 0 := hx
        have hy' :
            (y : ModularRep.ExactGrothendieckGroup.KZero (ModuleCat.{u} R)) = 0 := hy
        simp [hx', hy']
  exact (all_eq_zero x).trans (all_eq_zero y).symm

end ModularRep.ModuleCategoryKZeroTrivial


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
