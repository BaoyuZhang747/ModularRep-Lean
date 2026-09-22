import Mathlib.Algebra.Group.Action.Pi
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter

/-!
# Restricting the actual return to a coordinate

An automorphism preserves a coordinate when its value there is determined
by an automorphism of that actual factor.  Such automorphisms form a
subgroup.  The factor automorphism is unique because coordinate projection
is onto, and therefore gives a homomorphism.  An exact equation for a
generator restricts every element of its literal `zpowers` subgroup.

This is group-theoretic infrastructure for the Type B cycle normalisation.
It has no character, selector, fixedness or stabiliser assumption.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBReturnCoordinateAction

variable {I : Type*} (X : I → Type*) [∀ i, Group (X i)]

/-- Projection from the actual product onto any of its factors is onto. -/
theorem coordinate_surjective (i : I) :
    Function.Surjective (fun x : (j : I) → X j ↦ x i) := by
  classical
  intro xi
  exact ⟨Function.update 1 i xi, by simp⟩

/-- Automorphisms whose action on the selected coordinate depends only on
that coordinate, through an actual automorphism of the factor. -/
def coordinatePreserving (i : I) : Subgroup (MulAut ((j : I) → X j)) where
  carrier := {a | ∃ beta : MulAut (X i), ∀ x, a x i = beta (x i)}
  one_mem' := ⟨1, fun _ ↦ rfl⟩
  mul_mem' := by
    rintro a b ⟨alpha, ha⟩ ⟨beta, hb⟩
    refine ⟨alpha * beta, ?_⟩
    intro x
    change a (b x) i = alpha (beta (x i))
    rw [ha, hb]
  inv_mem' := by
    rintro a ⟨alpha, ha⟩
    refine ⟨alpha⁻¹, ?_⟩
    intro x
    have h := congrArg alpha.symm (ha (a.symm x))
    simpa using h.symm

/-- The unique automorphism on the factor determined by the product action. -/
def restrictionAut (i : I) (a : coordinatePreserving X i) : MulAut (X i) :=
  Classical.choose a.property

theorem restrictionAut_value (i : I) (a : coordinatePreserving X i)
    (x : (j : I) → X j) :
    a.1 x i = restrictionAut X i a (x i) :=
  Classical.choose_spec a.property x

/-- The choice in `restrictionAut` is unique on the literal factor. -/
theorem restrictionAut_eq_of_value (i : I) (a : coordinatePreserving X i)
    (beta : MulAut (X i))
    (hbeta : ∀ x, a.1 x i = beta (x i)) :
    restrictionAut X i a = beta := by
  apply MulEquiv.ext
  intro xi
  obtain ⟨x, rfl⟩ := coordinate_surjective X i xi
  exact (restrictionAut_value X i a x).symm.trans (hbeta x)

/-- Restriction is a homomorphism; this follows from uniqueness, rather than
from a choice of exponents for elements of a cyclic group. -/
def restriction (i : I) : coordinatePreserving X i →* MulAut (X i) where
  toFun := restrictionAut X i
  map_one' := by
    apply restrictionAut_eq_of_value X i (1 : coordinatePreserving X i) 1
    intro x
    rfl
  map_mul' a b := by
    apply restrictionAut_eq_of_value X i (a * b)
      (restrictionAut X i a * restrictionAut X i b)
    intro x
    change a.1 (b.1 x) i = restrictionAut X i a (restrictionAut X i b (x i))
    rw [restrictionAut_value, restrictionAut_value]

theorem restriction_value (i : I) (a : coordinatePreserving X i)
    (x : (j : I) → X j) :
    a.1 x i = restriction X i a (x i) :=
  restrictionAut_value X i a x

variable {E : Type*} [Group E]

/-- Every power of the actual generator preserves the selected coordinate. -/
theorem zpowers_le_coordinatePreserving
    (outer : E →* MulAut ((j : I) → X j)) (s : E) (i : I)
    (beta : MulAut (X i)) (hgen : ∀ x, outer s x i = beta (x i)) :
    Subgroup.zpowers s ≤ (coordinatePreserving X i).comap outer := by
  apply Subgroup.zpowers_le.mpr
  exact ⟨beta, hgen⟩

/-- The actual outer homomorphism restricted to its literal cyclic subgroup,
with codomain restricted to coordinate-preserving automorphisms. -/
def returnLift
    (outer : E →* MulAut ((j : I) → X j)) (s : E) (i : I)
    (beta : MulAut (X i)) (hgen : ∀ x, outer s x i = beta (x i)) :
    Subgroup.zpowers s →* coordinatePreserving X i where
  toFun r := ⟨outer r.1, zpowers_le_coordinatePreserving X outer s i beta hgen r.2⟩
  map_one' := by
    apply Subtype.ext
    exact outer.map_one
  map_mul' r t := by
    apply Subtype.ext
    exact outer.map_mul r.1 t.1

/-- The coordinate action of the return group, determined by the actual
ambient homomorphism and a single generator equation. -/
def returnHom
    (outer : E →* MulAut ((j : I) → X j)) (s : E) (i : I)
    (beta : MulAut (X i)) (hgen : ∀ x, outer s x i = beta (x i)) :
    Subgroup.zpowers s →* MulAut (X i) :=
  (restriction X i).comp (returnLift X outer s i beta hgen)

/-- Exact coordinate restriction for every member of the return subgroup. -/
theorem returnHom_value
    (outer : E →* MulAut ((j : I) → X j)) (s : E) (i : I)
    (beta : MulAut (X i)) (hgen : ∀ x, outer s x i = beta (x i))
    (r : Subgroup.zpowers s) (x : (j : I) → X j) :
    outer r.1 x i = returnHom X outer s i beta hgen r (x i) :=
  restriction_value X i (returnLift X outer s i beta hgen r) x

/-- Restriction sends the literal generator to its proven factor automorphism. -/
theorem returnHom_generator_eq
    (outer : E →* MulAut ((j : I) → X j)) (s : E) (i : I)
    (beta : MulAut (X i)) (hgen : ∀ x, outer s x i = beta (x i)) :
    returnHom X outer s i beta hgen ⟨s, Subgroup.mem_zpowers s⟩ = beta := by
  apply restrictionAut_eq_of_value X i
    (returnLift X outer s i beta hgen ⟨s, Subgroup.mem_zpowers s⟩) beta
  exact hgen

section Compatibility

open TypeBRegularLeviCharacterActionAdapter

variable {J R : Type} (H D : J → Type)
variable [∀ j, Group (H j)] [∀ j, Group (D j)] [Group R]

/-- Global normalisation restricts to the actual coordinate actions.
All coordinate equations hold on the entire product, so surjectivity of
projection permits arbitrary factor elements in the resulting equality.
This derives the local semidirect compatibility needed for the return;
it is not a separate compatibility certificate. -/
theorem coordinateRestrictions_semidirectCompatible
    (diagonal : ∀ j, D j →* MulAut (H j))
    (outer : R →* MulAut ((j : J) → H j))
    (phi : R →* MulAut ((j : J) → D j))
    (i : J) (returnH : R →* MulAut (H i)) (returnD : R →* MulAut (D i))
    (normalises : AutomorphismSemidirectCompatible
      (coordinateMulAut H D diagonal) outer phi)
    (hH : ∀ r g, outer r g i = returnH r (g i))
    (hD : ∀ r d, phi r d i = returnD r (d i)) :
    AutomorphismSemidirectCompatible (diagonal i) returnH returnD := by
  intro r di
  apply MulEquiv.ext
  intro hi
  obtain ⟨d, rfl⟩ := coordinate_surjective D i di
  obtain ⟨g, rfl⟩ := coordinate_surjective H i hi
  have h := congrArg (fun a : MulAut ((j : J) → H j) ↦ a g i) (normalises r d)
  change diagonal i (phi r d i) (g i) =
    outer r ((coordinateMulAut H D diagonal d) ((outer r)⁻¹ g)) i at h
  rw [hD, hH] at h
  change diagonal i (returnD r (d i)) (g i) =
    returnH r (diagonal i (d i) ((outer r)⁻¹ g i)) at h
  have hinv : (outer r)⁻¹ g i = (returnH r)⁻¹ (g i) := by
    simpa only [map_inv] using hH r⁻¹ g
  rw [hinv] at h
  exact h

end Compatibility

end ModularRep.PaperProofs.TypeBReturnCoordinateAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
