import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Square classes of the actual units of a finite odd field

The subgroup is mathlib's literal subgroup of squares in `Fˣ`. Its index
is computed by the existing power-map index theorem for finite cyclic
groups and `Nat.card_units`. The quotient is then identified with the
existing two-element cyclic group. No quadratic-character, norm, centre,
diagonal-action or published-source certificate is an input.

The cardinality hypothesis is `Odd (Nat.card F)`. This formulation uses
only `[Finite F]` and does not select an external enumeration of the field.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFiniteFieldSquareClass

universe u

variable (F : Type u) [Field F]

/-- Squares in the actual field unit group. -/
abbrev squareSubgroup : Subgroup Fˣ := Subgroup.square Fˣ

/-- Square membership is witnessed by an actual field unit. -/
theorem mem_squareSubgroup_iff_exists_sq (a : Fˣ) :
    a ∈ squareSubgroup F ↔ ∃ z : Fˣ, z ^ 2 = a := by
  change IsSquare a ↔ ∃ z : Fˣ, z ^ 2 = a
  rw [isSquare_iff_exists_sq]
  exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩

/-- The same subgroup is the range of the existing squaring homomorphism. -/
theorem squareSubgroup_eq_range :
    squareSubgroup F = (powMonoidHom 2 : Fˣ →* Fˣ).range := by
  ext a
  exact mem_squareSubgroup_iff_exists_sq F a

/-- The literal unit quotient, before identifying its two elements. -/
abbrev SquareClass := Fˣ ⧸ squareSubgroup F

/-- The canonical quotient map on actual units. -/
def quotientMap : Fˣ →* SquareClass F :=
  QuotientGroup.mk' (squareSubgroup F)

theorem quotientMap_surjective : Function.Surjective (quotientMap F) :=
  QuotientGroup.mk'_surjective (squareSubgroup F)

@[simp] theorem quotientMap_kernel : (quotientMap F).ker = squareSubgroup F :=
  QuotientGroup.ker_mk' (squareSubgroup F)

theorem quotientMap_eq_one_iff (a : Fˣ) :
    quotientMap F a = 1 ↔ ∃ z : Fˣ, z ^ 2 = a := by
  change a ∈ (quotientMap F).ker ↔ ∃ z : Fˣ, z ^ 2 = a
  rw [quotientMap_kernel]
  exact mem_squareSubgroup_iff_exists_sq F a

variable [Finite F]

/-- Odd field cardinality makes the actual unit group have even cardinality. -/
theorem two_dvd_card_units (hOdd : Odd (Nat.card F)) : 2 ∣ Nat.card Fˣ := by
  obtain ⟨m, hm⟩ := hOdd.exists_bit1
  rw [Nat.card_units, hm, Nat.add_sub_cancel]
  exact dvd_mul_right 2 m

/-- The cyclic power-map index formula gives precisely two square classes. -/
theorem squareClass_card (hOdd : Odd (Nat.card F)) :
    Nat.card (SquareClass F) = 2 := by
  change (squareSubgroup F).index = 2
  rw [squareSubgroup_eq_range, IsCyclic.index_powMonoidHom_range]
  exact Nat.gcd_eq_right (two_dvd_card_units F hOdd)

/-- A group equivalence with the actual two-element cyclic group. -/
def squareClassEquiv (hOdd : Odd (Nat.card F)) :
    SquareClass F ≃* Multiplicative (ZMod 2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact mulEquivOfPrimeCardEq (p := 2) (squareClass_card F hOdd)
    (by simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])

/-- The square-class homomorphism to `Multiplicative (ZMod 2)`. -/
def squareClassMap (hOdd : Odd (Nat.card F)) : Fˣ →* Multiplicative (ZMod 2) :=
  (squareClassEquiv F hOdd).toMonoidHom.comp (quotientMap F)

theorem squareClassMap_apply (hOdd : Odd (Nat.card F)) (a : Fˣ) :
    squareClassMap F hOdd a = squareClassEquiv F hOdd (quotientMap F a) := rfl

theorem squareClassMap_surjective (hOdd : Odd (Nat.card F)) :
    Function.Surjective (squareClassMap F hOdd) :=
  (squareClassEquiv F hOdd).surjective.comp (quotientMap_surjective F)

/-- No larger subgroup is lost when the quotient is identified with `C₂`. -/
@[simp] theorem squareClassMap_kernel (hOdd : Odd (Nat.card F)) :
    (squareClassMap F hOdd).ker = squareSubgroup F := by
  exact (MonoidHom.ker_comp_of_injective (quotientMap F)
    (squareClassEquiv F hOdd).toMonoidHom (squareClassEquiv F hOdd).injective).trans
      (quotientMap_kernel F)

theorem squareClassMap_eq_one_iff (hOdd : Odd (Nat.card F)) (a : Fˣ) :
    squareClassMap F hOdd a = 1 ↔ ∃ z : Fˣ, z ^ 2 = a := by
  change a ∈ (squareClassMap F hOdd).ker ↔ ∃ z : Fˣ, z ^ 2 = a
  rw [squareClassMap_kernel]
  exact mem_squareSubgroup_iff_exists_sq F a

@[simp] theorem squareClassMap_sq (hOdd : Odd (Nat.card F)) (z : Fˣ) :
    squareClassMap F hOdd (z ^ 2) = 1 :=
  (squareClassMap_eq_one_iff F hOdd (z ^ 2)).mpr ⟨z, rfl⟩

end ModularRep.PaperProofs.TypeBFiniteFieldSquareClass


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
