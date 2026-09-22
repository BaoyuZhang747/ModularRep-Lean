import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Roots-of-unity equivalence fixed by two primitive roots

Two specified primitive m-th roots determine the unique multiplicative
equivalence of the full m-th-root groups carrying the first root to the
second. Both parametrizations use the same exponent in ZMod m.

This is a K construction over commutative domains. It assumes no map between
the rings, no characteristic or splitting-field certificate, and no supplied
root equivalence. The positive order is retained as `NeZero m`.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrimitiveRootEquivalence

universe u v w

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
variable {m : ℕ} [NeZero m] {a : A} {b : B}

/-- The specified ring element, viewed as a primitive unit. -/
theorem primitive_unit (ha : IsPrimitiveRoot a m) :
    IsPrimitiveRoot ha.toRootsOfUnity.val m :=
  IsPrimitiveRoot.coe_units_iff.mp ha

/-- Exponent parametrization of the entire root group using the specified root. -/
def parametrization (ha : IsPrimitiveRoot a m) :
    Multiplicative (ZMod m) ≃* rootsOfUnity m A :=
  (AddEquiv.toMultiplicativeLeft (primitive_unit ha).zmodEquivZPowers).trans
    (MulEquiv.subgroupCongr (primitive_unit ha).zpowers_eq)

/-- Natural exponents keep their literal root-group value. -/
theorem parametrization_nat (ha : IsPrimitiveRoot a m) (j : ℕ) :
    parametrization ha (Multiplicative.ofAdd (j : ZMod m)) =
      ha.toRootsOfUnity ^ j := by
  apply Subtype.ext
  change ((primitive_unit ha).zmodEquivZPowers (j : ZMod m)).toMul.val =
    ha.toRootsOfUnity.val ^ j
  rw [(primitive_unit ha).zmodEquivZPowers_apply_coe_nat]
  rfl

/-- The unique equivalence aligned with the two specified primitive roots. -/
def equiv (ha : IsPrimitiveRoot a m) (hb : IsPrimitiveRoot b m) :
    rootsOfUnity m A ≃* rootsOfUnity m B :=
  (parametrization ha).symm.trans (parametrization hb)

theorem equiv_parametrization (ha : IsPrimitiveRoot a m)
    (hb : IsPrimitiveRoot b m) (j : Multiplicative (ZMod m)) :
    equiv ha hb (parametrization ha j) = parametrization hb j := by
  exact congrArg (parametrization hb) ((parametrization ha).symm_apply_apply j)

/-- Equal natural powers of the specified roots correspond. -/
theorem equiv_pow (ha : IsPrimitiveRoot a m) (hb : IsPrimitiveRoot b m) (j : ℕ) :
    equiv ha hb (ha.toRootsOfUnity ^ j) = hb.toRootsOfUnity ^ j := by
  rw [← parametrization_nat ha j, equiv_parametrization, parametrization_nat]

theorem equiv_generator (ha : IsPrimitiveRoot a m) (hb : IsPrimitiveRoot b m) :
    equiv ha hb ha.toRootsOfUnity = hb.toRootsOfUnity := by
  simpa only [pow_one] using equiv_pow ha hb 1

/-- The target ring value is the same literal power of the specified target root. -/
theorem equiv_pow_value (ha : IsPrimitiveRoot a m) (hb : IsPrimitiveRoot b m) (j : ℕ) :
    (((equiv ha hb (ha.toRootsOfUnity ^ j)) : Bˣ) : B) = b ^ j := by
  rw [equiv_pow, rootsOfUnity.coe_pow]
  rfl

/-- Every source root is a bounded natural power of the specified generator. -/
theorem exists_pow (ha : IsPrimitiveRoot a m) (x : rootsOfUnity m A) :
    ∃ j < m, ha.toRootsOfUnity ^ j = x := by
  obtain ⟨j, hj, h⟩ := (primitive_unit ha).eq_pow_of_mem_rootsOfUnity x.property
  exact ⟨j, hj, Subtype.ext h⟩

/-- A pointwise value equation suffices; no equality of chosen unit presentations is needed. -/
theorem equiv_apply_of_value_eq_pow (ha : IsPrimitiveRoot a m)
    (hb : IsPrimitiveRoot b m) (x : rootsOfUnity m A) (j : ℕ)
    (hx : (x.val : A) = a ^ j) :
    (((equiv ha hb x) : Bˣ) : B) = b ^ j := by
  have hpow : (((ha.toRootsOfUnity ^ j) : Aˣ) : A) = a ^ j := by
    rw [Units.val_pow_eq_pow_val]
    rfl
  have hx' : x = ha.toRootsOfUnity ^ j :=
    rootsOfUnity.coe_injective (hx.trans hpow.symm)
  rw [hx']
  exact equiv_pow_value ha hb j

/-- A homomorphism from the root group is determined by this one specified root. -/
theorem hom_ext (ha : IsPrimitiveRoot a m) {G : Type w} [Monoid G]
    (f g : rootsOfUnity m A →* G) (h : f ha.toRootsOfUnity = g ha.toRootsOfUnity) :
    f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨j, _, rfl⟩ := exists_pow ha x
  simp only [map_pow, h]

/-- Uniqueness is among all group equivalences with the specified generator value. -/
theorem equiv_unique (ha : IsPrimitiveRoot a m) (hb : IsPrimitiveRoot b m)
    (e : rootsOfUnity m A ≃* rootsOfUnity m B)
    (h : e ha.toRootsOfUnity = hb.toRootsOfUnity) : e = equiv ha hb := by
  have he := hom_ext ha e.toMonoidHom (equiv ha hb).toMonoidHom
    (h.trans (equiv_generator ha hb).symm)
  apply MulEquiv.ext
  intro x
  exact DFunLike.congr_fun he x

end ModularRep.PaperProofs.TypeBPrimitiveRootEquivalence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
