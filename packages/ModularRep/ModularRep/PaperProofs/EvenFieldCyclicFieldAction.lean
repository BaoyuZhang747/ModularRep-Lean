import ModularRep.PaperProofs.EvenFieldFrobeniusPowers
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The cyclic field action on a Frobenius fixed-point group

Let `F₂` be a group endomorphism and let `a > 0`.  On the subgroup fixed by
the `a`th iterate of `F₂`, the restriction of `F₂` is an automorphism whose
order divides `a`.  This file constructs the resulting genuine action of
`Multiplicative (ZMod a)` and proves that the class represented by `j` acts as
the `j`th iterate of `F₂`.

This is the elementary action-theoretic part of the manuscript notation
`E_H = ⟨F₂⟩`.  It does not assert that the action is faithful, so the actual
field automorphism group can be a proper quotient if the order of the
restriction is smaller than `a`.
-/

namespace ModularRep.PaperProofs.EvenFieldCyclicFieldAction

open ModularRep.PaperProofs.EvenFieldSourceShaped
open ModularRep.PaperProofs.EvenFieldFrobeniusPowers

universe u

variable {G : Type u} [Group G]

/-- The fixed-point subgroup of the `a`th iterate of `F₂`. -/
abbrev FixedPoints (F₂ : G →* G) (a : ℕ) :=
  frobeniusFixedSubgroup (iterateMonoidHom F₂ a)

/-- On the fixed points of `F₂^[a]`, the restriction of `F₂` is a group
automorphism.  Its displayed inverse is the restriction of `F₂^[a - 1]`.
The positivity of `a` is essential for this formula. -/
def fieldGeneratorEquiv (F₂ : G →* G) (a : ℕ) (ha : 0 < a) :
    FixedPoints F₂ a ≃* FixedPoints F₂ a where
  toFun := fieldPowerOnFixedSubgroup F₂ a 1
  invFun := fieldPowerOnFixedSubgroup F₂ a (a - 1)
  left_inv x := by
    rw [fieldPowerOnFixedSubgroup_add]
    have hsum : a - 1 + 1 = a := Nat.sub_add_cancel ha
    rw [hsum]
    exact Subtype.ext x.property
  right_inv x := by
    rw [fieldPowerOnFixedSubgroup_add]
    have hsum : 1 + (a - 1) = a := by omega
    rw [hsum]
    exact Subtype.ext x.property
  map_mul' x y := by
    exact map_mul (fieldPowerOnFixedSubgroup F₂ a 1) x y

@[simp]
theorem fieldGeneratorEquiv_apply (F₂ : G →* G) (a : ℕ) (ha : 0 < a)
    (x : FixedPoints F₂ a) :
    (fieldGeneratorEquiv F₂ a ha x : G) = iterateMonoidHom F₂ 1 (x : G) :=
  rfl

/-- The `n`th power of the generator acts as the `n`th iterate of `F₂`. -/
theorem fieldGeneratorEquiv_pow_apply (F₂ : G →* G) (a n : ℕ) (ha : 0 < a)
    (x : FixedPoints F₂ a) :
    (fieldGeneratorEquiv F₂ a ha ^ n) x =
      fieldPowerOnFixedSubgroup F₂ a n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change (fieldGeneratorEquiv F₂ a ha ^ n)
          (fieldGeneratorEquiv F₂ a ha x) = _
      rw [ih]
      exact fieldPowerOnFixedSubgroup_add F₂ a n 1 x

/-- The generator has exponent dividing `a` on the fixed-point subgroup. -/
theorem fieldGeneratorEquiv_pow_definingExponent
    (F₂ : G →* G) (a : ℕ) (ha : 0 < a) :
    fieldGeneratorEquiv F₂ a ha ^ a = 1 := by
  ext x
  rw [fieldGeneratorEquiv_pow_apply]
  change iterateMonoidHom F₂ a (x : G) = x
  exact x.property

/-- The additive homomorphism from integer exponents to powers of the field
generator. -/
def integerFieldPowerHom (F₂ : G →* G) (a : ℕ) (ha : 0 < a) :
    ℤ →+ Additive (FixedPoints F₂ a ≃* FixedPoints F₂ a) :=
  zmultiplesHom _ (Additive.ofMul (fieldGeneratorEquiv F₂ a ha))

@[simp]
theorem integerFieldPowerHom_apply_nat
    (F₂ : G →* G) (a n : ℕ) (ha : 0 < a) :
    integerFieldPowerHom F₂ a ha n =
      Additive.ofMul (fieldGeneratorEquiv F₂ a ha ^ n) := by
  simp [integerFieldPowerHom, zmultiplesHom_apply]

/-- Integer field powers descend through reduction modulo `a`. -/
def zmodFieldPowerAddHom (F₂ : G →* G) (a : ℕ) (ha : 0 < a) :
    ZMod a →+ Additive (FixedPoints F₂ a ≃* FixedPoints F₂ a) :=
  ZMod.lift a ⟨integerFieldPowerHom F₂ a ha, by
    rw [integerFieldPowerHom_apply_nat, fieldGeneratorEquiv_pow_definingExponent]
    rfl⟩

/-- The genuine cyclic group homomorphism implementing the field action. -/
def fieldActionHom (F₂ : G →* G) (a : ℕ) (ha : 0 < a) :
    Multiplicative (ZMod a) →* (FixedPoints F₂ a ≃* FixedPoints F₂ a) :=
  AddMonoidHom.toMultiplicativeLeft (zmodFieldPowerAddHom F₂ a ha)

/-- The residue class of a natural number `n` acts as the `n`th Frobenius
power on the fixed-point group. -/
theorem fieldActionHom_natCast_apply
    (F₂ : G →* G) (a n : ℕ) (ha : 0 < a)
    (x : FixedPoints F₂ a) :
    fieldActionHom F₂ a ha (Multiplicative.ofAdd (n : ZMod a)) x =
      fieldPowerOnFixedSubgroup F₂ a n x := by
  change (zmodFieldPowerAddHom F₂ a ha (n : ZMod a)).toMul x = _
  rw [show (n : ZMod a) = ((n : ℤ) : ZMod a) by simp]
  simp only [zmodFieldPowerAddHom, ZMod.lift_coe]
  change (fieldGeneratorEquiv F₂ a ha ^ n) x = _
  exact fieldGeneratorEquiv_pow_apply F₂ a n ha x

/-- As an automorphism, the image of the residue class of `n` is the `n`th
power of the restricted Frobenius generator. -/
theorem fieldActionHom_natCast_eq
    (F₂ : G →* G) (a n : ℕ) (ha : 0 < a) :
    fieldActionHom F₂ a ha (Multiplicative.ofAdd (n : ZMod a)) =
      fieldGeneratorEquiv F₂ a ha ^ n := by
  ext x
  rw [fieldActionHom_natCast_apply, fieldGeneratorEquiv_pow_apply]

/-- Every element of the cyclic field group acts by the Frobenius power
given by its canonical residue representative. -/
theorem fieldActionHom_apply_val
    (F₂ : G →* G) (a : ℕ) (ha : 0 < a)
    (sigma : Multiplicative (ZMod a)) (x : FixedPoints F₂ a) :
    fieldActionHom F₂ a ha sigma x =
      fieldPowerOnFixedSubgroup F₂ a sigma.toAdd.val x := by
  let _ : NeZero a := ⟨Nat.ne_of_gt ha⟩
  let n := sigma.toAdd.val
  have hsigma : sigma = Multiplicative.ofAdd (n : ZMod a) := by
    apply Multiplicative.ext
    exact (ZMod.natCast_zmod_val sigma.toAdd).symm
  calc
    fieldActionHom F₂ a ha sigma x =
        fieldActionHom F₂ a ha
          (Multiplicative.ofAdd (n : ZMod a)) x :=
      congrArg (fun s => fieldActionHom F₂ a ha s x) hsigma
    _ = fieldPowerOnFixedSubgroup F₂ a n x :=
      fieldActionHom_natCast_apply F₂ a n ha x
    _ = fieldPowerOnFixedSubgroup F₂ a sigma.toAdd.val x := rfl

/-- Every element of the cyclic group maps to the corresponding power of the
restricted Frobenius generator. -/
theorem fieldActionHom_eq_generator_pow_val
    (F₂ : G →* G) (a : ℕ) (ha : 0 < a)
    (sigma : Multiplicative (ZMod a)) :
    fieldActionHom F₂ a ha sigma =
      fieldGeneratorEquiv F₂ a ha ^ sigma.toAdd.val := by
  ext x
  rw [fieldActionHom_apply_val, fieldGeneratorEquiv_pow_apply]

/-- The action of the cyclic field group obtained from `fieldActionHom`. -/
@[instance_reducible]
def cyclicFieldMulAction (F₂ : G →* G) (a : ℕ) (ha : 0 < a) :
    MulAction (Multiplicative (ZMod a)) (FixedPoints F₂ a) :=
  MulAction.compHom _ (fieldActionHom F₂ a ha)

/-- In the induced action, the residue class of `n` acts as `F₂^[n]`. -/
theorem cyclicFieldMulAction_natCast_smul
    (F₂ : G →* G) (a n : ℕ) (ha : 0 < a)
    (x : FixedPoints F₂ a) :
    letI := cyclicFieldMulAction F₂ a ha
    Multiplicative.ofAdd (n : ZMod a) • x =
      fieldPowerOnFixedSubgroup F₂ a n x := by
  change fieldActionHom F₂ a ha (Multiplicative.ofAdd (n : ZMod a)) x = _
  exact fieldActionHom_natCast_apply F₂ a n ha x

/-- In the induced action, an arbitrary residue class acts by the Frobenius
power indexed by its canonical representative. -/
theorem cyclicFieldMulAction_smul_eq_val
    (F₂ : G →* G) (a : ℕ) (ha : 0 < a)
    (sigma : Multiplicative (ZMod a)) (x : FixedPoints F₂ a) :
    letI := cyclicFieldMulAction F₂ a ha
    sigma • x = fieldPowerOnFixedSubgroup F₂ a sigma.toAdd.val x := by
  change fieldActionHom F₂ a ha sigma x = _
  exact fieldActionHom_apply_val F₂ a ha sigma x

end ModularRep.PaperProofs.EvenFieldCyclicFieldAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
