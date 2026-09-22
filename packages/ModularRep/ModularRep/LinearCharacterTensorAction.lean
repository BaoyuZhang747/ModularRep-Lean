import ModularRep.OrdinaryIrreducibleCharacter
import Formalisation.SemidirectStabilizer

/-!
# Tensoring by linear characters

The conformal-group arguments use an action obtained by tensoring an
irreducible character with a linear character.  On a fixed representation
space this operation multiplies every representing matrix by the scalar value
of the linear character.  This file constructs that operation directly,
proves that it preserves irreducibility, and installs the manuscript's right
action on function-valued ordinary irreducible characters.

No block-theoretic or character-parametrisation conclusion is assumed here.
-/

noncomputable section

namespace Representation

universe u v

variable {k G V W : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- Tensor a representation with a linear character while retaining the
same underlying vector space. -/
def linearCharacterTwist (rho : Representation k G V) (lambda : G →* kˣ) :
    Representation k G V where
  toFun g := (lambda g : k) • rho g
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply,
      Module.End.mul_apply]
    simp only [map_smul, smul_smul]

@[simp]
theorem linearCharacterTwist_apply
    (rho : Representation k G V) (lambda : G →* kˣ) (g : G) (x : V) :
    rho.linearCharacterTwist lambda g x = (lambda g : k) • rho g x :=
  rfl

@[simp]
theorem linearCharacterTwist_one (rho : Representation k G V) :
    rho.linearCharacterTwist (1 : G →* kˣ) = rho := by
  ext g x
  simp

@[simp]
theorem linearCharacterTwist_mul
    (rho : Representation k G V) (lambda mu : G →* kˣ) :
    (rho.linearCharacterTwist lambda).linearCharacterTwist mu =
      rho.linearCharacterTwist (lambda * mu) := by
  ext g x
  simp only [linearCharacterTwist_apply, MonoidHom.mul_apply, Units.val_mul,
    smul_smul]
  rw [mul_comm (mu g : k) (lambda g : k)]

/-- Twisting an intertwiner by a linear character does not change its
underlying linear map. -/
def Equiv.linearCharacterTwist
    {rho : Representation k G V} {sigma : Representation k G W}
    (e : Equiv rho sigma) (lambda : G →* kˣ) :
    Equiv (rho.linearCharacterTwist lambda)
      (sigma.linearCharacterTwist lambda) :=
  Equiv.mk e.toLinearEquiv fun g ↦ by
    ext x
    change e.toLinearEquiv ((lambda g : k) • rho g x) =
      (lambda g : k) • sigma g (e.toLinearEquiv x)
    rw [map_smul]
    exact congrArg (fun y : W ↦ (lambda g : k) • y)
      (congr($(e.isIntertwining' g) x))

/-- Invariant subspaces are unchanged by tensoring with a linear character.
The reverse implication uses that every value of a linear character is a
unit. -/
def subrepresentationLinearCharacterTwistOrderIso
    (rho : Representation k G V) (lambda : G →* kˣ) :
    Subrepresentation (rho.linearCharacterTwist lambda) ≃o
      Subrepresentation rho where
  toFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        have htwisted := U.apply_mem_toSubmodule g hx
        have hscaled := U.toSubmodule.smul_mem ((lambda g)⁻¹ : k) htwisted
        simpa [mul_smul] using hscaled }
  invFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        exact U.toSubmodule.smul_mem (lambda g : k)
          (U.apply_mem_toSubmodule g hx) }
  left_inv U := by
    apply Subrepresentation.ext
    rfl
  right_inv U := by
    apply Subrepresentation.ext
    rfl
  map_rel_iff' := by
    rfl

/-- Tensoring by a linear character preserves and reflects irreducibility. -/
theorem isIrreducible_linearCharacterTwist_iff
    (rho : Representation k G V) (lambda : G →* kˣ) :
    IsIrreducible (rho.linearCharacterTwist lambda) ↔ IsIrreducible rho :=
  OrderIso.isSimpleOrder_iff
    (subrepresentationLinearCharacterTwistOrderIso rho lambda)

namespace IsIrreducible

/-- An irreducible representation remains irreducible after tensoring by a
linear character. -/
theorem linearCharacterTwist
    {rho : Representation k G V} (hrho : IsIrreducible rho)
    (lambda : G →* kˣ) :
    IsIrreducible (rho.linearCharacterTwist lambda) :=
  (isIrreducible_linearCharacterTwist_iff rho lambda).2 hrho

end IsIrreducible

variable [FiniteDimensional k V]

/-- The trace character of a linear character twist is the pointwise product
of the two character values. -/
@[simp]
theorem character_linearCharacterTwist
    (rho : Representation k G V) (lambda : G →* kˣ) (g : G) :
    (rho.linearCharacterTwist lambda).character g =
      (lambda g : k) * rho.character g := by
  change LinearMap.trace k V ((lambda g : k) • rho g) = _
  rw [map_smul]
  rfl

/-- Tensoring and automorphism twisting commute after the linear character
is pulled back by the same automorphism. -/
theorem linearCharacterTwist_twist
    (rho : Representation k G V) (lambda : G →* kˣ)
    (alpha : MulAut G) :
    (rho.linearCharacterTwist lambda).twist alpha =
      (rho.twist alpha).linearCharacterTwist
        (lambda.comp alpha.toMonoidHom) := by
  rfl

end Representation

namespace ModularRep.OrdinaryIrreducibleCharacter

universe u

variable {k G : Type u} [Field k] [CharZero k] [Group G]

/-- Tensor a function-valued ordinary irreducible character with a linear
character. -/
def linearTwist (chi : Irr k G) (lambda : G →* kˣ) : Irr k G :=
  ⟨fun g ↦ (lambda g : k) * chi g, by
    rcases chi.property with ⟨R⟩
    refine ⟨
      { dimension := R.dimension
        representation := R.representation.linearCharacterTwist lambda
        irreducible := R.irreducible.linearCharacterTwist lambda
        character_eq := by
          funext g
          rw [Representation.character_linearCharacterTwist,
            R.character_eq] }
    ⟩⟩

@[simp]
theorem linearTwist_apply
    (chi : Irr k G) (lambda : G →* kˣ) (g : G) :
    linearTwist chi lambda g = (lambda g : k) * chi g :=
  rfl

@[simp]
theorem linearTwist_one (chi : Irr k G) :
    linearTwist chi (1 : G →* kˣ) = chi := by
  ext g
  simp

@[simp]
theorem linearTwist_mul
    (chi : Irr k G) (lambda mu : G →* kˣ) :
    linearTwist (linearTwist chi lambda) mu =
      linearTwist chi (lambda * mu) := by
  ext g
  simp only [linearTwist_apply, MonoidHom.mul_apply, Units.val_mul]
  ring

/-- The manuscript's right tensor action, encoded as a left action of the
opposite linear character group. -/
instance : MulAction (G →* kˣ)ᵐᵒᵖ (Irr k G) where
  smul lambda chi := linearTwist chi lambda.unop
  one_smul chi := by
    change linearTwist chi (MulOpposite.unop 1) = chi
    rw [MulOpposite.unop_one, linearTwist_one]
  mul_smul lambda mu chi := by
    change linearTwist chi (MulOpposite.unop (lambda * mu)) =
      linearTwist (linearTwist chi mu.unop) lambda.unop
    rw [MulOpposite.unop_mul, linearTwist_mul]

@[simp]
theorem op_smul_apply
    (lambda : (G →* kˣ)ᵐᵒᵖ) (chi : Irr k G) (g : G) :
    (lambda • chi) g = (lambda.unop g : k) * chi g :=
  rfl

/-- Tensoring with a linear character commutes with the manuscript's right
automorphism twist after pulling back the linear character. -/
theorem twist_linearTwist
    (chi : Irr k G) (lambda : G →* kˣ) (alpha : MulAut G) :
    twist k G (linearTwist chi lambda) alpha =
      linearTwist (twist k G chi alpha)
        (lambda.comp alpha.toMonoidHom) := by
  ext g
  rfl

@[simp]
theorem twist_mul
    (chi : Irr k G) (alpha beta : MulAut G) :
    twist k G (twist k G chi alpha) beta =
      twist k G chi (alpha * beta) := by
  ext g
  rfl

/-! ## The combined tensor and field action -/

variable {A : Type u} [Group A]

/-- Pullback of linear characters by a group automorphism. -/
def linearCharacterPrecompMulEquiv (alpha : MulAut G) :
    (G →* kˣ) ≃* (G →* kˣ) where
  toFun lambda := lambda.comp alpha.toMonoidHom
  invFun lambda := lambda.comp alpha.symm.toMonoidHom
  left_inv lambda := by
    ext g
    simp
  right_inv lambda := by
    ext g
    simp
  map_mul' lambda mu := by
    ext g
    rfl

@[simp]
theorem linearCharacterPrecompMulEquiv_apply
    (alpha : MulAut G) (lambda : G →* kˣ) (g : G) :
    linearCharacterPrecompMulEquiv alpha lambda g = lambda (alpha g) :=
  rfl

/-- The action of a field-automorphism group on linear characters.  The
inverse appears because Lean uses a left action to encode the manuscript's
right action. -/
def linearCharacterFieldAction (field : A →* MulAut G) :
    A →* MulAut (G →* kˣ) where
  toFun a := linearCharacterPrecompMulEquiv (field a⁻¹)
  map_one' := by
    ext lambda g
    simp [linearCharacterPrecompMulEquiv]
  map_mul' a b := by
    ext lambda g
    simp [linearCharacterPrecompMulEquiv, mul_inv_rev]

/-- Tensoring by linear characters as a left action.  An element `lambda`
acts by tensoring with `lambda⁻¹`, so its orbits and stabilisers are those of
the manuscript's right tensor action. -/
@[instance_reducible]
def inverseTensorAction : MulAction (G →* kˣ) (Irr k G) where
  smul lambda chi := linearTwist chi lambda⁻¹
  one_smul chi := by
    change linearTwist chi (1 : G →* kˣ)⁻¹ = chi
    apply OrdinaryIrreducibleCharacter.ext
    intro g
    change ((((1 : G →* kˣ)⁻¹) g : k) * chi g) = chi g
    simp
  mul_smul lambda mu chi := by
    change linearTwist chi (lambda * mu)⁻¹ =
      linearTwist (linearTwist chi mu⁻¹) lambda⁻¹
    calc
      linearTwist chi (lambda * mu)⁻¹ =
          linearTwist chi (mu⁻¹ * lambda⁻¹) := by
            exact congrArg (linearTwist chi) (mul_inv_rev lambda mu)
      _ = linearTwist (linearTwist chi mu⁻¹) lambda⁻¹ :=
        (linearTwist_mul chi mu⁻¹ lambda⁻¹).symm

/-- Field automorphisms as a left action encoding the manuscript's right
automorphism action. -/
@[instance_reducible]
def inverseFieldAction (field : A →* MulAut G) :
    MulAction A (Irr k G) where
  smul a chi := twist k G chi (field a⁻¹)
  one_smul chi := by
    change twist k G chi (field (1 : A)⁻¹) = chi
    rw [inv_one, map_one]
    exact twist_refl k G chi
  mul_smul a b chi := by
    change twist k G chi (field (a * b)⁻¹) =
      twist k G (twist k G chi (field b⁻¹)) (field a⁻¹)
    calc
      twist k G chi (field (a * b)⁻¹) =
          twist k G chi (field b⁻¹ * field a⁻¹) := by
            congr 2
            rw [mul_inv_rev, map_mul]
      _ = twist k G (twist k G chi (field b⁻¹)) (field a⁻¹) :=
        (twist_mul chi (field b⁻¹) (field a⁻¹)).symm

/-- The actual tensor and field actions satisfy the semidirect compatibility
identity required to act on ordinary irreducible characters. -/
theorem tensorField_semidirectCompatible
    (field : A →* MulAut G) :
    @Formalisation.SemidirectActionCompatible
      (G →* kˣ) A (Irr k G) _ _
      (inverseTensorAction : MulAction (G →* kˣ) (Irr k G))
      (inverseFieldAction field : MulAction A (Irr k G))
      (linearCharacterFieldAction (k := k) field) := by
  intro a lambda chi
  apply OrdinaryIrreducibleCharacter.ext
  intro g
  rfl

/-- The literal action of the tensor-and-field semidirect product on
function-valued ordinary irreducible characters. -/
@[instance_reducible]
def tensorFieldSemidirectAction (field : A →* MulAut G) :
    MulAction
      ((G →* kˣ) ⋊[linearCharacterFieldAction (k := k) field] A)
      (Irr k G) := by
  exact @Formalisation.semidirectMulAction
    (G →* kˣ) A (Irr k G) _ _
    (inverseTensorAction : MulAction (G →* kˣ) (Irr k G))
    (inverseFieldAction field : MulAction A (Irr k G))
    (linearCharacterFieldAction (k := k) field)
    (tensorField_semidirectCompatible field)

/-- Elementwise formula for the combined action. -/
theorem tensorFieldSemidirectAction_apply
    (field : A →* MulAut G)
    (a : (G →* kˣ) ⋊[linearCharacterFieldAction (k := k) field] A)
    (chi : Irr k G) :
    let _ : MulAction
        ((G →* kˣ) ⋊[linearCharacterFieldAction (k := k) field] A)
          (Irr k G) :=
      tensorFieldSemidirectAction (k := k) field
    a • chi = linearTwist (twist k G chi (field a.right⁻¹)) a.left⁻¹ := by
  rfl

end ModularRep.OrdinaryIrreducibleCharacter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
