import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Equivariant maps and fixed points

The manuscript writes its character actions on the right and converts them to left actions by
`a · y = y ^ (a⁻¹)` before using permutation arguments.  The results below formalise the
elementary group-action facts used after that conversion.

They concern only abstract group actions.  In particular, they do not formalise the
representation theoretic construction of any of the actions or bijections in the manuscript.
-/

namespace Formalisation

section RightToLeft

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

/-- Mathlib represents a right action of `G` on `Ω` as a left action of the opposite group
`Gᵐᵒᵖ`.  This function writes that action without introducing a second action notation. -/
def rightAct (y : Ω) (g : G) : Ω :=
  MulOpposite.op g • y

@[simp]
theorem rightAct_one (y : Ω) : rightAct y (1 : G) = y := by
  simp [rightAct]

/-- The opposite-group action has the usual right-action composition law. -/
theorem rightAct_mul (y : Ω) (g h : G) :
    rightAct (rightAct y g) h = rightAct y (g * h) := by
  simpa [rightAct] using (op_smul_op_smul y g h)

/-- Convert a right action to a left action by the manuscript's convention
`g · y = y ^ (g⁻¹)`. -/
def leftActOfRight (g : G) (y : Ω) : Ω :=
  rightAct y g⁻¹

@[simp]
theorem leftActOfRight_one (y : Ω) : leftActOfRight (1 : G) y = y := by
  simp [leftActOfRight]

/-- The converted operation satisfies the multiplication law for a left action. -/
theorem leftActOfRight_mul (g h : G) (y : Ω) :
    leftActOfRight (g * h) y = leftActOfRight g (leftActOfRight h y) := by
  calc
    leftActOfRight (g * h) y = rightAct y (h⁻¹ * g⁻¹) := by
      simp [leftActOfRight, mul_inv_rev]
    _ = rightAct (rightAct y h⁻¹) g⁻¹ := (rightAct_mul y h⁻¹ g⁻¹).symm
    _ = leftActOfRight g (leftActOfRight h y) := rfl

/-- The left `MulAction` obtained from a right action via inverse elements. -/
@[instance_reducible]
def leftMulActionOfRight : MulAction G Ω where
  smul := leftActOfRight
  one_smul := leftActOfRight_one
  mul_smul := leftActOfRight_mul

/-- The subgroup of elements fixing a point for the original right action. -/
def rightStabilizer (y : Ω) : Subgroup G where
  carrier := {g | rightAct y g = y}
  one_mem' := rightAct_one y
  mul_mem' := by
    intro g h hg hh
    change rightAct y (g * h) = y
    change rightAct y g = y at hg
    change rightAct y h = y at hh
    rw [← rightAct_mul, hg, hh]
  inv_mem' := by
    intro g hg
    change rightAct y g = y at hg
    change rightAct y g⁻¹ = y
    calc
      rightAct y g⁻¹ = rightAct (rightAct y g) g⁻¹ := by rw [hg]
      _ = rightAct y (g * g⁻¹) := rightAct_mul y g g⁻¹
      _ = y := by simp

/-- Right equivariance is exactly left equivariance after converting both
actions by inverse elements. -/
theorem rightEquivariant_iff_leftEquivariant
    {Y : Type*} [MulAction Gᵐᵒᵖ Y] (f : Ω → Y) :
    (∀ y g, f (rightAct (G := G) y g) =
      rightAct (G := G) (f y) g) ↔
      ∀ g y, f (leftActOfRight (G := G) g y) =
        leftActOfRight (G := G) g (f y) := by
  constructor
  · intro h g y
    exact h y g⁻¹
  · intro h y g
    simpa [leftActOfRight] using h g⁻¹ y

/-- The stabilizer for the converted left action is the stabilizer for the
original right action. -/
theorem stabilizer_leftMulActionOfRight_eq_rightStabilizer (y : Ω) :
    letI := leftMulActionOfRight (G := G) (Ω := Ω)
    MulAction.stabilizer G y = rightStabilizer y := by
  let _ := leftMulActionOfRight (G := G) (Ω := Ω)
  ext g
  change rightAct y g⁻¹ = y ↔ rightAct y g = y
  constructor
  · intro hg
    have hmem : g⁻¹ ∈ rightStabilizer y := hg
    have hinv : (g⁻¹)⁻¹ ∈ rightStabilizer y :=
      (rightStabilizer y).inv_mem hmem
    change rightAct y (g⁻¹)⁻¹ = y at hinv
    simpa only [inv_inv] using hinv
  · intro hg
    have hmem : g ∈ rightStabilizer y := hg
    have hinv : g⁻¹ ∈ rightStabilizer y :=
      (rightStabilizer y).inv_mem hmem
    change rightAct y g⁻¹ = y at hinv
    exact hinv

end RightToLeft

variable {A X Y : Type*} [Group A] [MulAction A X] [MulAction A Y]

/-- An injective equivariant map reflects as well as preserves fixedness under each group
element. -/
theorem fixed_iff_of_injective_equivariant
    {f : X → Y} (hf : Function.Injective f)
    (hequiv : ∀ (a : A) (x : X), f (a • x) = a • f x)
    (a : A) (x : X) :
    a • x = x ↔ a • f x = f x := by
  constructor
  · intro hx
    calc
      a • f x = f (a • x) := (hequiv a x).symm
      _ = f x := congrArg f hx
  · intro hx
    apply hf
    calc
      f (a • x) = a • f x := hequiv a x
      _ = f x := hx

/-- An injective equivariant map preserves the stabiliser of every point. -/
theorem stabilizer_eq_of_injective_equivariant
    {f : X → Y} (hf : Function.Injective f)
    (hequiv : ∀ (a : A) (x : X), f (a • x) = a • f x)
    (x : X) :
    MulAction.stabilizer A x = MulAction.stabilizer A (f x) := by
  ext a
  simp only [MulAction.mem_stabilizer_iff]
  exact fixed_iff_of_injective_equivariant hf hequiv a x

/-- The inverse of an equivariant equivalence is equivariant. -/
theorem equiv_symm_equivariant
    (e : X ≃ Y) (hequiv : ∀ (a : A) (x : X), e (a • x) = a • e x)
    (a : A) (y : Y) :
    e.symm (a • y) = a • e.symm y := by
  apply e.injective
  simpa using (hequiv a (e.symm y)).symm

/-- An equivariant equivalence restricts to an equivalence between the points fixed by any
subgroup. -/
def fixedPointsEquiv
    (e : X ≃ Y) (hequiv : ∀ (a : A) (x : X), e (a • x) = a • e x)
    (H : Subgroup A) :
    MulAction.fixedPoints H X ≃ MulAction.fixedPoints H Y where
  toFun x := ⟨e x, by
    rw [MulAction.mem_fixedPoints]
    intro h
    calc
      h • e x = e (h • x) := (hequiv h x).symm
      _ = e x := congrArg e ((MulAction.mem_fixedPoints.mp x.property) h)
    ⟩
  invFun y := ⟨e.symm y, by
    rw [MulAction.mem_fixedPoints]
    intro h
    calc
      h • e.symm y = e.symm (h • y) := (equiv_symm_equivariant e hequiv h y).symm
      _ = e.symm y := congrArg e.symm ((MulAction.mem_fixedPoints.mp y.property) h)
    ⟩
  left_inv x := by
    ext
    exact e.symm_apply_apply x
  right_inv y := by
    ext
    exact e.apply_symm_apply y

/-- The algebraic equality underlying independence of a chosen transporter.  If `e` is
equivariant under the stabiliser of `b`, then two group elements that agree on `b` and carry
the chosen inputs to the same point also give the same transported output.  This statement
uses ambient `A`-sets; it does not itself construct a family of bijections between fibres. -/
theorem orbit_transport_well_defined
    {B : Type*} [MulAction A B]
    (b : B) (e : X ≃ Y)
    (hequiv : ∀ (a : A), a ∈ MulAction.stabilizer A b →
      ∀ x : X, e (a • x) = a • e x)
    {g h : A} {x x' : X}
    (hbase : g • b = h • b) (hpoint : g • x = h • x') :
    g • e x = h • e x' := by
  have hk : h⁻¹ * g ∈ MulAction.stabilizer A b := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      (h⁻¹ * g) • b = h⁻¹ • (g • b) := mul_smul h⁻¹ g b
      _ = h⁻¹ • (h • b) := congrArg (fun z ↦ h⁻¹ • z) hbase
      _ = b := by simp
  have hx : (h⁻¹ * g) • x = x' := by
    calc
      (h⁻¹ * g) • x = h⁻¹ • (g • x) := mul_smul h⁻¹ g x
      _ = h⁻¹ • (h • x') := congrArg (fun z ↦ h⁻¹ • z) hpoint
      _ = x' := by simp
  calc
    g • e x = (h * (h⁻¹ * g)) • e x := by simp
    _ = h • ((h⁻¹ * g) • e x) := mul_smul h (h⁻¹ * g) (e x)
    _ = h • e ((h⁻¹ * g) • x) :=
      congrArg (fun y ↦ h • y) (hequiv (h⁻¹ * g) hk x).symm
    _ = h • e x' := congrArg (fun y ↦ h • e y) hx

/-- Consequently, an equivariant equivalence gives equal fixed-point counts for every subgroup
when the acted-on sets are finite. -/
theorem card_fixedPoints_eq_of_equivariant_equiv
    (e : X ≃ Y) (hequiv : ∀ (a : A) (x : X), e (a • x) = a • e x)
    (H : Subgroup A) :
    Nat.card (MulAction.fixedPoints H X) =
      Nat.card (MulAction.fixedPoints H Y) :=
  Nat.card_congr (fixedPointsEquiv e hequiv H)

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
