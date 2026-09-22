import ModularRep.PaperProofs.TypeBConformalDualCarriers
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Literal centralizer carriers for a later algebraic isotypy interpretation

The full centralizer, its multiplier-one subgroup and their inclusion are
actual subgroups of the prescribed conformal symplectic group. Over an
algebraically closed defining field, extracting a square root of a multiplier
expresses every full-centralizer element as an actual scalar times an element
of the multiplier-one subgroup.

These are group/field deductions only. In particular, scalar decomposition
does not assert connectedness, reductivity, algebraicity, an algebraic isotypy,
an equality of finite commutator subgroups, or any unipotent character theorem.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCSpCentralizerIsotypyCarriers

open TypeBConformalDualCarriers

universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- The actual full conformal centralizer, without a semisimplicity assumption. -/
def fullCentralizer (s : CSp F n) : Subgroup (CSp F n) :=
  Subgroup.centralizer ({s} : Set (CSp F n))

/-- The restriction of the same ambient multiplier. -/
def restrictedMultiplier (s : CSp F n) : fullCentralizer s →* Fˣ :=
  (multiplier F n).comp (fullCentralizer s).subtype

@[simp] theorem restrictedMultiplier_value (s : CSp F n) (c : fullCentralizer s) :
    restrictedMultiplier s c = multiplier F n c.val := rfl

/-- The multiplier-one centralizer as a subgroup of the full centralizer. -/
def symplecticCentralizer (s : CSp F n) : Subgroup (fullCentralizer s) :=
  (restrictedMultiplier s).ker

@[simp] theorem mem_symplecticCentralizer (s : CSp F n) (c : fullCentralizer s) :
    c ∈ symplecticCentralizer s ↔ restrictedMultiplier s c = 1 := Iff.rfl

/-- The literal subgroup inclusion; no independently chosen map is supplied. -/
def inclusion (s : CSp F n) : symplecticCentralizer s →* fullCentralizer s :=
  (symplecticCentralizer s).subtype

@[simp] theorem inclusion_value (s : CSp F n) (h : symplecticCentralizer s) :
    (inclusion s h).val = h.val.val := rfl

theorem inclusion_injective (s : CSp F n) : Function.Injective (inclusion s) :=
  Subtype.val_injective

@[simp] theorem restrictedMultiplier_inclusion (s : CSp F n)
    (h : symplecticCentralizer s) : restrictedMultiplier s (inclusion s h) = 1 :=
  h.property

/-- Every actual ambient scalar centralizes the specified element. -/
def scalarCentralizer (s : CSp F n) : Fˣ →* fullCentralizer s where
  toFun z := ⟨scalar F n z,
    Subgroup.mem_centralizer_singleton_iff.mpr (scalar_commute F n z s)⟩
  map_one' := Subtype.ext (map_one (scalar F n))
  map_mul' z t := Subtype.ext (map_mul (scalar F n) z t)

@[simp] theorem scalarCentralizer_value (s : CSp F n) (z : Fˣ) :
    (scalarCentralizer s z).val = scalar F n z := rfl

@[simp] theorem restrictedMultiplier_scalar (s : CSp F n) (z : Fˣ) :
    restrictedMultiplier s (scalarCentralizer s z) = z ^ 2 := rfl

theorem scalarCentralizer_commute (s : CSp F n) (z : Fˣ)
    (c : fullCentralizer s) : scalarCentralizer s z * c = c * scalarCentralizer s z := by
  apply Subtype.ext
  exact scalar_commute F n z c.val

theorem scalarCentralizer_central (s : CSp F n) (z : Fˣ) :
    scalarCentralizer s z ∈ Subgroup.center (fullCentralizer s) := by
  apply Subgroup.mem_center_iff.mpr
  intro c
  exact (scalarCentralizer_commute s z c).symm

/-- Remove an actual scalar square root of the multiplier. -/
def scalarAdjustment (s : CSp F n) (c : fullCentralizer s) (z : Fˣ)
    (hz : z ^ 2 = restrictedMultiplier s c) : symplecticCentralizer s :=
  ⟨(scalarCentralizer s z)⁻¹ * c, by
    change restrictedMultiplier s ((scalarCentralizer s z)⁻¹ * c) = 1
    rw [map_mul, map_inv, restrictedMultiplier_scalar, hz, inv_mul_cancel]⟩

@[simp] theorem scalarAdjustment_inclusion (s : CSp F n) (c : fullCentralizer s)
    (z : Fˣ) (hz : z ^ 2 = restrictedMultiplier s c) :
    inclusion s (scalarAdjustment s c z hz) = (scalarCentralizer s z)⁻¹ * c := rfl

@[simp] theorem scalarAdjustment_value (s : CSp F n) (c : fullCentralizer s)
    (z : Fˣ) (hz : z ^ 2 = restrictedMultiplier s c) :
    (scalarAdjustment s c z hz).val.val = (scalar F n z)⁻¹ * c.val := rfl

theorem scalar_mul_adjustment (s : CSp F n) (c : fullCentralizer s)
    (z : Fˣ) (hz : z ^ 2 = restrictedMultiplier s c) :
    scalarCentralizer s z * inclusion s (scalarAdjustment s c z hz) = c := by
  rw [scalarAdjustment_inclusion]
  simp

/-- Scalar decomposition on algebraically closed defining-field points.
This does not assert any algebraic-group structure on the point carriers. -/
theorem exists_scalar_decomposition [IsAlgClosed F] (s : CSp F n)
    (c : fullCentralizer s) :
    ∃ (z : Fˣ) (h : symplecticCentralizer s),
      z ^ 2 = restrictedMultiplier s c ∧ c = scalarCentralizer s z * inclusion s h := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq
    ((restrictedMultiplier s c : Fˣ) : F) (n := 2) zero_lt_two
  have ha0 : a ≠ 0 := by
    intro hzero
    apply (restrictedMultiplier s c).ne_zero
    rw [← ha, hzero, zero_pow (by decide : 2 ≠ 0)]
  let z : Fˣ := Units.mk0 a ha0
  have hz : z ^ 2 = restrictedMultiplier s c := by
    apply Units.ext
    change a ^ 2 = ((restrictedMultiplier s c : Fˣ) : F)
    exact ha
  exact ⟨z, scalarAdjustment s c z hz, hz, (scalar_mul_adjustment s c z hz).symm⟩

end ModularRep.PaperProofs.TypeBCSpCentralizerIsotypyCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
