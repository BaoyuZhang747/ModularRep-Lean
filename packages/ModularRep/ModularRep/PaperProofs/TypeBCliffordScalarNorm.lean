import ModularRep.PaperProofs.TypeBCliffordOrthogonalAction

/-!
# Scalars and the literal Clifford norm

The scalar embedding is the actual algebra-map unit embedding in the even
vector normalizer. Its centrality and the square formula for NormSource
are deductions on that map, needed for scalar adjustment in Spin -> Omega.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordScalarNorm

open TypeBCliffordCarriers TypeBCliffordOrthogonalAction
open scoped Pointwise

universe u
variable (n : ℕ) (F : Type u) [Field F]

/-- Scalar units in the actual Clifford algebra. -/
def scalarUnit : Fˣ →* (Clifford n F)ˣ :=
  Units.map (algebraMap F (Clifford n F)).toMonoidHom

@[simp] theorem scalarUnit_val (z : Fˣ) :
    (scalarUnit n F z : Clifford n F) = algebraMap F (Clifford n F) (z : F) := rfl

theorem scalarUnit_mem_even (z : Fˣ) : scalarUnit n F z ∈ evenUnits n F := by
  refine ⟨Units.map (algebraMap F (CliffordAlgebra.even (splitForm n F))).toMonoidHom z, ?_⟩
  apply Units.ext
  rfl

theorem scalarUnit_conjugates (z : Fˣ) (x : Clifford n F) :
    ConjAct.toConjAct (scalarUnit n F z) • x = x := by
  change algebraMap F (Clifford n F) (z : F) * x *
    algebraMap F (Clifford n F) ((z⁻¹ : Fˣ) : F) = x
  rw [Algebra.commutes]
  rw [mul_assoc, ← map_mul]
  simp

theorem scalarUnit_mem_normalizer (z : Fˣ) :
    scalarUnit n F z ∈ vectorNormalizer n F := by
  change ConjAct.toConjAct (scalarUnit n F z) • vectorImage n F = vectorImage n F
  ext x
  simp only [Set.mem_smul_set, scalarUnit_conjugates]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/-- The scalar homomorphism lands in the same even-unit normalizer as Spin. -/
def scalar : Fˣ →* SpecialClifford n F :=
  (scalarUnit n F).codRestrict (specialCliffordSubgroup n F)
    (fun z => ⟨scalarUnit_mem_even n F z, scalarUnit_mem_normalizer n F z⟩)

@[simp] theorem toClifford_scalar (z : Fˣ) :
    toClifford n F (scalar n F z) = algebraMap F (Clifford n F) (z : F) := rfl

theorem scalar_injective : Function.Injective (scalar n F) := by
  intro z w h
  apply Units.ext
  exact algebraMap_injective n F (congrArg (toClifford n F) h)

theorem scalar_mem_center (z : Fˣ) :
    scalar n F z ∈ Subgroup.center (SpecialClifford n F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply toClifford_injective n F
  simp only [map_mul, toClifford_scalar]
  exact (Algebra.commutes (z : F) (toClifford n F g)).symm

theorem linearAction_scalar (z : Fˣ) : linearAction n F (scalar n F z) = 1 := by
  apply LinearEquiv.ext
  intro v
  apply iota_injective n F
  rw [iota_action]
  change algebraMap F (Clifford n F) (z : F) *
      CliffordAlgebra.ι (splitForm n F) v *
      toClifford n F ((scalar n F z)⁻¹) =
    CliffordAlgebra.ι (splitForm n F) v
  rw [← map_inv, toClifford_scalar]
  rw [Algebra.commutes, mul_assoc, ← map_mul]
  simp

/-- The source norm is forced to be the square on the literal scalar map. -/
theorem norm_scalar (N : NormSource n F) (z : Fˣ) :
    N.norm (scalar n F z) = z ^ 2 := by
  apply Units.ext
  apply algebraMap_injective n F
  rw [N.value, toClifford_scalar, CliffordAlgebra.reverse.commutes]
  change algebraMap F (Clifford n F) (z : F) *
      algebraMap F (Clifford n F) (z : F) =
    algebraMap F (Clifford n F) ((z ^ 2 : Fˣ) : F)
  rw [pow_two, Units.val_mul, map_mul]

/-- Scalar adjustment of a Clifford lift gives a genuine norm-one element. -/
theorem adjusted_mem_spin (N : NormSource n F) (g : SpecialClifford n F)
    (z : Fˣ) (h : N.norm g = z ^ 2) :
    scalar n F (z⁻¹) * g ∈ SpinSubgroup n F N := by
  change N.norm (scalar n F (z⁻¹) * g) = 1
  rw [map_mul, norm_scalar, h]
  simp

end ModularRep.PaperProofs.TypeBCliffordScalarNorm


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
