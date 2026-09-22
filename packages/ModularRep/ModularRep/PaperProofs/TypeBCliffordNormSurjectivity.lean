import ModularRep.PaperProofs.TypeBCliffordScalarNorm

/-!
# Surjectivity of the actual split Clifford norm

For `n ≥ 1`, the displayed split form represents every nonzero scalar on
its first hyperbolic plane. A product of the corresponding Clifford vector
with the zeroth coordinate vector is an actual even unit normalizing the
literal vector image, and its reversal norm is the prescribed scalar.

All membership and norm statements are deductions from Clifford identities.
There is no centre, quotient, automorphism, or norm-surjectivity source.
The construction works over every field; the finite odd-field application,
including q=3, is a specialization. We do not identify the normalizer with
Mathlib's generated Spin or Lipschitz groups.
-/

noncomputable section
set_option autoImplicit false

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBCliffordNormSurjectivity

open TypeBCliffordCarriers TypeBCliffordOrthogonalAction

universe u
variable (n : ℕ) (F : Type u) [Field F]

/-- A nonisotropic vector is an actual unit, with its explicit inverse. -/
def vectorUnit (v : Vector n F) (hv : splitForm n F v ≠ 0) :
    (Clifford n F)ˣ where
  val := CliffordAlgebra.ι (splitForm n F) v
  inv := (splitForm n F v)⁻¹ • CliffordAlgebra.ι (splitForm n F) v
  val_inv := by
    rw [mul_smul_comm, CliffordAlgebra.ι_sq_scalar, Algebra.smul_def,
      ← map_mul, inv_mul_cancel₀ hv, map_one]
  inv_val := by
    rw [smul_mul_assoc, CliffordAlgebra.ι_sq_scalar, Algebra.smul_def,
      ← map_mul, inv_mul_cancel₀ hv, map_one]

@[simp] theorem vectorUnit_val (v : Vector n F) (hv : splitForm n F v ≠ 0) :
    (vectorUnit n F v hv : Clifford n F) =
      CliffordAlgebra.ι (splitForm n F) v := rfl

@[simp] theorem vectorUnit_inv_val (v : Vector n F) (hv : splitForm n F v ≠ 0) :
    (((vectorUnit n F v hv)⁻¹ : (Clifford n F)ˣ) : Clifford n F) =
      (splitForm n F v)⁻¹ • CliffordAlgebra.ι (splitForm n F) v := rfl

/-- Forward conjugation is the literal polar-form vector expression. -/
theorem vectorUnit_conjugates (v : Vector n F) (hv : splitForm n F v ≠ 0)
    (w : Vector n F) :
    ConjAct.toConjAct (vectorUnit n F v hv) •
        CliffordAlgebra.ι (splitForm n F) w =
      CliffordAlgebra.ι (splitForm n F)
        ((splitForm n F v)⁻¹ •
          (QuadraticMap.polar (splitForm n F) v w • v - splitForm n F v • w)) := by
  change (CliffordAlgebra.ι (splitForm n F) v *
      CliffordAlgebra.ι (splitForm n F) w) *
        ((splitForm n F v)⁻¹ • CliffordAlgebra.ι (splitForm n F) v) = _
  rw [mul_smul_comm, CliffordAlgebra.ι_mul_ι_mul_ι, ← map_smul]

/-- Inverse conjugation has the same vector expression. -/
theorem vectorUnit_inverse_conjugates (v : Vector n F)
    (hv : splitForm n F v ≠ 0) (w : Vector n F) :
    ConjAct.toConjAct ((vectorUnit n F v hv)⁻¹) •
        CliffordAlgebra.ι (splitForm n F) w =
      CliffordAlgebra.ι (splitForm n F)
        ((splitForm n F v)⁻¹ •
          (QuadraticMap.polar (splitForm n F) v w • v - splitForm n F v • w)) := by
  change (((splitForm n F v)⁻¹ • CliffordAlgebra.ι (splitForm n F) v) *
      CliffordAlgebra.ι (splitForm n F) w) *
        CliffordAlgebra.ι (splitForm n F) v = _
  rw [smul_mul_assoc, smul_mul_assoc, CliffordAlgebra.ι_mul_ι_mul_ι, ← map_smul]

theorem vectorUnit_mem_normalizer (v : Vector n F) (hv : splitForm n F v ≠ 0) :
    vectorUnit n F v hv ∈ vectorNormalizer n F := by
  change ConjAct.toConjAct (vectorUnit n F v hv) • vectorImage n F = vectorImage n F
  ext x
  constructor
  · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
    exact ⟨_, (vectorUnit_conjugates n F v hv w).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨ConjAct.toConjAct ((vectorUnit n F v hv)⁻¹) •
      CliffordAlgebra.ι (splitForm n F) w, ?_, ?_⟩
    · exact ⟨_, (vectorUnit_inverse_conjugates n F v hv w).symm⟩
    · simp

/-- The product and its inverse lie in the actual even subalgebra. -/
theorem vectorPair_mem_even (v w : Vector n F)
    (hv : splitForm n F v ≠ 0) (hw : splitForm n F w ≠ 0) :
    vectorUnit n F v hv * vectorUnit n F w hw ∈ evenUnits n F := by
  let z := vectorUnit n F v hv * vectorUnit n F w hw
  have hval : (z : Clifford n F) ∈ CliffordAlgebra.even (splitForm n F) :=
    CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (splitForm n F) v w
  have hinv : ((z⁻¹ : (Clifford n F)ˣ) : Clifford n F) ∈
      CliffordAlgebra.even (splitForm n F) := by
    change ((splitForm n F w)⁻¹ • CliffordAlgebra.ι (splitForm n F) w) *
      ((splitForm n F v)⁻¹ • CliffordAlgebra.ι (splitForm n F) v) ∈ _
    rw [smul_mul_assoc, mul_smul_comm]
    exact (CliffordAlgebra.even (splitForm n F)).smul_mem
      ((CliffordAlgebra.even (splitForm n F)).smul_mem
        (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (splitForm n F) w v) _) _
  let e : (CliffordAlgebra.even (splitForm n F))ˣ :=
    { val := ⟨(z : Clifford n F), hval⟩
      inv := ⟨((z⁻¹ : (Clifford n F)ˣ) : Clifford n F), hinv⟩
      val_inv := Subtype.ext z.val_inv
      inv_val := Subtype.ext z.inv_val }
  refine ⟨e, ?_⟩
  apply Units.ext
  rfl

/-- An actual even vector-normalizing unit, not a generated-group alias. -/
def vectorPair (v w : Vector n F)
    (hv : splitForm n F v ≠ 0) (hw : splitForm n F w ≠ 0) :
    SpecialClifford n F :=
  ⟨vectorUnit n F v hv * vectorUnit n F w hw,
    vectorPair_mem_even n F v w hv hw,
    (vectorNormalizer n F).mul_mem
      (vectorUnit_mem_normalizer n F v hv) (vectorUnit_mem_normalizer n F w hw)⟩

@[simp] theorem toClifford_vectorPair (v w : Vector n F)
    (hv : splitForm n F v ≠ 0) (hw : splitForm n F w ≠ 0) :
    toClifford n F (vectorPair n F v w hv hw) =
      CliffordAlgebra.ι (splitForm n F) v *
        CliffordAlgebra.ι (splitForm n F) w := rfl

/-- The reversal product computes the norm on the actual constructed pair. -/
theorem vectorPair_reverse_product (v w : Vector n F)
    (hv : splitForm n F v ≠ 0) (hw : splitForm n F w ≠ 0) :
    toClifford n F (vectorPair n F v w hv hw) *
        CliffordAlgebra.reverse (toClifford n F (vectorPair n F v w hv hw)) =
      algebraMap F (Clifford n F) (splitForm n F v * splitForm n F w) := by
  rw [toClifford_vectorPair, CliffordAlgebra.reverse.map_mul,
    CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse_ι]
  calc
    (CliffordAlgebra.ι (splitForm n F) v * CliffordAlgebra.ι (splitForm n F) w) *
        (CliffordAlgebra.ι (splitForm n F) w * CliffordAlgebra.ι (splitForm n F) v) =
      CliffordAlgebra.ι (splitForm n F) v *
        (CliffordAlgebra.ι (splitForm n F) w * CliffordAlgebra.ι (splitForm n F) w) *
        CliffordAlgebra.ι (splitForm n F) v := by simp only [mul_assoc]
    _ = algebraMap F (Clifford n F) (splitForm n F w) *
        (CliffordAlgebra.ι (splitForm n F) v * CliffordAlgebra.ι (splitForm n F) v) := by
      rw [CliffordAlgebra.ι_sq_scalar, ← Algebra.commutes]
      rw [mul_assoc]
    _ = algebraMap F (Clifford n F) (splitForm n F v * splitForm n F w) := by
      rw [CliffordAlgebra.ι_sq_scalar, ← map_mul, mul_comm]

theorem norm_vectorPair (N : NormSource n F) (v w : Vector n F)
    (hv : splitForm n F v ≠ 0) (hw : splitForm n F w ≠ 0) :
    (N.norm (vectorPair n F v w hv hw) : F) =
      splitForm n F v * splitForm n F w := by
  apply algebraMap_injective n F
  rw [N.value, vectorPair_reverse_product]

/-- The zeroth coordinate vector has norm one. -/
def axisVector : Vector n F
  | none => 1
  | some _ => 0

@[simp] theorem splitForm_axisVector : splitForm n F (axisVector n F) = 1 := by
  simp [splitForm_apply, axisVector]

/-- The first chosen hyperbolic plane represents the prescribed scalar. -/
def hyperbolicVector (i : Fin n) (a : F) : Vector n F
  | none => 0
  | some (Sum.inl j) => if j = i then 1 else 0
  | some (Sum.inr j) => if j = i then a else 0

@[simp] theorem splitForm_hyperbolicVector (i : Fin n) (a : F) :
    splitForm n F (hyperbolicVector n F i a) = a := by
  simp [splitForm_apply, hyperbolicVector, ite_mul, mul_ite]

/-- A prescribed unit has a concrete preimage in the actual carrier. -/
def normPreimage (hn : 1 ≤ n) (a : Fˣ) : SpecialClifford n F :=
  vectorPair n F (axisVector n F)
    (hyperbolicVector n F ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩ (a : F))
    (by rw [splitForm_axisVector]; exact one_ne_zero)
    (by simpa only [splitForm_hyperbolicVector] using a.ne_zero)

@[simp] theorem norm_normPreimage (hn : 1 ≤ n) (N : NormSource n F) (a : Fˣ) :
    N.norm (normPreimage n F hn a) = a := by
  apply Units.ext
  simp only [normPreimage, norm_vectorPair, splitForm_axisVector,
    splitForm_hyperbolicVector, one_mul]

/-- Surjectivity is derived from the defining reversal norm, not assumed. -/
theorem norm_surjective (hn : 1 ≤ n) (N : NormSource n F) :
    Function.Surjective N.norm :=
  fun a => ⟨normPreimage n F hn a, norm_normPreimage n F hn N a⟩

end ModularRep.PaperProofs.TypeBCliffordNormSurjectivity


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
