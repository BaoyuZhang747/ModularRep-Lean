import ModularRep.PaperProofs.TypeBCliffordOrthogonalAction
import ModularRep.PaperProofs.TypeBCliffordScalarNorm

/-!
# The literal Frobenius square for Clifford conjugation

The vector map is coordinatewise prime Frobenius on the same split space.
The square follows from the existing algebra-Frobenius source equations
and the constructed Clifford conjugation action. No orthogonal action or
compatibility theorem is added as an external input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordOrthogonalFieldAction

open TypeBCliffordCarriers TypeBCliffordOrthogonalAction

universe u
variable {n p f : ℕ} {F : Type u} [Field F] [Finite F] [CharP F p]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (S : FieldActionSource n F p f parameters N)

/-- Prime Frobenius on the literal coordinate vector space. -/
def vectorFrobenius (v : Vector n F) : Vector n F := fun i => v i ^ p

/-- The existing field source on the same inverse Clifford element. -/
theorem inverse_clifford_frobenius (g : SpecialClifford n F) :
    toClifford n F ((S.action (fieldGenerator f) g)⁻¹) =
      S.algebraFrobenius (toClifford n F (g⁻¹)) := by
  exact (congrArg (toClifford n F)
    (map_inv (S.action (fieldGenerator f)) g).symm).trans
      (S.action_generator (g⁻¹))

/-- The generator square uses the actual Clifford action and actual
coordinate Frobenius. It is valid before restricting the action to SO. -/
theorem generator_square (g : SpecialClifford n F) (v : Vector n F) :
    linearAction n F (S.action (fieldGenerator f) g)
        (vectorFrobenius (p := p) v) =
      vectorFrobenius (p := p) (linearAction n F g v) := by
  apply iota_injective n F
  calc
    CliffordAlgebra.ι (splitForm n F)
        (linearAction n F (S.action (fieldGenerator f) g)
          (vectorFrobenius (p := p) v)) =
        toClifford n F (S.action (fieldGenerator f) g) *
          CliffordAlgebra.ι (splitForm n F) (vectorFrobenius (p := p) v) *
          toClifford n F ((S.action (fieldGenerator f) g)⁻¹) :=
      iota_action n F _ _
    _ = S.algebraFrobenius (toClifford n F g) *
          S.algebraFrobenius (CliffordAlgebra.ι (splitForm n F) v) *
          S.algebraFrobenius (toClifford n F (g⁻¹)) := by
      rw [S.action_generator, inverse_clifford_frobenius S]
      exact congrArg
        (fun x => S.algebraFrobenius (toClifford n F g) * x *
          S.algebraFrobenius (toClifford n F (g⁻¹))) (S.on_vector v).symm
    _ = S.algebraFrobenius (toClifford n F g *
          CliffordAlgebra.ι (splitForm n F) v * toClifford n F (g⁻¹)) := by
      simp only [map_mul]
    _ = CliffordAlgebra.ι (splitForm n F)
          (vectorFrobenius (p := p) (linearAction n F g v)) :=
      (congrArg S.algebraFrobenius (iota_action n F g v).symm).trans
        (S.on_vector (linearAction n F g v))

/-- The same generator sends each actual scalar to its prescribed field
image. Scalar kernels are preserved, without assuming pointwise fixation. -/
theorem scalar_generator (z : Fˣ) :
    S.action (fieldGenerator f) (TypeBCliffordScalarNorm.scalar n F z) =
      TypeBCliffordScalarNorm.scalar n F (S.scalarAction (fieldGenerator f) z) := by
  apply toClifford_injective n F
  rw [S.action_generator, TypeBCliffordScalarNorm.toClifford_scalar,
    S.on_scalar, TypeBCliffordScalarNorm.toClifford_scalar, S.scalar_generator]

/-- The specified field generator generates every element of the literal
finite cyclic field group; this fixes its exponent without choosing another generator. -/
theorem fieldGenerator_pow_val (f : ℕ) [NeZero f] (e : FieldGroup f) :
    fieldGenerator f ^ e.toAdd.val = e := by
  apply Multiplicative.toAdd.injective
  change e.toAdd.val • (1 : ZMod f) = e.toAdd
  simpa only [nsmul_one] using ZMod.natCast_zmod_val e.toAdd

theorem scalar_generator_pow (a : ℕ) (z : Fˣ) :
    S.action (fieldGenerator f ^ a) (TypeBCliffordScalarNorm.scalar n F z) =
      TypeBCliffordScalarNorm.scalar n F (S.scalarAction (fieldGenerator f ^ a) z) := by
  induction a generalizing z with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, map_mul, map_mul]
    change S.action (fieldGenerator f ^ a)
        (S.action (fieldGenerator f) (TypeBCliffordScalarNorm.scalar n F z)) =
      TypeBCliffordScalarNorm.scalar n F
        (S.scalarAction (fieldGenerator f ^ a) (S.scalarAction (fieldGenerator f) z))
    rw [scalar_generator, ih]

/-- The actual field action preserves scalars through the prescribed scalar
action for every field-group element, not only the prime generator. -/
theorem scalar_natural (e : FieldGroup f) (z : Fˣ) :
    S.action e (TypeBCliffordScalarNorm.scalar n F z) =
      TypeBCliffordScalarNorm.scalar n F (S.scalarAction e z) := by
  letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
  have h := scalar_generator_pow S e.toAdd.val z
  rw [fieldGenerator_pow_val] at h
  exact h

end ModularRep.PaperProofs.TypeBCliffordOrthogonalFieldAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
