import ModularRep.PaperProofs.TypeBCliffordCarriers
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Orthogonal, special orthogonal and derived carriers on the actual split space

The space and quadratic form are exactly `TypeBCliffordCarriers.Vector` and
`splitForm`. The orthogonal group is its subgroup of form-preserving linear
automorphisms; SO is the kernel of the actual determinant homomorphism; Omega
is the commutator subgroup of this SO. Their faithful coordinate matrices,
inclusions, finiteness and normality are constructed without a source input.

No identification with a Clifford quotient is assumed. In the intended odd
field/rank scope, the identification of this derived-SO convention with the
standard orthogonal Omega is the structural source join of Grove Proposition
6.14, pp. 50--51; its spinor-kernel interpretation is Theorem 9.7, p. 77.
Neither equality, nor any covering, character, block or weight statement, is
an input or conclusion here. All definitions themselves make sense over any
field and all ranks.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBOrthogonalOmegaCarriers

open TypeBCliffordCarriers

universe u v

variable (n : ℕ) (F : Type u) [Field F]

/-- The actual linear automorphisms of the fixed coordinate space. -/
abbrev LinearAutomorphism := Vector n F ≃ₗ[F] Vector n F

/-- Form preservation is the membership predicate, rather than a supplied
abstract finite orthogonal group. -/
def orthogonalSubgroup : Subgroup (LinearAutomorphism n F) where
  carrier := {g | ∀ x, splitForm n F (g x) = splitForm n F x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have h := hg (g.symm x)
    exact h.symm.trans (congrArg (splitForm n F) (g.apply_symm_apply x))

abbrev Orthogonal := orthogonalSubgroup n F

@[simp] theorem mem_orthogonalSubgroup (g : LinearAutomorphism n F) :
    g ∈ orthogonalSubgroup n F ↔ ∀ x, splitForm n F (g x) = splitForm n F x := Iff.rfl

def orthogonalToLinear : Orthogonal n F →* LinearAutomorphism n F :=
  (orthogonalSubgroup n F).subtype

@[simp] theorem orthogonalToLinear_apply (g : Orthogonal n F) :
    orthogonalToLinear n F g = g.val := rfl

theorem orthogonalToLinear_injective : Function.Injective (orthogonalToLinear n F) :=
  Subtype.val_injective

theorem preserves_splitForm (g : Orthogonal n F) (x : Vector n F) :
    splitForm n F (orthogonalToLinear n F g x) = splitForm n F x := g.property x

@[ext] theorem orthogonal_ext {g h : Orthogonal n F}
    (heq : ∀ x : Vector n F, orthogonalToLinear n F g x = orthogonalToLinear n F h x) :
    g = h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  exact heq

/-- Restrict an already constructed linear action using its proved form
preservation. The actual target subgroup and underlying map stay fixed. -/
def liftToOrthogonal {D : Type v} [Group D]
    (a : D →* LinearAutomorphism n F)
    (preserves : ∀ g x, splitForm n F (a g x) = splitForm n F x) :
    D →* Orthogonal n F :=
  a.codRestrict (orthogonalSubgroup n F) preserves

@[simp] theorem liftToOrthogonal_value {D : Type v} [Group D]
    (a : D →* LinearAutomorphism n F)
    (preserves : ∀ g x, splitForm n F (a g x) = splitForm n F x) (g : D) :
    orthogonalToLinear n F (liftToOrthogonal n F a preserves g) = a g := rfl

/-- The actual determinant in the units of the specified field. -/
def determinant : Orthogonal n F →* Fˣ :=
  (LinearEquiv.det : LinearAutomorphism n F →* Fˣ).comp (orthogonalToLinear n F)

@[simp] theorem determinant_value (g : Orthogonal n F) :
    determinant n F g = LinearEquiv.det (orthogonalToLinear n F g) := rfl

/-- SO is literally the determinant-one kernel inside this orthogonal group. -/
def specialOrthogonalSubgroup : Subgroup (Orthogonal n F) := (determinant n F).ker

abbrev SpecialOrthogonal := specialOrthogonalSubgroup n F

instance specialOrthogonal_normal : (specialOrthogonalSubgroup n F).Normal :=
  inferInstanceAs (determinant n F).ker.Normal

@[simp] theorem mem_specialOrthogonalSubgroup (g : Orthogonal n F) :
    g ∈ specialOrthogonalSubgroup n F ↔ determinant n F g = 1 := Iff.rfl

def specialOrthogonalToOrthogonal : SpecialOrthogonal n F →* Orthogonal n F :=
  (specialOrthogonalSubgroup n F).subtype

def specialOrthogonalToLinear : SpecialOrthogonal n F →* LinearAutomorphism n F :=
  (orthogonalToLinear n F).comp (specialOrthogonalToOrthogonal n F)

theorem specialOrthogonalToOrthogonal_injective :
    Function.Injective (specialOrthogonalToOrthogonal n F) := Subtype.val_injective

theorem specialOrthogonalToLinear_injective :
    Function.Injective (specialOrthogonalToLinear n F) :=
  (orthogonalToLinear_injective n F).comp (specialOrthogonalToOrthogonal_injective n F)

@[simp] theorem specialOrthogonal_determinant (g : SpecialOrthogonal n F) :
    determinant n F (specialOrthogonalToOrthogonal n F g) = 1 := g.property

theorem specialOrthogonal_preserves (g : SpecialOrthogonal n F) (x : Vector n F) :
    splitForm n F (specialOrthogonalToLinear n F g x) = splitForm n F x :=
  preserves_splitForm n F (specialOrthogonalToOrthogonal n F g) x

def liftToSpecialOrthogonal {D : Type v} [Group D]
    (a : D →* Orthogonal n F) (det_one : ∀ g, determinant n F (a g) = 1) :
    D →* SpecialOrthogonal n F :=
  a.codRestrict (specialOrthogonalSubgroup n F) det_one

@[simp] theorem liftToSpecialOrthogonal_value {D : Type v} [Group D]
    (a : D →* Orthogonal n F) (det_one : ∀ g, determinant n F (a g) = 1) (g : D) :
    specialOrthogonalToOrthogonal n F (liftToSpecialOrthogonal n F a det_one g) = a g := rfl

/-- The derived subgroup of the actual SO carrier. Its identification with
other standard presentations of Omega is kept separate. -/
def omegaSubgroup : Subgroup (SpecialOrthogonal n F) :=
  _root_.commutator (SpecialOrthogonal n F)

abbrev Omega := omegaSubgroup n F

instance omega_normal : (omegaSubgroup n F).Normal :=
  inferInstanceAs (_root_.commutator (SpecialOrthogonal n F)).Normal

instance omega_characteristic : (omegaSubgroup n F).Characteristic :=
  inferInstanceAs (_root_.commutator (SpecialOrthogonal n F)).Characteristic

def omegaToSpecialOrthogonal : Omega n F →* SpecialOrthogonal n F :=
  (omegaSubgroup n F).subtype

def omegaToOrthogonal : Omega n F →* Orthogonal n F :=
  (specialOrthogonalToOrthogonal n F).comp (omegaToSpecialOrthogonal n F)

def omegaToLinear : Omega n F →* LinearAutomorphism n F :=
  (orthogonalToLinear n F).comp (omegaToOrthogonal n F)

theorem omegaToSpecialOrthogonal_injective :
    Function.Injective (omegaToSpecialOrthogonal n F) := Subtype.val_injective

theorem omegaToOrthogonal_injective : Function.Injective (omegaToOrthogonal n F) :=
  (specialOrthogonalToOrthogonal_injective n F).comp (omegaToSpecialOrthogonal_injective n F)

theorem omegaToLinear_injective : Function.Injective (omegaToLinear n F) :=
  (orthogonalToLinear_injective n F).comp (omegaToOrthogonal_injective n F)

@[simp] theorem omega_determinant (g : Omega n F) :
    determinant n F (omegaToOrthogonal n F g) = 1 := g.val.property

theorem omega_preserves (g : Omega n F) (x : Vector n F) :
    splitForm n F (omegaToLinear n F g x) = splitForm n F x :=
  preserves_splitForm n F (omegaToOrthogonal n F g) x

/-- The same Omega as an actual subgroup of O, rather than a new carrier. -/
def omegaImage : Subgroup (Orthogonal n F) :=
  (omegaSubgroup n F).map (specialOrthogonalToOrthogonal n F)

theorem omegaImage_eq_commutator : omegaImage n F =
    ⁅specialOrthogonalSubgroup n F, specialOrthogonalSubgroup n F⁆ :=
  Subgroup.map_subtype_commutator (specialOrthogonalSubgroup n F)

instance omegaImage_normal : (omegaImage n F).Normal := by
  rw [omegaImage_eq_commutator]
  infer_instance

theorem omegaImage_le_specialOrthogonal :
    omegaImage n F ≤ specialOrthogonalSubgroup n F := by
  rw [omegaImage_eq_commutator]
  exact Subgroup.commutator_le_self _

def omegaImageEquiv : Omega n F ≃* omegaImage n F :=
  (omegaSubgroup n F).equivMapOfInjective (specialOrthogonalToOrthogonal n F)
    (specialOrthogonalToOrthogonal_injective n F)

@[simp] theorem omegaImageEquiv_value (g : Omega n F) :
    (omegaImageEquiv n F g : Orthogonal n F) = omegaToOrthogonal n F g := rfl

section Coordinates

/-- The actual coordinate matrix of the linear action, as a monoid map. -/
def matrixHom : Orthogonal n F →* Matrix (Coordinate n) (Coordinate n) F :=
  (LinearMap.toMatrixAlgEquiv'.toMonoidHom).comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (orthogonalToLinear n F))

@[simp] theorem matrixHom_entry (g : Orthogonal n F) (i j : Coordinate n) :
    matrixHom n F g i j = orthogonalToLinear n F g (Pi.single j 1) i := rfl

theorem matrixHom_mulVec (g : Orthogonal n F) (x : Vector n F) :
    (matrixHom n F g).mulVec x = orthogonalToLinear n F g x :=
  LinearMap.toMatrix'_mulVec (orthogonalToLinear n F g).toLinearMap x

theorem matrixHom_injective : Function.Injective (matrixHom n F) := by
  intro g h heq
  apply orthogonal_ext n F
  intro x
  exact (matrixHom_mulVec n F g x).symm.trans
    ((congrArg (fun m : Matrix (Coordinate n) (Coordinate n) F => m.mulVec x) heq).trans
      (matrixHom_mulVec n F h x))

theorem matrixHom_det (g : Orthogonal n F) :
    Matrix.det (matrixHom n F g) = (determinant n F g : F) := by
  calc
    Matrix.det (matrixHom n F g) =
        LinearMap.det (orthogonalToLinear n F g).toLinearMap :=
      LinearMap.det_toMatrix' (orthogonalToLinear n F g).toLinearMap
    _ = (determinant n F g : F) := (LinearEquiv.coe_det _).symm

def specialOrthogonalMatrixHom : SpecialOrthogonal n F →*
    Matrix (Coordinate n) (Coordinate n) F :=
  (matrixHom n F).comp (specialOrthogonalToOrthogonal n F)

def omegaMatrixHom : Omega n F →* Matrix (Coordinate n) (Coordinate n) F :=
  (matrixHom n F).comp (omegaToOrthogonal n F)

theorem specialOrthogonalMatrixHom_injective :
    Function.Injective (specialOrthogonalMatrixHom n F) :=
  (matrixHom_injective n F).comp (specialOrthogonalToOrthogonal_injective n F)

theorem omegaMatrixHom_injective : Function.Injective (omegaMatrixHom n F) :=
  (matrixHom_injective n F).comp (omegaToOrthogonal_injective n F)

@[simp] theorem specialOrthogonalMatrixHom_det (g : SpecialOrthogonal n F) :
    Matrix.det (specialOrthogonalMatrixHom n F g) = 1 := by
  change Matrix.det (matrixHom n F (specialOrthogonalToOrthogonal n F g)) = 1
  rw [matrixHom_det, specialOrthogonal_determinant]
  rfl

@[simp] theorem omegaMatrixHom_det (g : Omega n F) :
    Matrix.det (omegaMatrixHom n F g) = 1 := by
  change Matrix.det (matrixHom n F (omegaToOrthogonal n F g)) = 1
  rw [matrixHom_det, omega_determinant]
  rfl

theorem coordinate_card : Fintype.card (Coordinate n) = 2 * n + 1 := by
  simp [Coordinate, two_mul, add_comm]

theorem vector_finrank : Module.finrank F (Vector n F) = 2 * n + 1 := by
  rw [Module.finrank_fintype_fun_eq_card]
  exact coordinate_card n

end Coordinates

section Finite

variable [Finite F]

/-- Finiteness follows from the actual finite coordinate space, without a
separate orthogonal-group finiteness certificate. -/
instance orthogonal_finite : Finite (Orthogonal n F) :=
  Finite.of_injective
    (fun g : Orthogonal n F => (fun x : Vector n F => orthogonalToLinear n F g x))
    (by intro g h heq; exact orthogonal_ext n F (congrFun heq))

instance specialOrthogonal_finite : Finite (SpecialOrthogonal n F) :=
  Finite.of_injective (specialOrthogonalToOrthogonal n F)
    (specialOrthogonalToOrthogonal_injective n F)

instance omega_finite : Finite (Omega n F) :=
  Finite.of_injective (omegaToOrthogonal n F) (omegaToOrthogonal_injective n F)

end Finite

end ModularRep.PaperProofs.TypeBOrthogonalOmegaCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
