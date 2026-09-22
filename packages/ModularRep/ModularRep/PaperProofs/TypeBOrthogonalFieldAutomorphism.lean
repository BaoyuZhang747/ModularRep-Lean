import ModularRep.PaperProofs.TypeBOrthogonalOmegaCarriers
import Mathlib.FieldTheory.Perfect

/-!
# Actual coordinate field automorphisms of O, SO and Omega

A field automorphism acts on the fixed coordinate space semilinearly.
Conjugation yields the actual linear-group automorphism, and preservation
of the displayed split form restricts it to O. The determinant transforms
by the same field automorphism, so its literal kernel SO is preserved.
The actual derived subgroup Omega is characteristic in SO. No field-action
compatibility, norm, covering, character or weight source is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBOrthogonalFieldAutomorphism

open TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers

universe u
variable (n : ℕ) (F : Type u) [Field F]

local instance coordinateInversePair (sigma : F ≃+* F) :
    RingHomInvPair sigma.toRingHom sigma.symm.toRingHom where
  comp_eq := by
    ext x
    exact sigma.symm_apply_apply x
  comp_eq₂ := by
    ext x
    exact sigma.apply_symm_apply x

/-- Coordinatewise application of the same field automorphism. -/
def coordinateEquiv (sigma : F ≃+* F) : Vector n F ≃+* Vector n F :=
  RingEquiv.piCongrRight (fun _ : Coordinate n => sigma)

@[simp] theorem coordinateEquiv_apply (sigma : F ≃+* F) (v : Vector n F) (i : Coordinate n) :
    coordinateEquiv n F sigma v i = sigma (v i) := rfl

@[simp] theorem coordinateEquiv_symm (sigma : F ≃+* F) :
    (coordinateEquiv n F sigma).symm = coordinateEquiv n F sigma.symm := rfl

def coordinateSemilinear (sigma : F ≃+* F) :
    LinearEquiv (σ' := sigma.symm.toRingHom) sigma.toRingHom (Vector n F) (Vector n F) where
  __ := (coordinateEquiv n F sigma).toAddEquiv
  map_smul' c v := by
    ext i
    exact sigma.map_mul c (v i)

@[simp] theorem coordinateSemilinear_apply (sigma : F ≃+* F) (v : Vector n F) :
    (coordinateSemilinear n F sigma).toFun v = coordinateEquiv n F sigma v := rfl

theorem splitForm_coordinateEquiv (sigma : F ≃+* F) (v : Vector n F) :
    splitForm n F (coordinateEquiv n F sigma v) = sigma (splitForm n F v) := by
  simp only [splitForm_apply, coordinateEquiv_apply, map_add, map_mul, map_sum]

/-- Semilinear conjugation is already implemented for the actual general
linear group. The two outer equivalences retain our linear-automorphism carrier. -/
def linearAutomorphism (sigma : F ≃+* F) : MulAut (LinearAutomorphism n F) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Vector n F)).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv
      (σ₁₂ := sigma.toRingHom) (σ₂₁ := sigma.symm.toRingHom)
      (coordinateSemilinear n F sigma)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Vector n F)))

theorem linearAutomorphism_apply (sigma : F ≃+* F) (g : LinearAutomorphism n F)
    (v : Vector n F) :
    linearAutomorphism n F sigma g v =
      coordinateEquiv n F sigma (g ((coordinateEquiv n F sigma).symm v)) := rfl

theorem linearAutomorphism_square (sigma : F ≃+* F) (g : LinearAutomorphism n F)
    (v : Vector n F) :
    linearAutomorphism n F sigma g (coordinateEquiv n F sigma v) =
      coordinateEquiv n F sigma (g v) := by
  rw [linearAutomorphism_apply, RingEquiv.symm_apply_apply]

@[simp] theorem linearAutomorphism_symm (sigma : F ≃+* F) :
    (linearAutomorphism n F sigma).symm = linearAutomorphism n F sigma.symm := rfl

theorem linearAutomorphism_preserves (sigma : F ≃+* F) (g : Orthogonal n F)
    (v : Vector n F) :
    splitForm n F (linearAutomorphism n F sigma g.val v) = splitForm n F v := by
  calc
    splitForm n F (linearAutomorphism n F sigma g.val v) =
        sigma (splitForm n F (g.val ((coordinateEquiv n F sigma).symm v))) :=
      (congrArg (splitForm n F) (linearAutomorphism_apply n F sigma g.val v)).trans
        (splitForm_coordinateEquiv n F sigma _)
    _ = sigma (splitForm n F ((coordinateEquiv n F sigma).symm v)) :=
      congrArg sigma (g.property _)
    _ = sigma (sigma.symm (splitForm n F v)) :=
      congrArg sigma (splitForm_coordinateEquiv n F sigma.symm v)
    _ = splitForm n F v := sigma.apply_symm_apply _

def orthogonalAutomorphism (sigma : F ≃+* F) : MulAut (Orthogonal n F) where
  toFun g := ⟨linearAutomorphism n F sigma g.val, linearAutomorphism_preserves n F sigma g⟩
  invFun g := ⟨linearAutomorphism n F sigma.symm g.val,
    linearAutomorphism_preserves n F sigma.symm g⟩
  left_inv g := by
    apply Subtype.ext
    exact (linearAutomorphism n F sigma).symm_apply_apply g.val
  right_inv g := by
    apply Subtype.ext
    exact (linearAutomorphism n F sigma).apply_symm_apply g.val
  map_mul' g h := Subtype.ext ((linearAutomorphism n F sigma).map_mul g.val h.val)

@[simp] theorem orthogonalAutomorphism_toLinear (sigma : F ≃+* F) (g : Orthogonal n F) :
    orthogonalToLinear n F (orthogonalAutomorphism n F sigma g) =
      linearAutomorphism n F sigma (orthogonalToLinear n F g) := rfl

@[simp] theorem orthogonalAutomorphism_symm (sigma : F ≃+* F) :
    (orthogonalAutomorphism n F sigma).symm = orthogonalAutomorphism n F sigma.symm := rfl

theorem coordinateEquiv_basis (sigma : F ≃+* F) (j : Coordinate n) :
    coordinateEquiv n F sigma (Pi.single j 1) = Pi.single j 1 := by
  ext i
  by_cases h : j = i
  · subst i
    simp
  · simp [Pi.single_apply, h]

/-- The semilinear conjugation sends the actual matrix to its coefficientwise
field image; the coordinate basis is fixed. -/
theorem matrixHom_orthogonalAutomorphism (sigma : F ≃+* F) (g : Orthogonal n F) :
    matrixHom n F (orthogonalAutomorphism n F sigma g) = sigma.mapMatrix (matrixHom n F g) := by
  ext i j
  change linearAutomorphism n F sigma g.val (Pi.single j 1) i =
    sigma (g.val (Pi.single j 1) i)
  have h := congrFun (linearAutomorphism_apply n F sigma g.val (Pi.single j 1)) i
  have hb : (coordinateEquiv n F sigma).symm (Pi.single j 1) = Pi.single j 1 :=
    coordinateEquiv_basis n F sigma.symm j
  exact h.trans (congrArg (fun v : Vector n F => sigma (g.val v i)) hb)

/-- The determinant square is proved from the actual coordinate matrices. -/
theorem determinant_orthogonalAutomorphism (sigma : F ≃+* F) (g : Orthogonal n F) :
    determinant n F (orthogonalAutomorphism n F sigma g) =
      Units.map sigma.toRingHom.toMonoidHom (determinant n F g) := by
  apply Units.ext
  change (determinant n F (orthogonalAutomorphism n F sigma g) : F) =
    sigma (determinant n F g : F)
  calc
    (determinant n F (orthogonalAutomorphism n F sigma g) : F) =
        Matrix.det (matrixHom n F (orthogonalAutomorphism n F sigma g)) :=
      (matrixHom_det n F _).symm
    _ = Matrix.det (sigma.mapMatrix (matrixHom n F g)) :=
      congrArg Matrix.det (matrixHom_orthogonalAutomorphism n F sigma g)
    _ = sigma (Matrix.det (matrixHom n F g)) := (sigma.map_det _).symm
    _ = sigma (determinant n F g : F) := congrArg sigma (matrixHom_det n F g)

theorem orthogonalAutomorphism_det_one (sigma : F ≃+* F) (g : SpecialOrthogonal n F) :
    determinant n F (orthogonalAutomorphism n F sigma g.val) = 1 := by
  rw [determinant_orthogonalAutomorphism, show determinant n F g.val = 1 from g.property,
    map_one]

def specialOrthogonalAutomorphism (sigma : F ≃+* F) : MulAut (SpecialOrthogonal n F) where
  toFun g := ⟨orthogonalAutomorphism n F sigma g.val,
    orthogonalAutomorphism_det_one n F sigma g⟩
  invFun g := ⟨orthogonalAutomorphism n F sigma.symm g.val,
    orthogonalAutomorphism_det_one n F sigma.symm g⟩
  left_inv g := Subtype.ext ((orthogonalAutomorphism n F sigma).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((orthogonalAutomorphism n F sigma).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((orthogonalAutomorphism n F sigma).map_mul g.val h.val)

@[simp] theorem specialOrthogonalAutomorphism_value (sigma : F ≃+* F)
    (g : SpecialOrthogonal n F) :
    specialOrthogonalToOrthogonal n F (specialOrthogonalAutomorphism n F sigma g) =
      orthogonalAutomorphism n F sigma (specialOrthogonalToOrthogonal n F g) := rfl

/-- No Omega stability source is needed: this literal Omega is characteristic. -/
def omegaAutomorphism (sigma : F ≃+* F) : MulAut (Omega n F) :=
  MulAut.characteristic (omegaSubgroup n F) (specialOrthogonalAutomorphism n F sigma)

@[simp] theorem omegaAutomorphism_value (sigma : F ≃+* F) (g : Omega n F) :
    omegaToSpecialOrthogonal n F (omegaAutomorphism n F sigma g) =
      specialOrthogonalAutomorphism n F sigma (omegaToSpecialOrthogonal n F g) := rfl

theorem specialOrthogonalAutomorphism_square (sigma : F ≃+* F)
    (g : SpecialOrthogonal n F) (v : Vector n F) :
    specialOrthogonalToLinear n F (specialOrthogonalAutomorphism n F sigma g)
        (coordinateEquiv n F sigma v) =
      coordinateEquiv n F sigma (specialOrthogonalToLinear n F g v) :=
  linearAutomorphism_square n F sigma (specialOrthogonalToLinear n F g) v

theorem omegaAutomorphism_square (sigma : F ≃+* F) (g : Omega n F) (v : Vector n F) :
    omegaToLinear n F (omegaAutomorphism n F sigma g) (coordinateEquiv n F sigma v) =
      coordinateEquiv n F sigma (omegaToLinear n F g v) :=
  linearAutomorphism_square n F sigma (omegaToLinear n F g) v

section PrimeFrobenius

variable (p : ℕ) [Finite F] [CharP F p]

/-- The prime guard and the characteristic of the actual finite field are explicit. -/
def primeFrobeniusOrthogonal (hp : p.Prime) : MulAut (Orthogonal n F) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact orthogonalAutomorphism n F (frobeniusEquiv F p)

def primeFrobeniusSpecialOrthogonal (hp : p.Prime) : MulAut (SpecialOrthogonal n F) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact specialOrthogonalAutomorphism n F (frobeniusEquiv F p)

def primeFrobeniusOmega (hp : p.Prime) : MulAut (Omega n F) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact omegaAutomorphism n F (frobeniusEquiv F p)

theorem primeFrobeniusSpecialOrthogonal_square (hp : p.Prime)
    (g : SpecialOrthogonal n F) (v : Vector n F) :
    specialOrthogonalToLinear n F (primeFrobeniusSpecialOrthogonal n F p hp g)
        (fun i => v i ^ p) =
      (fun i => (specialOrthogonalToLinear n F g v i) ^ p) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact specialOrthogonalAutomorphism_square n F (frobeniusEquiv F p) g v

theorem primeFrobeniusOmega_square (hp : p.Prime) (g : Omega n F) (v : Vector n F) :
    omegaToLinear n F (primeFrobeniusOmega n F p hp g) (fun i => v i ^ p) =
      (fun i => (omegaToLinear n F g v i) ^ p) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact omegaAutomorphism_square n F (frobeniusEquiv F p) g v

end PrimeFrobenius

end ModularRep.PaperProofs.TypeBOrthogonalFieldAutomorphism


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
