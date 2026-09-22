import ModularRep.PaperProofs.TypeBConformalDualCarriers
import ModularRep.PaperProofs.TypeBCliffordCarriers
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Coordinate field actions on the actual CSp and PCSp carriers

A field automorphism acts semilinearly on the fixed two-block symplectic
space. Conjugation transports its actual linear maps and the multiplier is
sent through that same field automorphism. Actual scalars are preserved,
so the action descends to the quotient by the full scalar subgroup.

The canonical cyclic action uses prime Frobenius and the finite-field
cardinality equation. All constructions here are K deductions. FLZ §3.1,
pp.541–542, identifies these finite groups with the corresponding dual
rational-point groups; that identification and rational-series naturality
are separate source statements. No rational-index or character action is
defined or assumed in this file.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace ModularRep.PaperProofs.TypeBConformalDualFieldAction

open TypeBConformalDualCarriers TypeBCliffordCarriers

universe u
variable (F : Type u) [Field F] (n : ℕ)

local instance coordinateInversePair (sigma : F ≃+* F) :
    RingHomInvPair sigma.toRingHom sigma.symm.toRingHom where
  comp_eq := by
    ext x
    exact sigma.symm_apply_apply x
  comp_eq₂ := by
    ext x
    exact sigma.apply_symm_apply x

/-- Entrywise application of the same field automorphism in both blocks. -/
def coordinateEquiv (sigma : F ≃+* F) :
    SymplecticSpace F n ≃+* SymplecticSpace F n :=
  RingEquiv.prodCongr (RingEquiv.piCongrRight fun _ : Fin n => sigma)
    (RingEquiv.piCongrRight fun _ : Fin n => sigma)

theorem coordinateEquiv_apply (sigma : F ≃+* F) (v : SymplecticSpace F n) :
    coordinateEquiv F n sigma v =
      ((fun i => sigma (v.1 i)), (fun i => sigma (v.2 i))) := rfl

@[simp] theorem coordinateEquiv_symm (sigma : F ≃+* F) :
    (coordinateEquiv F n sigma).symm = coordinateEquiv F n sigma.symm := rfl

theorem coordinateEquiv_smul (sigma : F ≃+* F) (a : F)
    (v : SymplecticSpace F n) :
    coordinateEquiv F n sigma (a • v) = sigma a • coordinateEquiv F n sigma v := by
  apply Prod.ext
  · funext i
    exact sigma.map_mul a (v.1 i)
  · funext i
    exact sigma.map_mul a (v.2 i)

theorem coordinateEquiv_mul (sigma tau : RingAut F) :
    coordinateEquiv F n (sigma * tau) =
      coordinateEquiv F n sigma * coordinateEquiv F n tau := by
  apply RingEquiv.ext
  intro v
  rfl

/-- The coordinate equivalence with its literal semilinear scalar law. -/
def coordinateSemilinear (sigma : F ≃+* F) :
    LinearEquiv (σ' := sigma.symm.toRingHom) sigma.toRingHom
      (SymplecticSpace F n) (SymplecticSpace F n) where
  __ := (coordinateEquiv F n sigma).toAddEquiv
  map_smul' := coordinateEquiv_smul F n sigma

theorem symplecticForm_coordinateEquiv (sigma : F ≃+* F)
    (v w : SymplecticSpace F n) :
    symplecticForm F n (coordinateEquiv F n sigma v) (coordinateEquiv F n sigma w) =
      sigma (symplecticForm F n v w) := by
  simp only [symplecticForm, coordinateEquiv_apply, map_sum, map_sub, map_mul]

/-- Existing semilinear conjugation on the actual general linear group. -/
def linearAutomorphism (sigma : F ≃+* F) :
    MulAut (SymplecticSpace F n ≃ₗ[F] SymplecticSpace F n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (SymplecticSpace F n)).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv
      (σ₁₂ := sigma.toRingHom) (σ₂₁ := sigma.symm.toRingHom)
      (coordinateSemilinear F n sigma)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (SymplecticSpace F n)))

theorem linearAutomorphism_apply (sigma : F ≃+* F)
    (g : SymplecticSpace F n ≃ₗ[F] SymplecticSpace F n) (v : SymplecticSpace F n) :
    linearAutomorphism F n sigma g v =
      coordinateEquiv F n sigma (g ((coordinateEquiv F n sigma).symm v)) := rfl

theorem linearAutomorphism_square (sigma : F ≃+* F)
    (g : SymplecticSpace F n ≃ₗ[F] SymplecticSpace F n) (v : SymplecticSpace F n) :
    linearAutomorphism F n sigma g (coordinateEquiv F n sigma v) =
      coordinateEquiv F n sigma (g v) := by
  rw [linearAutomorphism_apply, RingEquiv.symm_apply_apply]

@[simp] theorem linearAutomorphism_symm (sigma : F ≃+* F) :
    (linearAutomorphism F n sigma).symm = linearAutomorphism F n sigma.symm := rfl

theorem linearAutomorphism_preserves (sigma : F ≃+* F) (g : CSp F n)
    (v w : SymplecticSpace F n) :
    symplecticForm F n (linearAutomorphism F n sigma g.val.1 v)
      (linearAutomorphism F n sigma g.val.1 w) =
        sigma (g.val.2 : F) * symplecticForm F n v w := by
  rw [linearAutomorphism_apply, linearAutomorphism_apply, symplecticForm_coordinateEquiv]
  rw [g.property, map_mul, coordinateEquiv_symm, symplecticForm_coordinateEquiv]
  rw [RingEquiv.apply_symm_apply]

/-- Actual coordinate transport of a conformal map and its unit multiplier. -/
def cspAutomorphism (sigma : F ≃+* F) : MulAut (CSp F n) where
  toFun g := ⟨(linearAutomorphism F n sigma g.val.1,
    Units.mapEquiv sigma.toMulEquiv g.val.2), linearAutomorphism_preserves F n sigma g⟩
  invFun g := ⟨(linearAutomorphism F n sigma.symm g.val.1,
    Units.mapEquiv sigma.symm.toMulEquiv g.val.2),
    linearAutomorphism_preserves F n sigma.symm g⟩
  left_inv g := by
    apply Subtype.ext
    apply Prod.ext
    · exact (linearAutomorphism F n sigma).symm_apply_apply g.val.1
    · exact (Units.mapEquiv sigma.toMulEquiv).symm_apply_apply g.val.2
  right_inv g := by
    apply Subtype.ext
    apply Prod.ext
    · exact (linearAutomorphism F n sigma).apply_symm_apply g.val.1
    · exact (Units.mapEquiv sigma.toMulEquiv).apply_symm_apply g.val.2
  map_mul' g h := by
    apply Subtype.ext
    apply Prod.ext
    · exact (linearAutomorphism F n sigma).map_mul g.val.1 h.val.1
    · exact (Units.mapEquiv sigma.toMulEquiv).map_mul g.val.2 h.val.2

@[simp] theorem multiplier_cspAutomorphism (sigma : F ≃+* F) (g : CSp F n) :
    multiplier F n (cspAutomorphism F n sigma g) =
      Units.mapEquiv sigma.toMulEquiv (multiplier F n g) := rfl

theorem cspAutomorphism_linearPart (sigma : F ≃+* F) (g : CSp F n) :
    linearPart F n (cspAutomorphism F n sigma g) =
      linearAutomorphism F n sigma (linearPart F n g) := rfl

theorem cspAutomorphism_square (sigma : F ≃+* F) (g : CSp F n)
    (v : SymplecticSpace F n) :
    linearPart F n (cspAutomorphism F n sigma g) (coordinateEquiv F n sigma v) =
      coordinateEquiv F n sigma (linearPart F n g v) :=
  linearAutomorphism_square F n sigma (linearPart F n g) v

@[simp] theorem cspAutomorphism_scalar (sigma : F ≃+* F) (z : Fˣ) :
    cspAutomorphism F n sigma (TypeBConformalDualCarriers.scalar F n z) =
      TypeBConformalDualCarriers.scalar F n (Units.mapEquiv sigma.toMulEquiv z) := by
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro v
    change coordinateEquiv F n sigma ((z : F) • (coordinateEquiv F n sigma).symm v) =
      sigma (z : F) • v
    rw [coordinateEquiv_smul, RingEquiv.apply_symm_apply]
  · exact map_pow (Units.mapEquiv sigma.toMulEquiv) z 2

/-- Scalar preservation is proved on the whole actual subgroup. -/
theorem scalarSubgroup_map (sigma : F ≃+* F) :
    (scalarSubgroup F n).map (cspAutomorphism F n sigma).toMonoidHom =
      scalarSubgroup F n := by
  apply le_antisymm
  · rintro _ ⟨g, ⟨z, rfl⟩, rfl⟩
    change cspAutomorphism F n sigma (TypeBConformalDualCarriers.scalar F n z) ∈
      scalarSubgroup F n
    rw [cspAutomorphism_scalar]
    exact ⟨_, rfl⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨TypeBConformalDualCarriers.scalar F n
      ((Units.mapEquiv sigma.toMulEquiv).symm z), ⟨_, rfl⟩, ?_⟩
    change cspAutomorphism F n sigma (TypeBConformalDualCarriers.scalar F n
      ((Units.mapEquiv sigma.toMulEquiv).symm z)) = TypeBConformalDualCarriers.scalar F n z
    rw [cspAutomorphism_scalar, MulEquiv.apply_symm_apply]

/-- Quotient descent by the full scalar subgroup; no PSp substitution. -/
def pcspAutomorphism (sigma : F ≃+* F) : MulAut (PCSp F n) :=
  QuotientGroup.congr (scalarSubgroup F n) (scalarSubgroup F n)
    (cspAutomorphism F n sigma) (scalarSubgroup_map F n sigma)

@[simp] theorem pcspAutomorphism_mk (sigma : F ≃+* F) (g : CSp F n) :
    pcspAutomorphism F n sigma (QuotientGroup.mk' (scalarSubgroup F n) g) =
      QuotientGroup.mk' (scalarSubgroup F n) (cspAutomorphism F n sigma g) := rfl

theorem cspAutomorphism_one : cspAutomorphism F n (1 : RingAut F) = 1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro v
    rfl
  · apply Units.ext
    rfl

theorem cspAutomorphism_mul (sigma tau : RingAut F) :
    cspAutomorphism F n (sigma * tau) =
      cspAutomorphism F n sigma * cspAutomorphism F n tau := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro v
    change coordinateEquiv F n (sigma * tau)
        (g.val.1 ((coordinateEquiv F n (sigma * tau)).symm v)) =
      coordinateEquiv F n sigma (coordinateEquiv F n tau
        (g.val.1 ((coordinateEquiv F n tau).symm ((coordinateEquiv F n sigma).symm v))))
    rw [coordinateEquiv_mul]
    rfl
  · apply Units.ext
    rfl

def cspAutomorphismHom : RingAut F →* MulAut (CSp F n) where
  toFun := cspAutomorphism F n
  map_one' := cspAutomorphism_one F n
  map_mul' := cspAutomorphism_mul F n

def pcspAutomorphismHom : RingAut F →* MulAut (PCSp F n) where
  toFun := pcspAutomorphism F n
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup F n) x
    rw [pcspAutomorphism_mk, cspAutomorphism_one]
    rfl
  map_mul' sigma tau := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup F n) x
    change pcspAutomorphism F n (sigma * tau) (QuotientGroup.mk' _ g) =
      pcspAutomorphism F n sigma (pcspAutomorphism F n tau (QuotientGroup.mk' _ g))
    rw [pcspAutomorphism_mk, pcspAutomorphism_mk, pcspAutomorphism_mk, cspAutomorphism_mul]
    rfl

section FiniteField

variable [Finite F] {p f : ℕ} [CharP F p]

/-- Canonical prime Frobenius in the defining field. -/
def primeFieldAutomorphism (hp : p.Prime) : RingAut F := by
  letI : Fact p.Prime := ⟨hp⟩
  exact frobeniusEquiv F p

@[simp] theorem primeFieldAutomorphism_apply (hp : p.Prime) (x : F) :
    primeFieldAutomorphism F hp x = x ^ p := rfl

/-- The field cardinality proves the required cyclic exponent. -/
theorem primeFieldAutomorphism_pow (parameters : OddFieldParameters F p f) :
    primeFieldAutomorphism F parameters.prime ^ f = 1 := by
  letI : Fact p.Prime := ⟨parameters.prime⟩
  letI : Fintype F := Fintype.ofFinite F
  apply RingEquiv.ext
  intro x
  change (frobeniusEquiv F p ^ f) x = x
  rw [← iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_def]
  have card : Fintype.card F = p ^ f := by
    simpa only [Nat.card_eq_fintype_card] using parameters.cardinality
  rw [← card]
  exact FiniteField.pow_card x

/-- Integer Frobenius powers descend through the actual modulus f. -/
def fieldPowerAddHom (parameters : OddFieldParameters F p f) :
    ZMod f →+ Additive (RingAut F) :=
  ZMod.lift f ⟨zmultiplesHom _ (Additive.ofMul (primeFieldAutomorphism F parameters.prime)), by
    change (f : ℤ) • Additive.ofMul (primeFieldAutomorphism F parameters.prime) = 0
    rw [natCast_zsmul]
    change Additive.ofMul (primeFieldAutomorphism F parameters.prime ^ f) = 0
    rw [primeFieldAutomorphism_pow F parameters]
    rfl⟩

/-- The genuine finite cyclic field action, with positive prime Frobenius. -/
def fieldAutomorphism (parameters : OddFieldParameters F p f) :
    FieldGroup f →* RingAut F :=
  AddMonoidHom.toMultiplicativeLeft (fieldPowerAddHom F parameters)

theorem fieldAutomorphism_natCast (parameters : OddFieldParameters F p f) (a : ℕ) :
    fieldAutomorphism F parameters (Multiplicative.ofAdd (a : ZMod f)) =
      primeFieldAutomorphism F parameters.prime ^ a := by
  change (fieldPowerAddHom F parameters (a : ZMod f)).toMul = _
  rw [show (a : ZMod f) = ((a : ℤ) : ZMod f) by simp]
  unfold fieldPowerAddHom
  rw [ZMod.lift_coe]
  change ((a : ℤ) • Additive.ofMul (primeFieldAutomorphism F parameters.prime)).toMul = _
  rw [natCast_zsmul]
  rfl

@[simp] theorem fieldAutomorphism_generator (parameters : OddFieldParameters F p f) :
    fieldAutomorphism F parameters (fieldGenerator f) =
      primeFieldAutomorphism F parameters.prime := by
  simpa only [fieldGenerator, Nat.cast_one, pow_one] using
    fieldAutomorphism_natCast F parameters 1

def primeFrobeniusCSp (hp : p.Prime) : MulAut (CSp F n) :=
  cspAutomorphism F n (primeFieldAutomorphism F hp)

def primeFrobeniusPCSp (hp : p.Prime) : MulAut (PCSp F n) :=
  pcspAutomorphism F n (primeFieldAutomorphism F hp)

def cspFieldAction (parameters : OddFieldParameters F p f) :
    FieldGroup f →* MulAut (CSp F n) :=
  (cspAutomorphismHom F n).comp (fieldAutomorphism F parameters)

def pcspFieldAction (parameters : OddFieldParameters F p f) :
    FieldGroup f →* MulAut (PCSp F n) :=
  (pcspAutomorphismHom F n).comp (fieldAutomorphism F parameters)

theorem cspFieldAction_apply (parameters : OddFieldParameters F p f)
    (e : FieldGroup f) (g : CSp F n) :
    cspFieldAction F n parameters e g =
      cspAutomorphism F n (fieldAutomorphism F parameters e) g := rfl

theorem pcspFieldAction_apply (parameters : OddFieldParameters F p f)
    (e : FieldGroup f) (g : PCSp F n) :
    pcspFieldAction F n parameters e g =
      pcspAutomorphism F n (fieldAutomorphism F parameters e) g := rfl

@[simp] theorem cspFieldAction_generator (parameters : OddFieldParameters F p f) :
    cspFieldAction F n parameters (fieldGenerator f) =
      primeFrobeniusCSp F n parameters.prime := by
  change cspAutomorphism F n (fieldAutomorphism F parameters (fieldGenerator f)) = _
  rw [fieldAutomorphism_generator]
  rfl

@[simp] theorem pcspFieldAction_generator (parameters : OddFieldParameters F p f) :
    pcspFieldAction F n parameters (fieldGenerator f) =
      primeFrobeniusPCSp F n parameters.prime := by
  change pcspAutomorphism F n (fieldAutomorphism F parameters (fieldGenerator f)) = _
  rw [fieldAutomorphism_generator]
  rfl

@[simp] theorem pcspFieldAction_mk (parameters : OddFieldParameters F p f)
    (e : FieldGroup f) (g : CSp F n) :
    pcspFieldAction F n parameters e (QuotientGroup.mk' (scalarSubgroup F n) g) =
      QuotientGroup.mk' (scalarSubgroup F n) (cspFieldAction F n parameters e g) := rfl

theorem cspFieldAction_scalar (parameters : OddFieldParameters F p f)
    (e : FieldGroup f) (z : Fˣ) :
    cspFieldAction F n parameters e (TypeBConformalDualCarriers.scalar F n z) =
      TypeBConformalDualCarriers.scalar F n
        (Units.mapEquiv (fieldAutomorphism F parameters e).toMulEquiv z) :=
  cspAutomorphism_scalar F n (fieldAutomorphism F parameters e) z

end FiniteField

end ModularRep.PaperProofs.TypeBConformalDualFieldAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
