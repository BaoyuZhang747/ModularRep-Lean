import ModularRep.LinearCharacterTensorAction
import ModularRep.GroupAlgebraCentralFunctions

/-! Coefficient twisting on the actual group algebra and its action on a
representation. An involutive linear character gives an automorphism of
the centre, with no assertion about scalar action on a whole block. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLinearCharacterAlgebra

variable {k G : Type*} [Field k] [Group G]

def weightedGroupHom (lambda : G →* kˣ) : G →* k[G] where
  toFun g := MonoidAlgebra.single g (lambda g : k)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' g h := by simp [MonoidAlgebra.single_mul_single]

def algebraTwist (lambda : G →* kˣ) : k[G] →ₐ[k] k[G] :=
  MonoidAlgebra.lift k k[G] G (weightedGroupHom lambda)

@[simp]
theorem algebraTwist_single (lambda : G →* kˣ) (g : G) (a : k) :
    algebraTwist lambda (MonoidAlgebra.single g a) =
      MonoidAlgebra.single g (a * (lambda g : k)) := by
  simp [algebraTwist, weightedGroupHom, MonoidAlgebra.smul_single, smul_eq_mul]

theorem algebraTwist_coeff (lambda : G →* kˣ) (x : k[G]) (g : G) :
    (algebraTwist lambda x).coeff g = x.coeff g * (lambda g : k) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul]
  | single h a =>
      by_cases hh : h = g
      · subst h; simp
      · simp [MonoidAlgebra.coeff_single, hh]

theorem algebraTwist_involutive (lambda : G →* kˣ)
    (hsquare : ∀ g, (lambda g : k) * (lambda g : k) = 1) :
    Function.Involutive (algebraTwist lambda) := by
  intro x
  ext g
  rw [algebraTwist_coeff, algebraTwist_coeff, mul_assoc, hsquare, mul_one]

def algebraTwistEquiv (lambda : G →* kˣ)
    (hsquare : ∀ g, (lambda g : k) * (lambda g : k) = 1) :
    k[G] ≃ₐ[k] k[G] :=
  AlgEquiv.ofBijective (algebraTwist lambda)
    (algebraTwist_involutive lambda hsquare).bijective

def centerTwist (lambda : G →* kˣ)
    (hsquare : ∀ g, (lambda g : k) * (lambda g : k) = 1) :
    ModularRep.GroupAlgebraCenter k G ≃ₐ[k] ModularRep.GroupAlgebraCenter k G where
  toRingEquiv := Subsemiring.centerCongr (algebraTwistEquiv lambda hsquare).toRingEquiv
  commutes' a := by
    apply Subtype.ext
    exact (algebraTwistEquiv lambda hsquare).commutes a

@[simp]
theorem centerTwist_coe (lambda : G →* kˣ)
    (hsquare : ∀ g, (lambda g : k) * (lambda g : k) = 1)
    (z : ModularRep.GroupAlgebraCenter k G) :
    (centerTwist lambda hsquare z : k[G]) = algebraTwist lambda (z : k[G]) :=
  rfl

theorem twisted_algebra_action
    {V : Type*} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (lambda : G →* kˣ) (x : k[G]) :
    (rho.linearCharacterTwist lambda).asAlgebraHom x =
      rho.asAlgebraHom (algebraTwist lambda x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g a =>
      rw [algebraTwist_single]
      simp only [Representation.asAlgebraHom_single]
      change a • ((lambda g : k) • rho g) = (a * (lambda g : k)) • rho g
      exact (mul_smul a (lambda g : k) (rho g)).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLinearCharacterAlgebra


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
