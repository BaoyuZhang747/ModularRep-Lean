import ModularRep.FiniteFieldUnitsOdd
import ModularRep.ConformalCharacterFixed
import ModularRep.IrreducibleBrauerCharacter

/-!
# Conformal factorisation over a finite field of characteristic two

This file supplies the finite field specialisations of the abstract
conformal factorisation and class function arguments used in manuscript
Proposition 3.9.  The concrete conformal symplectic group, multiplier, scalar
embedding, and their compatibility identities remain explicit inputs.
-/

namespace ModularRep.ManuscriptVerification.FiniteFieldConformal

variable {C k R : Type*} [Group C] [Field k] [Finite k] [CharP k 2]
  {p : ℕ}

/-- A multiplier with central scalar square lifts over a finite field of
characteristic two factors every element through its kernel and centre. -/
theorem exists_ker_mul_center_of_char_two
    (multiplier : C →* kˣ) (scalar : kˣ → C)
    (multiplier_scalar : ∀ a : kˣ, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : kˣ, scalar a ∈ Subgroup.center C)
    (c : C) :
    ∃ x : multiplier.ker, ∃ z : Subgroup.center C,
      c = (x : C) * (z : C) :=
  ConformalFactorization.exists_ker_mul_center multiplier scalar
    multiplier_scalar scalar_central
    (FiniteFieldUnitsOdd.pow_two_bijective_units_of_char_two k).surjective c

/-- Conjugation by the conformal overgroup is inner on the multiplier kernel
under the finite field hypotheses and the explicit scalar identities. -/
theorem exists_ker_factor_conjNormal_eq_inner_of_char_two
    (multiplier : C →* kˣ) (scalar : kˣ → C)
    (multiplier_scalar : ∀ a : kˣ, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : kˣ, scalar a ∈ Subgroup.center C)
    (c : C) :
    ∃ x : multiplier.ker,
      MulAut.conjNormal (H := multiplier.ker) c = MulAut.conj x :=
  ConformalFactorization.exists_ker_factor_conjNormal_eq_inner multiplier scalar
    multiplier_scalar scalar_central
    (FiniteFieldUnitsOdd.pow_two_bijective_units_of_char_two k).surjective c

/-- Every prime regular class function on the multiplier kernel is fixed by
conformal conjugation under the same finite field and scalar hypotheses. -/
theorem primeRegularClassFunction_fixed_of_char_two
    (multiplier : C →* kˣ) (scalar : kˣ → C)
    (multiplier_scalar : ∀ a : kˣ, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : kˣ, scalar a ∈ Subgroup.center C)
    (f : PrimeRegularClassFunction R multiplier.ker p) (c : C) :
    f.twist (MulAut.conjNormal (H := multiplier.ker) c) = f :=
  ConformalCharacterFixed.primeRegularClassFunction_fixed multiplier scalar
    multiplier_scalar scalar_central
    (FiniteFieldUnitsOdd.pow_two_bijective_units_of_char_two k).surjective f c

end ModularRep.ManuscriptVerification.FiniteFieldConformal

namespace ModularRep.ManuscriptVerification.FiniteFieldConformal

universe u v w x

variable {p : ℕ} {C : Type u} {Fq : Type v} {k : Type w} {K : Type x}
variable [Group C] [Finite C]
variable [Field Fq] [Finite Fq] [CharP Fq 2]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- In characteristic two, the conformal overgroup fixes every
function-valued irreducible Brauer character of the multiplier kernel. -/
theorem irreducibleBrauerCharacter_fixed_of_char_two
    (multiplier : C →* Fqˣ) (scalar : Fqˣ → C)
    (multiplier_scalar : ∀ a : Fqˣ, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : Fqˣ, scalar a ∈ Subgroup.center C)
    (iota : PrimeRegularRootEmbedding p k K multiplier.ker)
    (phi : IBr iota) (c : C) :
    IrreducibleBrauerCharacter.twist iota phi
        (MulAut.conjNormal (H := multiplier.ker) c) = phi := by
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact primeRegularClassFunction_fixed_of_char_two multiplier scalar
    multiplier_scalar scalar_central phi.1 c

/-- The same conformal fixation theorem expressed through the explicit
right action of the automorphism group. -/
theorem op_conjNormal_smul_irreducibleBrauerCharacter_eq_of_char_two
    (multiplier : C →* Fqˣ) (scalar : Fqˣ → C)
    (multiplier_scalar : ∀ a : Fqˣ, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : Fqˣ, scalar a ∈ Subgroup.center C)
    (iota : PrimeRegularRootEmbedding p k K multiplier.ker)
    (phi : IBr iota) (c : C) :
    MulOpposite.op (MulAut.conjNormal (H := multiplier.ker) c) • phi = phi :=
  irreducibleBrauerCharacter_fixed_of_char_two multiplier scalar
    multiplier_scalar scalar_central iota phi c

end ModularRep.ManuscriptVerification.FiniteFieldConformal


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
