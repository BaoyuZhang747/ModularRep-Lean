import ModularRep.PaperProofs.TypeBCliffordOrthogonalFieldBinding
import ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientQuotient

/-!
# The full field action on the literal Spin/Omega quotient

The transported action on SO has the independently constructed coordinate
prime Frobenius as its distinguished generator. Restriction to the actual
characteristic commutator subgroup supplies its full Omega action. The
Spin projection and the existing Spin-centre quotient actor commute with
these actions for every element of the same cyclic field group.

All compatibility statements are deductions from the previously fixed
projection and field sources; no compatibility source is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordOrthogonalFullFieldBinding

open TypeBCliffordCarriers TypeBCliffordOrthogonalSourceBinding
open TypeBOrthogonalOmegaCarriers TypeBOrthogonalFieldAutomorphism
open TypeBCliffordOrthogonalAmbientQuotient

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (S : FieldActionSource n F p f parameters N) (rank : 3 ≤ n)
  (C : Source n F p f parameters rank N)

/-- Surjectivity of the same projection identifies its transported field
generator with the independently constructed coordinate Frobenius. -/
theorem soFieldAction_generator :
    soFieldAction n F parameters rank N C S (fieldGenerator f) =
      primeFrobeniusSpecialOrthogonal n F p parameters.prime := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := C.onto x
  exact (projection_field n F parameters rank N C S (fieldGenerator f) g).symm.trans
    (TypeBCliffordOrthogonalFieldBinding.projection_field_generator S rank C g)

/-- Every field-group element has its fixed canonical exponent, so the
entire transported SO action is expressed by powers of prime Frobenius. -/
theorem soFieldAction_eq_prime_pow (e : FieldGroup f) :
    soFieldAction n F parameters rank N C S e =
      primeFrobeniusSpecialOrthogonal n F p parameters.prime ^ e.toAdd.val := by
  letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
  calc
    soFieldAction n F parameters rank N C S e =
        soFieldAction n F parameters rank N C S (fieldGenerator f ^ e.toAdd.val) :=
      congrArg (soFieldAction n F parameters rank N C S)
        (TypeBCliffordOrthogonalFieldAction.fieldGenerator_pow_val f e).symm
    _ = _ := by rw [map_pow, soFieldAction_generator]

/-- The full action restricts to Omega because this literal subgroup is
the commutator of the actual SO carrier and hence characteristic. -/
def omegaFieldAction : FieldGroup f →* MulAut (Omega n F) :=
  (MulAut.characteristic (omegaSubgroup n F)).comp
    (soFieldAction n F parameters rank N C S)

@[simp] theorem omegaFieldAction_value (e : FieldGroup f) (x : Omega n F) :
    omegaToSpecialOrthogonal n F (omegaFieldAction S rank C e x) =
      soFieldAction n F parameters rank N C S e (omegaToSpecialOrthogonal n F x) := rfl

theorem omegaFieldAction_generator :
    omegaFieldAction S rank C (fieldGenerator f) =
      primeFrobeniusOmega n F p parameters.prime := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change soFieldAction n F parameters rank N C S (fieldGenerator f) x.val =
    primeFrobeniusSpecialOrthogonal n F p parameters.prime x.val
  exact congrArg (fun a : MulAut (SpecialOrthogonal n F) => a x.val)
    (soFieldAction_generator S rank C)

theorem omegaFieldAction_eq_prime_pow (e : FieldGroup f) :
    omegaFieldAction S rank C e =
      primeFrobeniusOmega n F p parameters.prime ^ e.toAdd.val := by
  letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
  calc
    omegaFieldAction S rank C e =
        omegaFieldAction S rank C (fieldGenerator f ^ e.toAdd.val) :=
      congrArg (omegaFieldAction S rank C)
        (TypeBCliffordOrthogonalFieldAction.fieldGenerator_pow_val f e).symm
    _ = _ := by rw [map_pow, omegaFieldAction_generator]

/-- The restriction of the actual projection commutes with every field
element; the norm-one and derived-SO carriers are the original subgroups. -/
theorem spinProjection_field (e : FieldGroup f) (g : Spin n F N) :
    spinProjection n F parameters rank N C (spinFieldAction n F S e g) =
      omegaFieldAction S rank C e (spinProjection n F parameters rank N C g) := by
  apply Subtype.ext
  change projection n F C.det_one (S.action e g.val) =
    soFieldAction n F parameters rank N C S e (projection n F C.det_one g.val)
  exact projection_field n F parameters rank N C S e g.val

theorem matrixOmegaEquiv_field_mk
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (e : FieldGroup f) (g : Spin n F N) :
    matrixOmegaEquiv n F N parameters rank C centre
        (QuotientGroup.mk' (Subgroup.center (Spin n F N)) (spinFieldAction n F S e g)) =
      omegaFieldAction S rank C e
        (matrixOmegaEquiv n F N parameters rank C centre
          (QuotientGroup.mk' (Subgroup.center (Spin n F N)) g)) :=
  spinProjection_field S rank C e g

/-- The all-element square retains the existing literal A/P actor; no
new field actor is chosen on the old Spin/Z quotient. -/
theorem matrixOmegaEquiv_field_action
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (e : FieldGroup f) (x : TypeBSpinCoverSource.Omega N) :
    matrixOmegaEquiv n F N parameters rank C centre
        (TypeBCentralKernelSpinBinding.omegaAction S
          (TypeBCentralKernelCarriers.qA (TypeBCentralKernelSpinBinding.P S)
            (SemidirectProduct.inr e)) x) =
      omegaFieldAction S rank C e
        (matrixOmegaEquiv n F N parameters rank C centre x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Spin n F N)) x
  rw [TypeBCentralKernelSpinBinding.omegaAction_mk,
    TypeBAutomorphismSource.ambientAutomorphism_inr]
  exact matrixOmegaEquiv_field_mk S rank C centre e g

/-- The same all-element square written directly in terms of the
independently constructed prime matrix Frobenius and the canonical exponent. -/
theorem matrixOmegaEquiv_field_action_prime_pow
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (e : FieldGroup f) (x : TypeBSpinCoverSource.Omega N) :
    matrixOmegaEquiv n F N parameters rank C centre
        (TypeBCentralKernelSpinBinding.omegaAction S
          (TypeBCentralKernelCarriers.qA (TypeBCentralKernelSpinBinding.P S)
            (SemidirectProduct.inr e)) x) =
      (primeFrobeniusOmega n F p parameters.prime ^ e.toAdd.val)
        (matrixOmegaEquiv n F N parameters rank C centre x) := by
  rw [matrixOmegaEquiv_field_action S rank C centre, omegaFieldAction_eq_prime_pow]

end ModularRep.PaperProofs.TypeBCliffordOrthogonalFullFieldBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
