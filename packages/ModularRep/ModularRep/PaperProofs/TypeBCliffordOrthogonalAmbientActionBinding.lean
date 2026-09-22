import ModularRep.PaperProofs.TypeBCliffordOrthogonalFullFieldBinding
import ModularRep.PaperProofs.TypeBCliffordOrthogonalResidualQuotient

/-!
# The literal SO/field action and the residual Clifford quotient

The target ambient acts by its actual field action followed by SO
conjugation. The same Spin-to-Omega equivalence intertwines this action with
the existing action of the Clifford ambient modulo the Spin centre.
Residual scalars fix Omega and centralize its actual embedded image;
they are not asserted to be the centre of the entire ambient group.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientActionBinding

open TypeBCliffordCarriers TypeBCliffordOrthogonalSourceBinding
open TypeBOrthogonalOmegaCarriers TypeBCliffordOrthogonalAmbientQuotient
open TypeBCliffordOrthogonalFullFieldBinding TypeBCliffordOrthogonalResidualQuotient

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (S : FieldActionSource n F p f parameters N) (rank : 3 ≤ n)
  (C : Source n F p f parameters rank N)

/-- The actual semidirect action on SO is conjugation in the SO coordinate
and the already constructed full field action in the other coordinate. -/
def soAmbientAction : OrthogonalAmbient n F parameters rank N C S →*
    MulAut (SpecialOrthogonal n F) :=
  SemidirectProduct.lift MulAut.conj (soFieldAction n F parameters rank N C S) (by
    intro e
    apply MonoidHom.ext
    intro g
    apply MulEquiv.ext
    intro x
    change soFieldAction n F parameters rank N C S e g * x *
        (soFieldAction n F parameters rank N C S e g)⁻¹ =
      soFieldAction n F parameters rank N C S e
        (g * (soFieldAction n F parameters rank N C S e)⁻¹ x * g⁻¹)
    simp only [map_mul, map_inv, MulAut.apply_inv_self])

@[simp] theorem soAmbientAction_value
    (a : OrthogonalAmbient n F parameters rank N C S) (x : SpecialOrthogonal n F) :
    soAmbientAction S rank C a x =
      a.left * soFieldAction n F parameters rank N C S a.right x * a.left⁻¹ := rfl

@[simp] theorem soAmbientAction_inr (e : FieldGroup f) :
    soAmbientAction S rank C (SemidirectProduct.inr e) =
      soFieldAction n F parameters rank N C S e := by
  exact SemidirectProduct.lift_inr _ _ _ e

/-- The derived SO subgroup is characteristic, so the same actual
semidirect action restricts without any extra stability input. -/
def omegaAmbientAction : OrthogonalAmbient n F parameters rank N C S →*
    MulAut (Omega n F) :=
  (MulAut.characteristic (omegaSubgroup n F)).comp (soAmbientAction S rank C)

@[simp] theorem omegaAmbientAction_value
    (a : OrthogonalAmbient n F parameters rank N C S) (x : Omega n F) :
    omegaToSpecialOrthogonal n F (omegaAmbientAction S rank C a x) =
      a.left * soFieldAction n F parameters rank N C S a.right x.val * a.left⁻¹ := rfl

@[simp] theorem omegaAmbientAction_inr (e : FieldGroup f) :
    omegaAmbientAction S rank C (SemidirectProduct.inr e) =
      omegaFieldAction S rank C e := by
  change MulAut.characteristic (omegaSubgroup n F)
      (soAmbientAction S rank C (SemidirectProduct.inr e)) = _
  rw [soAmbientAction_inr]
  rfl

/-- Exact ambient naturality of the same Spin projection. -/
theorem spinProjection_ambient
    (a : TypeBWeightStabilizerSource.Ambient S) (g : Spin n F N) :
    spinProjection n F parameters rank N C (TypeBAutomorphismSource.ambientAutomorphism S a g) =
      omegaAmbientAction S rank C (ambientProjection n F parameters rank N C S a)
        (spinProjection n F parameters rank N C g) := by
  apply Subtype.ext
  change projection n F C.det_one (a.left * S.action a.right g.val * a.left⁻¹) =
    projection n F C.det_one a.left *
      soFieldAction n F parameters rank N C S a.right (projection n F C.det_one g.val) *
      (projection n F C.det_one a.left)⁻¹
  rw [map_mul, map_mul, map_inv, projection_field]

variable (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)

theorem matrixOmegaEquiv_ambient_mk
    (a : TypeBWeightStabilizerSource.Ambient S) (g : Spin n F N) :
    matrixOmegaEquiv n F N parameters rank C centre
        (QuotientGroup.mk' (Subgroup.center (Spin n F N))
          (TypeBAutomorphismSource.ambientAutomorphism S a g)) =
      omegaAmbientAction S rank C (ambientProjection n F parameters rank N C S a)
        (matrixOmegaEquiv n F N parameters rank C centre
          (QuotientGroup.mk' (Subgroup.center (Spin n F N)) g)) :=
  spinProjection_ambient S rank C a g

theorem matrixOmegaEquiv_ambient_action
    (a : TypeBWeightStabilizerSource.Ambient S) (x : TypeBSpinCoverSource.Omega N) :
    matrixOmegaEquiv n F N parameters rank C centre
        (TypeBCentralKernelSpinBinding.omegaAction S
          (TypeBCentralKernelCarriers.qA (TypeBCentralKernelSpinBinding.P S) a) x) =
      omegaAmbientAction S rank C (ambientProjection n F parameters rank N C S a)
        (matrixOmegaEquiv n F N parameters rank C centre x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Spin n F N)) x
  rw [TypeBCentralKernelSpinBinding.omegaAction_mk]
  exact matrixOmegaEquiv_ambient_mk S rank C centre a g

/-- The complete actor square is on the existing quotient A/P and its
actual residual projection, for every quotient actor and Omega element. -/
theorem matrixOmegaEquiv_residual_action
    (a : ResidualAmbient n F parameters N S) (x : TypeBSpinCoverSource.Omega N) :
    matrixOmegaEquiv n F N parameters rank C centre
        (TypeBCentralKernelSpinBinding.omegaAction S a x) =
      omegaAmbientAction S rank C
        (residualProjection n F parameters N S rank C centre a)
        (matrixOmegaEquiv n F N parameters rank C centre x) := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (TypeBCentralKernelSpinBinding.P S) a
  exact matrixOmegaEquiv_ambient_action S rank C centre b x

/-- Equality of the actual homomorphisms into the automorphism carrier.
It is an intertwining statement, not a full-automorphism surjectivity claim. -/
theorem matrixOmegaEquiv_intertwines :
    (MulAut.congr (matrixOmegaEquiv n F N parameters rank C centre)).toMonoidHom.comp
        (TypeBCentralKernelSpinBinding.omegaAction S) =
      (omegaAmbientAction S rank C).comp
        (residualProjection n F parameters N S rank C centre) := by
  apply MonoidHom.ext
  intro a
  apply MulEquiv.ext
  intro x
  change matrixOmegaEquiv n F N parameters rank C centre
      (TypeBCentralKernelSpinBinding.omegaAction S a
        ((matrixOmegaEquiv n F N parameters rank C centre).symm x)) = _
  rw [matrixOmegaEquiv_residual_action]
  exact congrArg
    (omegaAmbientAction S rank C (residualProjection n F parameters N S rank C centre a))
    ((matrixOmegaEquiv n F N parameters rank C centre).apply_symm_apply x)

include rank C centre in
theorem residualScalars_fix
    (a : ResidualAmbient n F parameters N S) (ha : a ∈ residualScalars n F parameters N S)
    (x : TypeBSpinCoverSource.Omega N) :
    TypeBCentralKernelSpinBinding.omegaAction S a x = x := by
  apply (matrixOmegaEquiv n F N parameters rank C centre).injective
  rw [matrixOmegaEquiv_residual_action]
  rw [(residualProjection_eq_one_iff n F parameters N S rank C centre a).mpr ha, map_one]
  rfl

include rank C centre in
/-- Residual scalars centralize the actual embedded Omega, without any
assertion that the field group fixes scalars pointwise. -/
theorem residualScalars_centralizeOmega
    (a : ResidualAmbient n F parameters N S) (ha : a ∈ residualScalars n F parameters N S)
    (x : TypeBSpinCoverSource.Omega N) :
    a * TypeBCentralKernelSpinBinding.omegaEmbedding S x =
      TypeBCentralKernelSpinBinding.omegaEmbedding S x * a := by
  have h := TypeBCentralKernelSpinBinding.omegaAction_embedding S a x
  rw [residualScalars_fix S rank C centre a ha x] at h
  have multiplied := congrArg (fun b : ResidualAmbient n F parameters N S => b * a) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using multiplied.symm

end ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientActionBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
