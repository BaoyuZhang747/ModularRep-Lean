import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding
import ModularRep.PaperProofs.TypeBCliffordOrthogonalFieldAction
import ModularRep.PaperProofs.TypeBOrthogonalFieldAutomorphism

/-!
# Frobenius compatibility of the literal Spin-to-matrix-Omega map

The Clifford and matrix field actions use the same coordinate Frobenius.
The field squares follow from their proved vector formulas and faithful
linear actions; they are not additional structural source fields.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordOrthogonalFieldBinding

open TypeBCliffordCarriers TypeBCliffordOrthogonalSourceBinding
open TypeBOrthogonalOmegaCarriers TypeBOrthogonalFieldAutomorphism

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (S : FieldActionSource n F p f parameters N) (rank : 3 ≤ n)
  (C : Source n F p f parameters rank N)

/-- The coordinate Frobenius is surjective on this actual finite field space. -/
theorem vectorFrobenius_surjective (hp : p.Prime) :
    Function.Surjective (fun v : Vector n F => fun i => v i ^ p) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact (coordinateEquiv n F (frobeniusEquiv F p)).surjective

/-- The constructed D0 -> SO projection intertwines the actual prime
field action with entrywise Frobenius in the fixed matrix coordinates. -/
theorem projection_field_generator (g : SpecialClifford n F) :
    projection n F C.det_one (S.action (fieldGenerator f) g) =
      primeFrobeniusSpecialOrthogonal n F p parameters.prime
        (projection n F C.det_one g) := by
  apply specialOrthogonalToLinear_injective n F
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := vectorFrobenius_surjective (n := n) parameters.prime v
  exact (TypeBCliffordOrthogonalFieldAction.generator_square S g w).trans
    (primeFrobeniusSpecialOrthogonal_square n F p parameters.prime
      (projection n F C.det_one g) w).symm

/-- The same field square restricts to the actual norm-one Spin subgroup
and the independently defined derived SO subgroup. -/
theorem spinProjection_field_generator (g : Spin n F N) :
    spinProjection n F parameters rank N C
        (spinFieldAutomorphism n F S (fieldGenerator f) g) =
      primeFrobeniusOmega n F p parameters.prime
        (spinProjection n F parameters rank N C g) := by
  apply omegaToLinear_injective n F
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := vectorFrobenius_surjective (n := n) parameters.prime v
  exact (TypeBCliffordOrthogonalFieldAction.generator_square S g.val w).trans
    (primeFrobeniusOmega_square n F p parameters.prime
      (spinProjection n F parameters rank N C g) w).symm

/-- The quotient isomorphism's point formula commutes with Frobenius on
every actual Spin representative. -/
theorem matrixOmegaEquiv_field_mk
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (g : Spin n F N) :
    matrixOmegaEquiv n F N parameters rank C centre
        (QuotientGroup.mk' (Subgroup.center (Spin n F N))
          (spinFieldAutomorphism n F S (fieldGenerator f) g)) =
      primeFrobeniusOmega n F p parameters.prime
        (matrixOmegaEquiv n F N parameters rank C centre
          (QuotientGroup.mk' (Subgroup.center (Spin n F N)) g)) :=
  spinProjection_field_generator S rank C g

/-- The quotient field square uses the existing actual A/P action on
literal Spin/Z(Spin), at the prime field generator, for every quotient element. -/
theorem matrixOmegaEquiv_field_action
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (x : TypeBSpinCoverSource.Omega N) :
    matrixOmegaEquiv n F N parameters rank C centre
        (TypeBCentralKernelSpinBinding.omegaAction S
          (TypeBCentralKernelCarriers.qA (TypeBCentralKernelSpinBinding.P S)
            (SemidirectProduct.inr (fieldGenerator f))) x) =
      primeFrobeniusOmega n F p parameters.prime
        (matrixOmegaEquiv n F N parameters rank C centre x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Spin n F N)) x
  rw [TypeBCentralKernelSpinBinding.omegaAction_mk,
    TypeBAutomorphismSource.ambientAutomorphism_inr]
  exact matrixOmegaEquiv_field_mk S rank C centre g

end ModularRep.PaperProofs.TypeBCliffordOrthogonalFieldBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
