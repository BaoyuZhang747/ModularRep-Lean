import ModularRep.PaperProofs.TypeBSpinQuotientClassActions
import ModularRep.PaperProofs.TypeBCliffordIndexCompatibility
import ModularRep.PaperProofs.TypeBAutomorphismSource

/-!
# The actual diagonal quotient and its field action

The structural input contains only the literal diagonal homomorphism,
surjectivity and its exact Spin-join-centre kernel. All field preservation
and the identity of the induced field action are deductions. No class
action, character, block, basic set or effective-action conclusion is an
input. The quotient is not embedded in the automorphisms of Spin.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinDiagonalFieldQuotient

open TypeBCliffordCarriers TypeBSpinStabilizer TypeBSpinQuotientClassActions

variable {n : ℕ} {F : Type} [Field F] (N : NormSource n F)

/-- The precise retained structural boundary on the literal Clifford group.
Its published finite-point identification is separate from these deductions. -/
structure DiagonalSource where
  diagonal : SpecialClifford n F →* DiagonalGroup
  surjective : Function.Surjective diagonal
  kernel : diagonal.ker = kernelSubgroup N

/-- The first isomorphism theorem uses the exact supplied kernel equality. -/
def DiagonalSource.quotientEquiv (D : DiagonalSource N) :
    TypeBSpinQuotientClassActions.Quotient N ≃* DiagonalGroup :=
  QuotientGroup.liftEquiv (kernelSubgroup N) D.surjective D.kernel.symm

@[simp] theorem DiagonalSource.quotientEquiv_mk (D : DiagonalSource N)
    (g : SpecialClifford n F) :
    D.quotientEquiv N (projection N g) = D.diagonal g := rfl

/-- The cardinality belongs to the actual quotient, not D0/Spin alone. -/
theorem DiagonalSource.quotient_card (D : DiagonalSource N) :
    Nat.card (TypeBSpinQuotientClassActions.Quotient N) = 2 :=
  TypeBCliffordIndexCompatibility.specialClifford_quotient_order_two
    N D.diagonal D.surjective D.kernel

/-- An automorphism of a group with two elements fixes both elements. -/
theorem mulAut_eq_one_of_card_two {Q : Type*} [Group Q]
    (hcard : Nat.card Q = 2) (a : MulAut Q) : a = 1 := by
  apply MulEquiv.ext
  intro q
  by_cases hq : q = 1
  · simpa only [hq, map_one] using (rfl : (1 : MulAut Q) 1 = 1)
  · obtain ⟨t, ht, unique⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hcard
    have haq : a q ≠ 1 := by
      intro heq
      apply hq
      apply a.injective
      simpa only [map_one] using heq
    exact (unique (a q) haq).trans (unique q hq).symm

section Field

variable {p f : ℕ} [Finite F] [CharP F p]
  {parameters : OddFieldParameters F p f}
  (S : FieldActionSource n F p f parameters N)

/-- Both actual factors of the kernel are preserved by the field map. -/
theorem field_preserves_kernel (e : FieldGroup f) :
    kernelSubgroup N ≤ (kernelSubgroup N).comap (S.action e).toMonoidHom := by
  apply sup_le
  · intro g hg
    exact (show SpinSubgroup n F N ≤ kernelSubgroup N from le_sup_left)
      (field_preserves_spin n F S e g hg)
  · intro z hz
    exact (show Subgroup.center (SpecialClifford n F) ≤ kernelSubgroup N from le_sup_right)
      (TypeBAutomorphismSource.field_preserves_center S e z hz)

/-- Inverse field transport gives equality of the actual mapped subgroup. -/
theorem field_kernel_map (e : FieldGroup f) :
    (kernelSubgroup N).map (S.action e).toMonoidHom = kernelSubgroup N := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact field_preserves_kernel N S e hg
  · intro g hg
    refine ⟨S.action e⁻¹ g, field_preserves_kernel N S e⁻¹ hg, ?_⟩
    change S.action e (S.action e⁻¹ g) = g
    rw [map_inv]
    exact (S.action e).apply_symm_apply g

/-- The field automorphism on the actual quotient is the induced map. -/
def quotientFieldAutomorphism (e : FieldGroup f) :
    MulAut (TypeBSpinQuotientClassActions.Quotient N) :=
  QuotientGroup.congr (kernelSubgroup N) (kernelSubgroup N)
    (S.action e) (field_kernel_map N S e)

@[simp] theorem quotientFieldAutomorphism_mk (e : FieldGroup f)
    (g : SpecialClifford n F) :
    quotientFieldAutomorphism N S e (projection N g) =
      projection N (S.action e g) := rfl

/-- Induced field automorphisms compose as the original field maps do. -/
def quotientFieldAction :
    FieldGroup f →* MulAut (TypeBSpinQuotientClassActions.Quotient N) where
  toFun := quotientFieldAutomorphism N S
  map_one' := by
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun g => ?_
    change projection N (S.action 1 g) = projection N g
    rw [map_one]
    rfl
  map_mul' e d := by
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun g => ?_
    change projection N (S.action (e * d) g) =
      projection N (S.action e (S.action d g))
    rw [map_mul]
    rfl

@[simp] theorem quotientFieldAction_mk (e : FieldGroup f)
    (g : SpecialClifford n F) :
    quotientFieldAction N S e (projection N g) =
      projection N (S.action e g) := rfl

/-- The induced field map fixes the quotient because its order is two. -/
theorem quotientFieldAction_eq_one (D : DiagonalSource N) (e : FieldGroup f) :
    quotientFieldAction N S e = 1 :=
  mulAut_eq_one_of_card_two (D.quotient_card N) (quotientFieldAction N S e)

/-- The actual field transform and original element have the same coset. -/
theorem projection_field (D : DiagonalSource N) (e : FieldGroup f)
    (g : SpecialClifford n F) :
    projection N (S.action e g) = projection N g := by
  calc
    projection N (S.action e g) =
        quotientFieldAction N S e (projection N g) := rfl
    _ = projection N g := by
      rw [quotientFieldAction_eq_one N S D e]
      rfl

/-- The source's exact diagonal map is field invariant by quotient descent. -/
theorem diagonal_field (D : DiagonalSource N) (e : FieldGroup f)
    (g : SpecialClifford n F) : D.diagonal (S.action e g) = D.diagonal g := by
  have h := congrArg (D.quotientEquiv N) (projection_field N S D e g)
  simpa only [DiagonalSource.quotientEquiv_mk] using h

end Field

end ModularRep.PaperProofs.TypeBSpinDiagonalFieldQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
