import ModularRep.PaperProofs.TypeBSpinInnerClassActions
import ModularRep.PaperProofs.OddGFactorizationLemma312Relative
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Literal quotient descent of Spin class actions

The actor is the actual special Clifford group modulo its norm-one Spin
subgroup joined with its centre. The checked inner/scalar kernel
containments allow each class action to descend by `QuotientGroup.lift`.
Every projection formula retains the same inverse-conjugation convention.

The ordinary character action reuses the checked opposite-automorphism
action and the existing inner/central fixation theorems. No ordinary
algebraic closure, finite group or splitting-field hypothesis is needed
for that pullback construction. The Brauer action retains its prescribed
root and all actual coefficient and finite-carrier guards.

No diagonal quotient identification, field commutation, effective action
source, rational-series stability or external certificate is supplied here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinQuotientClassActions

open ModularRep ExactGrothendieckGroup TypeBCliffordCarriers
open TypeBSpinInnerClassActions

universe u

variable {n : ℕ} {F k : Type u} [Field F] [Field k]
  (N : NormSource n F)

/-- The literal subgroup already proved to kill the class actions. -/
abbrev kernelSubgroup : Subgroup (SpecialClifford n F) :=
  SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)

/-- The quotient is by the actual Spin join centre, before any C2 identification. -/
abbrev Quotient := SpecialClifford n F ⧸ kernelSubgroup N

/-- Its canonical projection, with the kernel subgroup fixed definitionally. -/
def projection : SpecialClifford n F →* Quotient N :=
  QuotientGroup.mk' (kernelSubgroup N)

theorem projection_surjective : Function.Surjective (projection N) :=
  QuotientGroup.mk'_surjective (kernelSubgroup N)

@[simp] theorem projection_kernel : (projection N).ker = kernelSubgroup N :=
  QuotientGroup.ker_mk' (kernelSubgroup N)

/-- Exact K0 descends through its proved kernel containment. -/
def quotientKZeroAction : Representation ℤ (Quotient N) (FDRepKZero k (Spin n F N)) :=
  QuotientGroup.lift (kernelSubgroup N) (spinKZeroAction (k := k) N)
    (spinKZeroAction_kernel (k := k) N)

@[simp] theorem quotientKZeroAction_mk (g : SpecialClifford n F) :
    quotientKZeroAction (k := k) N (projection N g) = spinKZeroAction (k := k) N g :=
  rfl

@[simp] theorem quotientKZeroAction_mk_apply (g : SpecialClifford n F)
    (x : FDRepKZero k (Spin n F N)) :
    quotientKZeroAction (k := k) N (projection N g) x =
      twistKZero (k := k) (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) x :=
  rfl

@[simp] theorem quotientKZeroAction_comp_projection :
    (quotientKZeroAction (k := k) N).comp (projection N) = spinKZeroAction (k := k) N :=
  rfl

/-- Literal primitive central idempotents descend by their actual kernel. -/
def quotientBlockHom : Quotient N →* Equiv.Perm (LiteralPrimitiveBlock k (Spin n F N)) :=
  QuotientGroup.lift (kernelSubgroup N) (spinBlockHom (k := k) N)
    (spinBlockHom_kernel (k := k) N)

@[simp] theorem quotientBlockHom_mk (g : SpecialClifford n F) :
    quotientBlockHom (k := k) N (projection N g) = spinBlockHom (k := k) N g :=
  rfl

@[simp] theorem quotientBlockHom_mk_apply (g : SpecialClifford n F)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    quotientBlockHom (k := k) N (projection N g) b =
      LiteralPrimitiveBlock.rightTwistBlock b
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) :=
  rfl

@[simp] theorem quotientBlockHom_comp_projection :
    (quotientBlockHom (k := k) N).comp (projection N) = spinBlockHom (k := k) N :=
  rfl

section Ordinary

variable [CharZero k]

/-- The existing ordinary pullback action restricted to actual Clifford conjugation. -/
def spinOrdinaryHom :
    SpecialClifford n F →* Equiv.Perm (OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) := by
  letI : MulAction (MulAut (Spin n F N))ᵐᵒᵖ
      (OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :=
    OddGFactorizationLemma312Relative.OrdinaryAction.oppositeAutomorphismAction
  exact (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ
    (OrdinaryIrreducibleCharacter.Irr k (Spin n F N))).comp (spinInverseConjugation N)

@[simp] theorem spinOrdinaryHom_apply (g : SpecialClifford n F)
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :
    spinOrdinaryHom (k := k) N g chi = OrdinaryIrreducibleCharacter.twist k (Spin n F N) chi
      (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) :=
  rfl

/-- Its kernel follows from the checked ordinary inner and central fixation. -/
theorem spinOrdinaryHom_kernel :
    kernelSubgroup N ≤ (spinOrdinaryHom (k := k) N).ker := by
  apply sup_le
  · intro g hg
    change spinOrdinaryHom (k := k) N g = 1
    apply Equiv.ext
    intro chi
    exact spinOrdinaryTwist_spin N chi ⟨g, hg⟩
  · intro z hz
    change spinOrdinaryHom (k := k) N z = 1
    apply Equiv.ext
    intro chi
    exact spinOrdinaryTwist_center N chi z hz

/-- The literal ordinary-character permutation homomorphism on the quotient. -/
def quotientOrdinaryHom :
    Quotient N →* Equiv.Perm (OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :=
  QuotientGroup.lift (kernelSubgroup N) (spinOrdinaryHom (k := k) N)
    (spinOrdinaryHom_kernel (k := k) N)

@[simp] theorem quotientOrdinaryHom_mk (g : SpecialClifford n F) :
    quotientOrdinaryHom (k := k) N (projection N g) = spinOrdinaryHom (k := k) N g :=
  rfl

@[simp] theorem quotientOrdinaryHom_mk_apply (g : SpecialClifford n F)
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) :
    quotientOrdinaryHom (k := k) N (projection N g) chi =
      OrdinaryIrreducibleCharacter.twist k (Spin n F N) chi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) :=
  rfl

@[simp] theorem quotientOrdinaryHom_comp_projection :
    (quotientOrdinaryHom (k := k) N).comp (projection N) = spinOrdinaryHom (k := k) N :=
  rfl

end Ordinary

section Brauer

variable {ell : ℕ} {K : Type u} [Field K] [CharZero K]
  [CharP k ell] [IsAlgClosed k] [Finite (Spin n F N)]
  (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

/-- The prescribed-root Brauer permutation homomorphism descends literally. -/
def quotientBrauerHom : Quotient N →* Equiv.Perm (IBr iota) :=
  QuotientGroup.lift (kernelSubgroup N) (spinBrauerHom N iota)
    (spinBrauerHom_kernel N iota)

@[simp] theorem quotientBrauerHom_mk (g : SpecialClifford n F) :
    quotientBrauerHom N iota (projection N g) = spinBrauerHom N iota g :=
  rfl

@[simp] theorem quotientBrauerHom_mk_apply (g : SpecialClifford n F) (phi : IBr iota) :
    quotientBrauerHom N iota (projection N g) phi =
      IrreducibleBrauerCharacter.twist iota phi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) :=
  rfl

@[simp] theorem quotientBrauerHom_comp_projection :
    (quotientBrauerHom N iota).comp (projection N) = spinBrauerHom N iota :=
  rfl

end Brauer

end ModularRep.PaperProofs.TypeBSpinQuotientClassActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
