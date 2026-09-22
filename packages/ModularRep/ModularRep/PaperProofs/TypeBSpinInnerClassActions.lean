import ModularRep.KZeroTwist
import ModularRep.FDRepEquiv
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.PrimitiveBlockAutomorphism
import ModularRep.PaperProofs.TypeBCliffordScalarNorm

/-!
# Inner and central kernels for the literal Spin class actions

Conjugating a representation by `g` is intertwined with the original
representation by its actual operator `rho g⁻¹`. Consequently inner twists
act trivially on exact FDRep K0 over any coefficient field. The same fact
for function-valued Brauer characters and literal primitive blocks is reused
from their checked conjugacy invariance.

The final kernels are on the actual norm-one Spin subgroup inside the
special Clifford normalizer. They contain `SpinSubgroup ⊔ center D0`.
No diagonal quotient, outer action, rational-series stability, character
correspondence, or new external source is supplied in this file.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace ModularRep.PaperProofs.TypeBSpinInnerClassActions

open ModularRep ExactGrothendieckGroup TypeBCliffordCarriers

universe u

section Inner

variable {k G V : Type u} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The actual inverse group operator, viewed as a linear equivalence. -/
def innerLinearEquiv (rho : Representation k G V) (g : G) : V ≃ₗ[k] V where
  toFun := rho g⁻¹
  invFun := rho g
  left_inv := rho.self_inv_apply g
  right_inv := rho.inv_self_apply g
  map_add' := (rho g⁻¹).map_add
  map_smul' := (rho g⁻¹).map_smul

@[simp] theorem innerLinearEquiv_apply
    (rho : Representation k G V) (g : G) (v : V) :
    innerLinearEquiv rho g v = rho g⁻¹ v := rfl

/-- The intertwiner has the precise orientation for right pullback. -/
def innerTwistEquiv (rho : Representation k G V) (g : G) :
    (rho.twist (MulAut.conj g)).Equiv rho := by
  refine Representation.Equiv.mk (innerLinearEquiv rho g) ?_
  intro h
  ext v
  change rho g⁻¹ (rho (g * h * g⁻¹) v) = rho h (rho g⁻¹ v)
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]

@[simp] theorem innerTwistEquiv_apply
    (rho : Representation k G V) (g : G) (v : V) :
    innerTwistEquiv rho g v = rho g⁻¹ v := rfl

/-- The actual twisted FDRep object is isomorphic to the original object. -/
def innerTwistFDRepIso (X : FDRep k G) (g : G) :
    (FDRep.twistEquivalence k G (MulAut.conj g)).functor.obj X ≅ X := by
  refine Action.mkIso
    (LinearEquiv.toFGModuleCatIso (innerTwistEquiv X.ρ g).toLinearEquiv) ?_
  intro h
  ext v
  exact Representation.IntertwiningMap.isIntertwining
    (Representation.twist X.ρ (MulAut.conj g)) X.ρ
    (innerTwistEquiv X.ρ g).toIntertwiningMap h v

/-- Inner automorphisms induce the identity on exact K0, in every field. -/
theorem twistKZero_inner (g : G) :
    twistKZero (k := k) (MulAut.conj g) =
      AddMonoidHom.id (FDRepKZero k G) := by
  apply ExactGrothendieckGroup.hom_ext
  intro X
  rw [twistKZero_classOf]
  exact ExactGrothendieckGroup.classOf_iso (FDRep k G) (innerTwistFDRepIso X g)

@[simp] theorem twistKZero_inner_apply (g : G) (x : FDRepKZero k G) :
    twistKZero (k := k) (MulAut.conj g) x = x := by
  rw [twistKZero_inner]
  rfl

/-- Ordinary character fixation uses its actual realizing trace character. -/
theorem ordinaryTwist_inner [CharZero k]
    (chi : OrdinaryIrreducibleCharacter.Irr k G) (g : G) :
    OrdinaryIrreducibleCharacter.twist k G chi (MulAut.conj g) = chi := by
  obtain ⟨R⟩ := chi.property
  apply OrdinaryIrreducibleCharacter.ext
  intro h
  change chi (g * h * g⁻¹) = chi h
  calc
    chi (g * h * g⁻¹) = R.representation.character (g * h * g⁻¹) :=
      (congrFun R.character_eq _).symm
    _ = R.representation.character h := R.representation.char_conj h g
    _ = chi h := congrFun R.character_eq h

end Inner

section Spin

variable {n : ℕ} {F k : Type u} [Field F] [Field k]
  (N : NormSource n F)

/-- Restricting conjugation by an actual Spin element is its inner automorphism. -/
theorem spinConjugation_inner (g : Spin n F N) :
    MulAut.conjNormal (H := SpinSubgroup n F N) g.val = MulAut.conj g := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  rfl

/-- Every actual central special Clifford element acts identically on Spin. -/
theorem spinConjugation_center (z : SpecialClifford n F)
    (hz : z ∈ Subgroup.center (SpecialClifford n F)) :
    MulAut.conjNormal (H := SpinSubgroup n F N) z =
      MulEquiv.refl (Spin n F N) := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  change z * h.val * z⁻¹ = h.val
  rw [← Subgroup.mem_center_iff.mp hz h.val]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- The actual conjugation homomorphism with inverse-pullback orientation. -/
def spinInverseConjugation : SpecialClifford n F →* (MulAut (Spin n F N))ᵐᵒᵖ where
  toFun g := MulOpposite.op (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)
  map_one' := by simp
  map_mul' g h := by simp

@[simp] theorem spinInverseConjugation_apply (g : SpecialClifford n F) :
    (spinInverseConjugation N g).unop =
      MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹ := rfl

/-- Exact K0 action constructed from the actual special Clifford conjugation. -/
def spinKZeroAction : Representation ℤ (SpecialClifford n F) (FDRepKZero k (Spin n F N)) :=
  (twistKZeroRepresentation (k := k) (G := Spin n F N)).comp
    (spinInverseConjugation N)

@[simp] theorem spinKZeroAction_apply (g : SpecialClifford n F)
    (x : FDRepKZero k (Spin n F N)) :
    spinKZeroAction (k := k) N g x =
      twistKZero (k := k) (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) x := rfl

theorem spinKZeroAction_spin (g : Spin n F N) (x : FDRepKZero k (Spin n F N)) :
    spinKZeroAction (k := k) N g.val x = x := by
  rw [spinKZeroAction_apply]
  change twistKZero (k := k) (MulAut.conjNormal (H := SpinSubgroup n F N) (g⁻¹).val) x = x
  rw [spinConjugation_inner, twistKZero_inner_apply]

theorem spinKZeroAction_center (z : SpecialClifford n F)
    (hz : z ∈ Subgroup.center (SpecialClifford n F))
    (x : FDRepKZero k (Spin n F N)) :
    spinKZeroAction (k := k) N z x = x := by
  rw [spinKZeroAction_apply,
    spinConjugation_center N z⁻¹ ((Subgroup.center _).inv_mem hz), twistKZero_refl]
  rfl

/-- The required kernel containment is a deduction on the literal norm kernel. -/
theorem spinKZeroAction_kernel :
    SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) ≤
      (spinKZeroAction (k := k) N).ker := by
  apply sup_le
  · intro g hg
    change spinKZeroAction (k := k) N g = 1
    apply LinearMap.ext
    intro x
    exact spinKZeroAction_spin N ⟨g, hg⟩ x
  · intro z hz
    change spinKZeroAction (k := k) N z = 1
    apply LinearMap.ext
    intro x
    exact spinKZeroAction_center N z hz x

/-- In particular, the actual algebra-map scalar units act trivially. -/
theorem spinKZeroAction_scalar (z : Fˣ) (x : FDRepKZero k (Spin n F N)) :
    spinKZeroAction (k := k) N (TypeBCliffordScalarNorm.scalar n F z) x = x :=
  spinKZeroAction_center N _ (TypeBCliffordScalarNorm.scalar_mem_center n F z) x

/-- The corresponding action on actual primitive central idempotents. -/
def spinBlockHom : SpecialClifford n F →* Equiv.Perm (LiteralPrimitiveBlock k (Spin n F N)) :=
  (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ
    (LiteralPrimitiveBlock k (Spin n F N))).comp (spinInverseConjugation N)

@[simp] theorem spinBlockHom_apply (g : SpecialClifford n F)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    spinBlockHom (k := k) N g b = LiteralPrimitiveBlock.rightTwistBlock b
      (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) := rfl

theorem spinBlockHom_spin (g : Spin n F N) (b : LiteralPrimitiveBlock k (Spin n F N)) :
    spinBlockHom (k := k) N g.val b = b := by
  change MulOpposite.op
    (MulAut.conjNormal (H := SpinSubgroup n F N) (g⁻¹).val) • b = b
  rw [spinConjugation_inner]
  exact LiteralPrimitiveBlock.inner_smul g b

theorem spinBlockHom_center (z : SpecialClifford n F)
    (hz : z ∈ Subgroup.center (SpecialClifford n F))
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    spinBlockHom (k := k) N z b = b := by
  change MulOpposite.op (MulAut.conjNormal (H := SpinSubgroup n F N) z⁻¹) • b = b
  rw [spinConjugation_center N z⁻¹ ((Subgroup.center _).inv_mem hz)]
  exact one_smul (MulAut (Spin n F N))ᵐᵒᵖ b

theorem spinBlockHom_kernel :
    SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) ≤
      (spinBlockHom (k := k) N).ker := by
  apply sup_le
  · intro g hg
    change spinBlockHom (k := k) N g = 1
    apply Equiv.ext
    intro b
    exact spinBlockHom_spin N ⟨g, hg⟩ b
  · intro z hz
    change spinBlockHom (k := k) N z = 1
    apply Equiv.ext
    intro b
    exact spinBlockHom_center N z hz b

theorem spinBlockHom_scalar (z : Fˣ) (b : LiteralPrimitiveBlock k (Spin n F N)) :
    spinBlockHom (k := k) N (TypeBCliffordScalarNorm.scalar n F z) b = b :=
  spinBlockHom_center N _ (TypeBCliffordScalarNorm.scalar_mem_center n F z) b

theorem spinOrdinaryTwist_spin [CharZero k]
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N)) (g : Spin n F N) :
    OrdinaryIrreducibleCharacter.twist k (Spin n F N) chi
      (MulAut.conjNormal (H := SpinSubgroup n F N) g.val⁻¹) = chi := by
  change OrdinaryIrreducibleCharacter.twist k (Spin n F N) chi
    (MulAut.conjNormal (H := SpinSubgroup n F N) (g⁻¹).val) = chi
  rw [spinConjugation_inner]
  exact ordinaryTwist_inner chi g⁻¹

theorem spinOrdinaryTwist_center [CharZero k]
    (chi : OrdinaryIrreducibleCharacter.Irr k (Spin n F N))
    (z : SpecialClifford n F) (hz : z ∈ Subgroup.center (SpecialClifford n F)) :
    OrdinaryIrreducibleCharacter.twist k (Spin n F N) chi
      (MulAut.conjNormal (H := SpinSubgroup n F N) z⁻¹) = chi := by
  rw [spinConjugation_center N z⁻¹ ((Subgroup.center _).inv_mem hz)]
  exact OrdinaryIrreducibleCharacter.twist_refl k (Spin n F N) chi

section Brauer

variable {ell : ℕ} {K : Type u} [Field K] [CharZero K]
  [CharP k ell] [IsAlgClosed k] [Finite (Spin n F N)]
  (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

/-- The Brauer permutation action uses the prescribed root and actual pullback. -/
def spinBrauerHom : SpecialClifford n F →* Equiv.Perm (IBr iota) :=
  (MulAction.toPermHom (MulAut (Spin n F N))ᵐᵒᵖ (IBr iota)).comp
    (spinInverseConjugation N)

@[simp] theorem spinBrauerHom_apply (g : SpecialClifford n F) (phi : IBr iota) :
    spinBrauerHom N iota g phi = IrreducibleBrauerCharacter.twist iota phi
      (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) := rfl

theorem spinBrauerHom_spin (g : Spin n F N) (phi : IBr iota) :
    spinBrauerHom N iota g.val phi = phi := by
  rw [spinBrauerHom_apply]
  change IrreducibleBrauerCharacter.twist iota phi
    (MulAut.conjNormal (H := SpinSubgroup n F N) (g⁻¹).val) = phi
  rw [spinConjugation_inner]
  exact IrreducibleBrauerCharacter.twist_eq_self_of_underlying iota phi
    (MulAut.conj g⁻¹) (PrimeRegularClassFunction.twist_conj phi.val g⁻¹)

theorem spinBrauerHom_center (z : SpecialClifford n F)
    (hz : z ∈ Subgroup.center (SpecialClifford n F)) (phi : IBr iota) :
    spinBrauerHom N iota z phi = phi := by
  rw [spinBrauerHom_apply,
    spinConjugation_center N z⁻¹ ((Subgroup.center _).inv_mem hz)]
  exact IrreducibleBrauerCharacter.twist_refl iota phi

theorem spinBrauerHom_kernel :
    SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) ≤
      (spinBrauerHom N iota).ker := by
  apply sup_le
  · intro g hg
    change spinBrauerHom N iota g = 1
    apply Equiv.ext
    intro phi
    exact spinBrauerHom_spin N iota ⟨g, hg⟩ phi
  · intro z hz
    change spinBrauerHom N iota z = 1
    apply Equiv.ext
    intro phi
    exact spinBrauerHom_center N iota z hz phi

theorem spinBrauerHom_scalar (z : Fˣ) (phi : IBr iota) :
    spinBrauerHom N iota (TypeBCliffordScalarNorm.scalar n F z) phi = phi :=
  spinBrauerHom_center N iota _ (TypeBCliffordScalarNorm.scalar_mem_center n F z) phi

end Brauer
end Spin

end ModularRep.PaperProofs.TypeBSpinInnerClassActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
