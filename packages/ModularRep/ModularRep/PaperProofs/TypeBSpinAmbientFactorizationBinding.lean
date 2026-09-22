import ModularRep.PaperProofs.TypeBSpinEffectiveSourceBinding
import ModularRep.PaperProofs.TypeBAutomorphismSource
import ModularRep.CyclicOuterBrauerExtension

/-!
# Constructed effective Spin actions and literal ambient inertia

The effective Brauer action is the existing permutation action on the
prescribed root fibre. The ambient action is induced by the actual Spin
automorphism of a special-Clifford and field semidirect-product element.
Their two factor formulas agree as literal character twists.

The final deduction converts an already established pointwise effective
factorization into a product of actual inertia subgroup images. It is an
internal conversion; no character, block, or constituent is selected here.
-/

noncomputable section
set_option autoImplicit false

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBSpinAmbientFactorizationBinding

open ModularRep TypeBCliffordCarriers TypeBSpinStabilizer
open TypeBSpinDiagonalFieldQuotient TypeBSpinEffectiveClassActions
open TypeBSpinEffectiveSourceBinding TypeBWeightStabilizerSource
open TypeBAutomorphismSource CyclicOuterLemma37Concrete

variable {n p f ell : ℕ} {F K k : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field K] [CharZero K] [Field k] [CharP k ell] [IsAlgClosed k]
variable (N : NormSource n F) (D : DiagonalSource N)
variable {parameters : OddFieldParameters F p f}
variable (fs : FieldActionSource n F p f parameters N)
variable [Finite (Spin n F N)]
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

/-- The actual ambient group acts through its natural Spin automorphisms. -/
@[instance_reducible]
def ambientBrauerAction : MulAction (Ambient fs) (IBr iota) :=
  rightAutomorphismAction (X := IBr iota) (ambientAutomorphism fs)

/-- Inertia is the inverse-automorphism preimage of the literal stabilizer. -/
def ambientBrauerInertia (phi : IBr iota) : Subgroup (Ambient fs) :=
  (MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ phi).comap
    (inverseOpHom (ambientAutomorphism fs))

/-- The special-Clifford inertia is embedded by the actual left inclusion. -/
def specialCliffordInertiaImage (phi : IBr iota) : Subgroup (Ambient fs) :=
  ((ambientBrauerInertia N fs iota phi).comap
    (SemidirectProduct.inl : SpecialClifford n F →* Ambient fs)).map
      SemidirectProduct.inl

/-- The field inertia is embedded by the actual right inclusion. -/
def fieldInertiaImage (phi : IBr iota) : Subgroup (Ambient fs) :=
  ((ambientBrauerInertia N fs iota phi).comap
    (SemidirectProduct.inr : FieldGroup f →* Ambient fs)).map
      SemidirectProduct.inr

/-- Membership uses the same ambient action, including its inverse convention. -/
theorem mem_ambientBrauerInertia (a : Ambient fs) (phi : IBr iota) :
    letI := ambientBrauerAction N fs iota
    a ∈ ambientBrauerInertia N fs iota phi ↔ a • phi = phi :=
  Iff.rfl

/-- The effective diagonal factor is the actual inverse conjugation pullback. -/
theorem diagonal_smul_eq_twist (g : SpecialClifford n F) (phi : IBr iota) :
    letI := brauerAction N D fs iota
    ((D.diagonal g, 1) : OuterGroup f) • phi =
      IrreducibleBrauerCharacter.twist iota phi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) :=
  effectiveBrauerHom_diagonal_apply N D fs iota g phi

/-- The effective field factor is the actual inverse field pullback. -/
theorem field_smul_eq_twist (e : FieldGroup f) (phi : IBr iota) :
    letI := brauerAction N D fs iota
    ((1, e) : OuterGroup f) • phi =
      IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F fs e⁻¹) :=
  effectiveBrauerHom_field_apply N D fs iota e phi

/-- The left ambient inclusion realizes the same effective diagonal action. -/
theorem ambient_inl_smul (g : SpecialClifford n F) (phi : IBr iota) :
    letI := brauerAction N D fs iota
    letI := ambientBrauerAction N fs iota
    (SemidirectProduct.inl g : Ambient fs) • phi =
      ((D.diagonal g, 1) : OuterGroup f) • phi := by
  letI := brauerAction N D fs iota
  letI := ambientBrauerAction N fs iota
  change IrreducibleBrauerCharacter.twist iota phi
    (ambientAutomorphism fs (SemidirectProduct.inl g : Ambient fs)⁻¹) = _
  have h : ambientAutomorphism fs
      (SemidirectProduct.inl g : Ambient fs)⁻¹ =
      MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹ := by
    simp only [map_inv, ambientAutomorphism_inl]
  rw [h]
  exact (diagonal_smul_eq_twist N D fs iota g phi).symm

/-- The right ambient inclusion realizes the same effective field action. -/
theorem ambient_inr_smul (e : FieldGroup f) (phi : IBr iota) :
    letI := brauerAction N D fs iota
    letI := ambientBrauerAction N fs iota
    (SemidirectProduct.inr e : Ambient fs) • phi =
      ((1, e) : OuterGroup f) • phi := by
  letI := brauerAction N D fs iota
  letI := ambientBrauerAction N fs iota
  change IrreducibleBrauerCharacter.twist iota phi
    (ambientAutomorphism fs (SemidirectProduct.inr e : Ambient fs)⁻¹) = _
  have h : ambientAutomorphism fs
      (SemidirectProduct.inr e : Ambient fs)⁻¹ =
      spinFieldAction n F fs e⁻¹ := by
    simp only [map_inv, ambientAutomorphism_inr]
  rw [h]
  exact (field_smul_eq_twist N D fs iota e phi).symm

/-- Every actual ambient element acts through its two effective coordinates. -/
theorem ambient_smul_eq_effective (a : Ambient fs) (phi : IBr iota) :
    letI := brauerAction N D fs iota
    letI := ambientBrauerAction N fs iota
    a • phi = ((D.diagonal a.left, a.right) : OuterGroup f) • phi := by
  letI := brauerAction N D fs iota
  letI := ambientBrauerAction N fs iota
  calc
    a • phi = (SemidirectProduct.inl a.left : Ambient fs) •
        ((SemidirectProduct.inr a.right : Ambient fs) • phi) := by
      rw [← mul_smul, SemidirectProduct.inl_left_mul_inr_right]
    _ = ((D.diagonal a.left, 1) : OuterGroup f) •
        (((1, a.right) : OuterGroup f) • phi) := by
      rw [ambient_inl_smul N D fs iota, ambient_inr_smul N D fs iota]
    _ = ((D.diagonal a.left, a.right) : OuterGroup f) • phi := by
      rw [← mul_smul]
      apply congrArg (fun b : OuterGroup f => b • phi)
      exact Prod.ext (mul_one (D.diagonal a.left)) (one_mul a.right)

/-- A derived pointwise effective factorization gives the literal ambient product. -/
theorem ambient_inertia_product_of_effective (phi : IBr iota)
    (factorization :
      letI := brauerAction N D fs iota
      ∀ (g : SpecialClifford n F) (e : FieldGroup f),
        ((D.diagonal g, 1) : OuterGroup f) •
            (((1, e) : OuterGroup f) • phi) = phi ↔
          ((D.diagonal g, 1) : OuterGroup f) • phi = phi ∧
            ((1, e) : OuterGroup f) • phi = phi) :
    (ambientBrauerInertia N fs iota phi : Set (Ambient fs)) =
      (specialCliffordInertiaImage N fs iota phi : Set (Ambient fs)) *
        (fieldInertiaImage N fs iota phi : Set (Ambient fs)) := by
  letI := brauerAction N D fs iota
  letI := ambientBrauerAction N fs iota
  have hm : ∀ (g : SpecialClifford n F) (psi : IBr iota),
      (SemidirectProduct.inl g : Ambient fs) • psi =
        ((D.diagonal g, 1) : OuterGroup f) • psi :=
    ambient_inl_smul N D fs iota
  have he : ∀ (e : FieldGroup f) (psi : IBr iota),
      (SemidirectProduct.inr e : Ambient fs) • psi =
        ((1, e) : OuterGroup f) • psi :=
    ambient_inr_smul N D fs iota
  have hc : ∀ (g : SpecialClifford n F) (e : FieldGroup f),
      (SemidirectProduct.inl g : Ambient fs) •
          ((SemidirectProduct.inr e : Ambient fs) • phi) = phi ↔
        (SemidirectProduct.inl g : Ambient fs) • phi = phi ∧
          (SemidirectProduct.inr e : Ambient fs) • phi = phi := by
    intro g e
    simpa only [hm, he] using factorization g e
  ext a
  constructor
  · intro ha
    have ha' : a • phi = phi := ha
    have hcombined : (SemidirectProduct.inl a.left : Ambient fs) •
        ((SemidirectProduct.inr a.right : Ambient fs) • phi) = phi := by
      rw [← mul_smul, SemidirectProduct.inl_left_mul_inr_right]
      exact ha'
    obtain ⟨hl, hr⟩ := (hc a.left a.right).mp hcombined
    exact Set.mem_mul.mpr ⟨SemidirectProduct.inl a.left,
      ⟨a.left, hl, rfl⟩, SemidirectProduct.inr a.right,
      ⟨a.right, hr, rfl⟩, SemidirectProduct.inl_left_mul_inr_right a⟩
  · intro ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp ha
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨e, he', rfl⟩ := hy
    exact (ambientBrauerInertia N fs iota phi).mul_mem hg he'

end ModularRep.PaperProofs.TypeBSpinAmbientFactorizationBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
