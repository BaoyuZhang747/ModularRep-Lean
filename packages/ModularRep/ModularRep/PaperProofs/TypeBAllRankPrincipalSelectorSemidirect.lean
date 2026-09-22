import ModularRep.PaperProofs.TypeBAutomorphismSource
import ModularRep.PaperProofs.TypeBInertiaHallSource
import ModularRep.PaperProofs.TypeBSemidirectFixedFieldFactorization
import ModularRep.CyclicOuterBrauerExtension
import ModularRep.BrauerCharacterEquivTransport
import ModularRep.BrauerCharacterExtensionBridge

/-!
# Literal stabilizer and extension deductions for the principal selector

The internal fixedness hypothesis below is supplied by the principal-selector
application for each actual principal-block Brauer character. The actor is the
same Frobenius source on the specified Clifford algebra and its norm kernel.
The Clifford-by-field action is inverse pullback through its constructed
natural automorphism, and the stabilizer factors use the canonical inclusions.

For the extension, the base is the kernel of the right projection of the
literal Spin-by-field semidirect product. Its equivalence with Spin, the root
transport, character invariance and cyclic quotient are constructed here. The
output is a representation of the whole semidirect product whose restriction
along the actual left inclusion affords the original character with the SAME
root embedding.

The only extension source is `BrauerCyclicExtensionPrinciple`: Navarro,
*Characters and Blocks of Finite Groups*, Theorem (8.12), p. 163. This uniform
E1 theorem constructs an extension of an invariant irreducible representation
over the algebraically closed modular field across a cyclic quotient. No
extension of this Spin character, field selector or criterion conclusion is
supplied as a source.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorSemidirect

open ModularRep TypeBCliffordCarriers
open CyclicOuterLemma37Concrete

variable {n p f ell : ℕ} {F k K : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable {N : NormSource n F} {parameters : OddFieldParameters F p f}
variable (fs : FieldActionSource n F p f parameters N)
variable [Finite (SpecialClifford n F)]
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

/-- The literal Clifford-by-field carrier for the chosen Frobenius action. -/
abbrev CliffordFieldGroup := SpecialClifford n F ⋊[fs.action] FieldGroup f

/-- The literal Spin-by-field carrier with the restricted SAME action. -/
abbrev SpinFieldGroup := Spin n F N ⋊[spinFieldAction n F fs] FieldGroup f

/-- The inclusion of the Spin-by-field group in the Clifford-by-field
group uses the fixed norm-kernel inclusion and the identity on fields. -/
def spinFieldInclusion : SpinFieldGroup fs →* CliffordFieldGroup fs where
  toFun a := ⟨a.left.val, a.right⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The same natural ambient action restricts to the actual inner/field
automorphism used in the extension deduction. -/
theorem ambientAutomorphism_spinField (a : SpinFieldGroup fs) :
    TypeBAutomorphismSource.ambientAutomorphism fs (spinFieldInclusion fs a) =
      MulAut.conj a.left * spinFieldAction n F fs a.right := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rfl

/-- The actual Brauer action is inverse pullback of the natural ambient map. -/
@[instance_reducible] def cliffordBrauerAction :
    MulAction (CliffordFieldGroup fs) (IBr iota) :=
  rightAutomorphismAction (X := IBr iota)
    (TypeBAutomorphismSource.ambientAutomorphism fs)

/-- The stabilizer of the prescribed actual function-valued Brauer character. -/
def cliffordStabilizer (psi : IBr iota) : Subgroup (CliffordFieldGroup fs) :=
  letI := cliffordBrauerAction fs iota
  MulAction.stabilizer (CliffordFieldGroup fs) psi

/-- The left factor acts by actual special Clifford conjugation on Spin. -/
theorem cliffordBrauerAction_inl (g : SpecialClifford n F) (psi : IBr iota) :
    letI := cliffordBrauerAction fs iota
    (SemidirectProduct.inl g : CliffordFieldGroup fs) • psi =
      IrreducibleBrauerCharacter.twist iota psi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) := by
  change IrreducibleBrauerCharacter.twist iota psi
    (TypeBAutomorphismSource.ambientAutomorphism fs
      ((SemidirectProduct.inl g : CliffordFieldGroup fs)⁻¹)) = _
  rw [← map_inv, TypeBAutomorphismSource.ambientAutomorphism_inl]

/-- The right factor uses the SAME inverse field twist as the projective
and Brauer fixation deduction. -/
theorem cliffordBrauerAction_inr (e : FieldGroup f) (psi : IBr iota) :
    letI := cliffordBrauerAction fs iota
    (SemidirectProduct.inr e : CliffordFieldGroup fs) • psi =
      IrreducibleBrauerCharacter.twist iota psi
        (spinFieldAction n F fs e⁻¹) := by
  change IrreducibleBrauerCharacter.twist iota psi
    (TypeBAutomorphismSource.ambientAutomorphism fs
      ((SemidirectProduct.inr e : CliffordFieldGroup fs)⁻¹)) = _
  rw [← map_inv, TypeBAutomorphismSource.ambientAutomorphism_inr]

/-- Individual field fixation forces the literal Clifford-by-field
stabilizer product. No stabilizer or product identity is a source input. -/
theorem cliffordStabilizer_eq_product (psi : IBr iota)
    (fixed : ∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota psi
      (spinFieldAction n F fs e⁻¹) = psi) :
    (cliffordStabilizer fs iota psi : Set (CliffordFieldGroup fs)) =
      ((cliffordStabilizer fs iota psi ⊓
        (SemidirectProduct.inl (φ := fs.action)).range) :
          Set (CliffordFieldGroup fs)) *
      ((SemidirectProduct.inr (φ := fs.action)).range :
        Set (CliffordFieldGroup fs)) := by
  letI := cliffordBrauerAction fs iota
  have hfixed : ∀ e : FieldGroup f,
      (SemidirectProduct.inr e : CliffordFieldGroup fs) • psi = psi := by
    intro e
    rw [cliffordBrauerAction_inr]
    exact fixed e
  have hle := TypeBSemidirectFixedFieldFactorization.inr_range_le_stabilizer
    fs.action psi hfixed
  have h := TypeBSemidirectFixedFieldFactorization.stabilizer_eq_product_of_inr_fixed
    fs.action psi hfixed
  have rightSet := congrArg
    (fun J : Subgroup (CliffordFieldGroup fs) => (J : Set (CliffordFieldGroup fs)))
    (inf_eq_right.mpr hle)
  exact h.trans (congrArg (fun T : Set (CliffordFieldGroup fs) =>
    ((cliffordStabilizer fs iota psi ⊓
      (SemidirectProduct.inl (φ := fs.action)).range) : Set (CliffordFieldGroup fs)) * T)
    rightSet)

/-- Elementwise form with the actual conjugation twist exposed. -/
theorem mem_cliffordStabilizer_iff (psi : IBr iota)
    (fixed : ∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota psi
      (spinFieldAction n F fs e⁻¹) = psi)
    (a : CliffordFieldGroup fs) :
    a ∈ cliffordStabilizer fs iota psi ↔
      IrreducibleBrauerCharacter.twist iota psi
        (MulAut.conjNormal (H := SpinSubgroup n F N) a.left⁻¹) = psi := by
  letI := cliffordBrauerAction fs iota
  have hfixed : ∀ e : FieldGroup f,
      (SemidirectProduct.inr e : CliffordFieldGroup fs) • psi = psi := by
    intro e
    rw [cliffordBrauerAction_inr]
    exact fixed e
  exact (TypeBSemidirectFixedFieldFactorization.mem_stabilizer_iff_inl_smul_of_inr_fixed
    fs.action psi hfixed a).trans (by rw [cliffordBrauerAction_inl])

/-- The left factor is the canonical image of the existing actual special
Clifford Brauer inertia. This identification needs no field-fixation premise. -/
theorem cliffordStabilizer_inf_inl_eq_brauerInertia_map (psi : IBr iota) :
    cliffordStabilizer fs iota psi ⊓
        (SemidirectProduct.inl (φ := fs.action)).range =
      (TypeBInertiaHallSource.brauerInertia N iota psi).map
        (SemidirectProduct.inl (φ := fs.action)) := by
  letI := cliffordBrauerAction fs iota
  apply le_antisymm
  · rintro a ⟨hstab, g, hg⟩
    refine ⟨g, ?_, hg⟩
    apply (TypeBInertiaHallSource.mem_brauerInertia N iota psi g).mpr
    rw [← hg] at hstab
    change (SemidirectProduct.inl g : CliffordFieldGroup fs) • psi = psi at hstab
    simpa only [cliffordBrauerAction_inl] using hstab
  · rintro a ⟨g, hg, rfl⟩
    refine ⟨?_, ⟨g, rfl⟩⟩
    change (SemidirectProduct.inl g : CliffordFieldGroup fs) • psi = psi
    rw [cliffordBrauerAction_inl]
    exact (TypeBInertiaHallSource.mem_brauerInertia N iota psi g).mp hg

/-- The manuscript's stabilizer product on its literal downstairs Brauer
inertia and the full canonical field subgroup. -/
theorem cliffordStabilizer_eq_brauerInertia_product (psi : IBr iota)
    (fixed : ∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota psi
      (spinFieldAction n F fs e⁻¹) = psi) :
    (cliffordStabilizer fs iota psi : Set (CliffordFieldGroup fs)) =
      ((TypeBInertiaHallSource.brauerInertia N iota psi).map
        (SemidirectProduct.inl (φ := fs.action)) :
          Set (CliffordFieldGroup fs)) *
      ((SemidirectProduct.inr (φ := fs.action)).range :
        Set (CliffordFieldGroup fs)) := by
  have factorSet := congrArg
    (fun J : Subgroup (CliffordFieldGroup fs) =>
      (J : Set (CliffordFieldGroup fs)) *
        ((SemidirectProduct.inr (φ := fs.action)).range : Set (CliffordFieldGroup fs)))
    (cliffordStabilizer_inf_inl_eq_brauerInertia_map fs iota psi)
  exact (cliffordStabilizer_eq_product fs iota psi fixed).trans factorSet

/-- The actual embedded Spin subgroup of the FULL Spin-by-field group. -/
abbrev spinKernel : Subgroup (SpinFieldGroup fs) :=
  (SemidirectProduct.rightHom (φ := spinFieldAction n F fs)).ker

/-- The equivalence is fixed by the canonical left inclusion, with inverse
the left coordinate. There is no choice of an abstract base-group model. -/
def spinKernelEquiv : Spin n F N ≃* spinKernel fs where
  toFun g := ⟨SemidirectProduct.inl g, SemidirectProduct.rightHom_inl g⟩
  invFun x := x.val.left
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact x.property.symm
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (SemidirectProduct.inl (φ := spinFieldAction n F fs)) g h

@[simp] theorem spinKernelEquiv_val (g : Spin n F N) :
    (spinKernelEquiv fs g).val =
      (SemidirectProduct.inl g : SpinFieldGroup fs) := rfl

@[simp] theorem spinKernelEquiv_symm (x : spinKernel fs) :
    (spinKernelEquiv fs).symm x = x.val.left := rfl

/-- Conjugation in the actual semidirect product gives the expected inner
and field automorphisms under the canonical base equivalence. -/
theorem spinKernel_conjugation (a : SpinFieldGroup fs) (x : spinKernel fs) :
    (spinKernelEquiv fs).symm (MulAut.conjNormal a x) =
      a.left * spinFieldAction n F fs a.right ((spinKernelEquiv fs).symm x) *
        a.left⁻¹ := by
  change (a * x.val * a⁻¹).left =
    a.left * spinFieldAction n F fs a.right x.val.left * a.left⁻¹
  have hx : x.val.right = 1 := x.property
  simp [hx, mul_assoc]

variable [fieldExponent : NeZero f]

private instance spinFieldGroup_finite : Finite (SpinFieldGroup fs) :=
  Finite.of_equiv
    (Spin n F N × FieldGroup f) (SemidirectProduct.equivProd.symm)

/-- All finite group root transport is through the canonical base map. -/
def spinKernelRoot : PrimeRegularRootEmbedding ell k K (spinKernel fs) :=
  iota.alongMulEquiv (spinKernelEquiv fs)

@[simp] theorem spinKernelRoot_lift (z : k) :
    (spinKernelRoot fs iota).lift z = iota.lift z :=
  iota.alongMulEquiv_lift (spinKernelEquiv fs) z

/-- The prescribed character pulled back through the same base equivalence. -/
def spinKernelBrauer (psi : IBr iota) : IBr (spinKernelRoot fs iota) :=
  IrreducibleBrauerCharacter.alongMulEquiv iota (spinKernelEquiv fs) psi

/-- Individual field fixation and class-function conjugacy invariance
imply invariance under the WHOLE Spin-by-field group. -/
theorem spinKernelBrauer_fixed (psi : IBr iota)
    (fixed : ∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota psi
      (spinFieldAction n F fs e⁻¹) = psi)
    (a : SpinFieldGroup fs) :
    IrreducibleBrauerCharacter.twist (spinKernelRoot fs iota)
      (spinKernelBrauer fs iota psi) (MulAut.conjNormal a) =
        spinKernelBrauer fs iota psi := by
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  let e := spinKernelEquiv fs
  let y := PrimeRegularElement.map e.symm.toMonoidHom x
  let z := PrimeRegularElement.map
    (spinFieldAction n F fs a.right).toMonoidHom y
  have hmap : PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map (MulAut.conjNormal a).toMonoidHom x) =
        PrimeRegularElement.map (MulAut.conj a.left).toMonoidHom z := by
    apply Subtype.ext
    exact spinKernel_conjugation fs a x.val
  have hinner := congrArg
    (fun q : PrimeRegularClassFunction K (Spin n F N) ell => q z)
    (PrimeRegularClassFunction.twist_conj psi.val a.left)
  have hfield : IrreducibleBrauerCharacter.twist iota psi
      (spinFieldAction n F fs a.right) = psi := by
    simpa only [inv_inv] using fixed a.right⁻¹
  have hfieldval := congrArg (fun q : IBr iota => q.val y) hfield
  change psi.val (PrimeRegularElement.map e.symm.toMonoidHom
    (PrimeRegularElement.map (MulAut.conjNormal a).toMonoidHom x)) = psi.val y
  rw [hmap]
  exact hinner.trans hfieldval

/-- The quotient is the literal cyclic field group, through the right
projection; cyclicity is derived, not a source premise. -/
theorem spinField_quotient_cyclic : IsCyclic (SpinFieldGroup fs ⧸ spinKernel fs) := by
  let e := (SemidirectProduct.toGroupExtension
    (spinFieldAction n F fs)).quotientKerRightHomEquivRight
  exact isCyclic_of_injective e.toMonoidHom e.injective

include fieldExponent in
/-- Extension on the full literal group and the ORIGINAL Spin
carrier and root. The only external theorem is the uniform Navarro E1;
the fixedness premise is internal to the combined principal-selector proof. -/
theorem extends_to_spinField (psi : IBr iota)
    (fixed : ∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota psi
      (spinFieldAction n F fs e⁻¹) = psi)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k) :
    ∃ V : FDRep k (Spin n F N), Representation.IsIrreducible V.ρ ∧
      psi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota ∧
      ∃ rho : Representation k (SpinFieldGroup fs) V.V,
        Representation.IsIrreducible rho ∧
        Nonempty (Representation.Equiv
          (Representation.pullback rho
            (SemidirectProduct.inl (φ := spinFieldAction n F fs))) V.ρ) := by
  let e := spinKernelEquiv fs
  obtain ⟨W, hW, hcharacter, ⟨extension⟩⟩ :=
    Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
      principle (spinKernelRoot fs iota) (spinKernelBrauer fs iota psi)
      (spinField_quotient_cyclic fs) (spinKernelBrauer_fixed fs iota psi fixed)
  refine ⟨FDRep.of (Representation.pullback W.ρ e.toMonoidHom),
    hW.pullback e.toMonoidHom e.surjective, ?_, extension.representation,
    extension.representation_isIrreducible hW, ?_⟩
  · apply PrimeRegularClassFunction.ext
    intro x
    have h := congrArg
      (fun q : PrimeRegularClassFunction K (spinKernel fs) ell =>
        q (PrimeRegularElement.map e.toMonoidHom x)) hcharacter
    have hx : PrimeRegularElement.map e.symm.toMonoidHom
        (PrimeRegularElement.map e.toMonoidHom x) = x := by
      apply Subtype.ext
      exact e.symm_apply_apply x.val
    have hlift : (spinKernelRoot fs iota).lift = iota.lift :=
      funext (spinKernelRoot_lift fs iota)
    change psi.val (PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map e.toMonoidHom x)) =
      ((W.ρ (e x.val)).charpoly.roots.map (spinKernelRoot fs iota).lift).sum at h
    rw [hx, hlift] at h
    exact h
  · exact ⟨extension.restrictionEquiv.pullback e.toMonoidHom⟩

end ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorSemidirect


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
