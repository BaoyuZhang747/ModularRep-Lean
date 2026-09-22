import ModularRep.PaperProofs.CharacterInductionEquivariance

/-!
# The effective conjugation kernel in the characteristic-two Clifford step

This file checks the finite group deduction used in manuscript Lemma 4.6.
If an element is trivial modulo `H C_Gamma(H)`, then it is a product of an
element of `H` and an element centralising `H`.  Consequently, on `H` it acts
by the same conjugation as the `H`-factor.  If the element fixes a selected
constituent and the centralising factor acts trivially on that constituent,
the `H`-factor belongs to its inertia group.

No Clifford correspondence, Gallagher theorem, Brauer-character extension,
or stabiliser factorisation is assumed or proved here.  The final declarations
give both orientations of the induced automorphism.  The inverse orientation
is the one used when the manuscript's right action is encoded as a Lean left
action.
-/

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordKernel

universe u v

variable {Gamma : Type u} [Group Gamma]

/-- The literal subgroup `H C_Gamma(H)` occurring in Lemma 4.6. -/
def effectiveConjugationKernel (H : Subgroup Gamma) : Subgroup Gamma :=
  H ⊔ Subgroup.centralizer (H : Set Gamma)

/-- The effective conjugation kernel is normal whenever `H` is normal. -/
theorem effectiveConjugationKernel_normal
    (H : Subgroup Gamma) [H.Normal] :
    (effectiveConjugationKernel H).Normal := by
  unfold effectiveConjugationKernel
  exact Subgroup.sup_normal _ _

/-- Membership in `H C_Gamma(H)` gives the literal product decomposition
needed in the manuscript argument. -/
theorem decompose_mem_effectiveConjugationKernel
    (H : Subgroup Gamma) [H.Normal] (a : Gamma)
    (ha : a ∈ effectiveConjugationKernel H) :
    ∃ h c : Gamma,
      h ∈ H ∧ c ∈ Subgroup.centralizer (H : Set Gamma) ∧
        a = h * c := by
  unfold effectiveConjugationKernel at ha
  change a ∈
    ((↑(H ⊔ Subgroup.centralizer (H : Set Gamma)) : Set Gamma)) at ha
  rw [Subgroup.mul_normal H (Subgroup.centralizer (H : Set Gamma))] at ha
  obtain ⟨h, hh, c, hc, hmul⟩ := ha
  exact ⟨h, c, hh, hc, hmul.symm⟩

/-- A quotient-kernel equation is converted to the product decomposition;
the product membership is derived rather than supplied. -/
theorem decompose_of_quotient_eq_one
    (H : Subgroup Gamma) [H.Normal] (a : Gamma)
    (ha :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      QuotientGroup.mk' (effectiveConjugationKernel H) a = 1) :
    ∃ h c : Gamma,
      h ∈ H ∧ c ∈ Subgroup.centralizer (H : Set Gamma) ∧
        a = h * c := by
  let _ : (effectiveConjugationKernel H).Normal :=
    effectiveConjugationKernel_normal H
  apply decompose_mem_effectiveConjugationKernel H a
  exact (QuotientGroup.eq_one_iff a).mp ha

section Inertia

variable {Theta : Type v} [MulAction Gamma Theta]

/-- The inertia subgroup of a selected constituent inside `H`, using the
restriction of the ambient action. -/
def inertiaSubgroup (H : Subgroup Gamma) (theta : Theta) : Subgroup H := by
  let _ := MulAction.compHom Theta H.subtype
  exact MulAction.stabilizer H theta

/-- The literal ambient stabiliser of the selected constituent.  Only this
subgroup, rather than all of `Gamma`, acts on the fixed inertia group. -/
def ambientStabilizer (theta : Theta) : Subgroup Gamma :=
  MulAction.stabilizer Gamma theta

/-- The inertia group represented as a normal subgroup of the ambient
stabiliser.  This carrier is definitionally the inverse image of `H`. -/
def inertiaInAmbientStabilizer
    (H : Subgroup Gamma) (theta : Theta) :
    Subgroup (ambientStabilizer (Gamma := Gamma) theta) :=
  H.comap (ambientStabilizer (Gamma := Gamma) theta).subtype

/-- Normality of the inertia group in the ambient stabiliser follows by
pulling back normality of `H`. -/
theorem inertiaInAmbientStabilizer_normal
    (H : Subgroup Gamma) [H.Normal] (theta : Theta) :
    (inertiaInAmbientStabilizer (Gamma := Gamma) H theta).Normal := by
  unfold inertiaInAmbientStabilizer
  infer_instance

/-- The two natural carriers for `H_theta` are canonically isomorphic: as a
subgroup of `H`, or as the inverse image of `H` inside the ambient stabiliser
of `theta`. -/
def inertiaCarrierEquiv (H : Subgroup Gamma) (theta : Theta) :
    inertiaInAmbientStabilizer (Gamma := Gamma) H theta ≃*
      inertiaSubgroup H theta where
  toFun x := ⟨⟨((x : ambientStabilizer (Gamma := Gamma) theta) : Gamma),
    x.property⟩, by
      change ((x : ambientStabilizer (Gamma := Gamma) theta) : Gamma) • theta = theta
      exact x.1.property⟩
  invFun x := ⟨⟨((x : H) : Gamma), by
      change ((x : H) : Gamma) • theta = theta
      exact x.property⟩, x.1.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

/-- Turn a homomorphism into the inverse opposite homomorphism used to encode
a right action as a Lean left action. -/
def inverseOppositeHom {A B : Type*} [Group A] [Group B]
    (rho : A →* B) : A →* Bᵐᵒᵖ where
  toFun a := MulOpposite.op (rho a⁻¹)
  map_one' := by simp
  map_mul' a b := by simp

/-- The genuine right-conjugation action on the fixed inertia group.  Its
source is the stabiliser of `theta`, which is exactly the subgroup that
normalises that inertia group. -/
def rightConjugationOnInertiaHom
    (H : Subgroup Gamma) [H.Normal] (theta : Theta) :
    ambientStabilizer (Gamma := Gamma) theta →*
      (MulAut (inertiaInAmbientStabilizer (Gamma := Gamma) H theta))ᵐᵒᵖ := by
  let _ : (inertiaInAmbientStabilizer (Gamma := Gamma) H theta).Normal :=
    inertiaInAmbientStabilizer_normal H theta
  exact inverseOppositeHom
    (MulAut.conjNormal
      (H := inertiaInAmbientStabilizer (Gamma := Gamma) H theta))

/-- Conjugation by an ambient element fixing `theta` preserves its inertia
subgroup in the normal subgroup `H`. -/
theorem inertiaSubgroup_stable_under_conjugation
    (H : Subgroup Gamma) [H.Normal] (theta : Theta)
    (a : Gamma) (haTheta : a • theta = theta) :
    ∀ x : H,
      x ∈ inertiaSubgroup H theta ↔
        MulAut.conjNormal a x ∈ inertiaSubgroup H theta := by
  intro x
  change (x : Gamma) • theta = theta ↔
    (a * (x : Gamma) * a⁻¹) • theta = theta
  have haInvTheta : a⁻¹ • theta = theta := by
    apply (MulAction.injective a)
    simp [haTheta]
  constructor
  · intro hx
    simp [mul_smul, haInvTheta, hx, haTheta]
  · intro hx
    have h := congrArg (fun y : Theta ↦ a⁻¹ • y) hx
    simpa [mul_smul, haInvTheta] using h

/-- The automorphism of the inertia subgroup induced by an ambient element
which fixes the selected constituent. -/
def conjugationOnInertia
    (H : Subgroup Gamma) [H.Normal] (theta : Theta)
    (a : Gamma) (haTheta : a • theta = theta) :
    MulAut (inertiaSubgroup H theta) :=
  CharacterInductionEquivariance.restrictAut
    (inertiaSubgroup H theta) (MulAut.conjNormal a)
    (inertiaSubgroup_stable_under_conjugation H theta a haTheta)

/-- The manuscript-specific kernel-to-inertia deduction.  The only
action-specific input says that elements centralising `H` act trivially on
the selected constituent.  For conjugation on a character of a normal
subgroup of `H`, this is the standard fact that the identity automorphism
fixes the character.

Lean derives an element `h` of the inertia group and proves that conjugation
by the original kernel element agrees on all of `H` with conjugation by `h`.
-/
theorem quotientKernel_acts_inner_on_inertia
    (H : Subgroup Gamma) [H.Normal]
    (theta : Theta)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (a : Gamma)
    (haKernel :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      QuotientGroup.mk' (effectiveConjugationKernel H) a = 1)
    (haTheta : a • theta = theta) :
    ∃ h : Gamma,
      h ∈ H ∧ h • theta = theta ∧
        ∀ x : Gamma, x ∈ H →
          a * x * a⁻¹ = h * x * h⁻¹ := by
  obtain ⟨h, c, hh, hc, ha⟩ :=
    decompose_of_quotient_eq_one H a haKernel
  have hcTheta : c • theta = theta := centralizer_fixes c hc
  have hhTheta : h • theta = theta := by
    rw [ha, mul_smul, hcTheta] at haTheta
    exact haTheta
  refine ⟨h, hh, hhTheta, ?_⟩
  intro x hx
  have hcx : c * x = x * c := by
    rw [Subgroup.mem_centralizer_iff] at hc
    exact (hc x hx).symm
  rw [ha]
  calc
    (h * c) * x * (h * c)⁻¹ = h * (c * x) * c⁻¹ * h⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    _ = h * (x * c) * c⁻¹ * h⁻¹ := by rw [hcx]
    _ = h * x * h⁻¹ := by simp [mul_assoc]

/-- Subtype-level form of `quotientKernel_acts_inner_on_inertia`: the inner
element is packaged as an actual member of the inertia subgroup. -/
theorem quotientKernel_conjugation_inner_on_inertia
    (H : Subgroup Gamma) [H.Normal]
    (theta : Theta)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (a : Gamma)
    (haKernel :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      QuotientGroup.mk' (effectiveConjugationKernel H) a = 1)
    (haTheta : a • theta = theta) :
    ∃ h : inertiaSubgroup H theta,
      ∀ x : inertiaSubgroup H theta,
        a * (x : H) * a⁻¹ = (h : H) * (x : H) * (h : H)⁻¹ := by
  obtain ⟨h, hh, hhTheta, hconj⟩ :=
    quotientKernel_acts_inner_on_inertia H theta centralizer_fixes a
      haKernel haTheta
  let hH : H := ⟨h, hh⟩
  have hH_inertia : hH ∈ inertiaSubgroup H theta := by
    change h • theta = theta
    exact hhTheta
  let hI : inertiaSubgroup H theta := ⟨hH, hH_inertia⟩
  refine ⟨hI, ?_⟩
  intro x
  exact hconj (x : H) x.1.property

/-- Automorphism-level form of the kernel-to-inertia deduction.  This is the
literal innerness assertion needed to discharge the effective-kernel field
of the function-valued Brauer-character theorem. -/
theorem conjugationOnInertia_eq_inner_of_quotient_eq_one
    (H : Subgroup Gamma) [H.Normal]
    (theta : Theta)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (a : Gamma)
    (haKernel :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      QuotientGroup.mk' (effectiveConjugationKernel H) a = 1)
    (haTheta : a • theta = theta) :
    ∃ h : inertiaSubgroup H theta,
      conjugationOnInertia H theta a haTheta = MulAut.conj h := by
  obtain ⟨h, hconj⟩ :=
    quotientKernel_conjugation_inner_on_inertia H theta centralizer_fixes a
      haKernel haTheta
  refine ⟨h, ?_⟩
  ext x
  exact hconj x

/-- Inverse-conjugation form of the kernel-to-inertia deduction.  Under the
manuscript's right-action convention, a Lean left action by `a` uses the
automorphism induced by `a⁻¹`. -/
theorem inverse_conjugationOnInertia_eq_inner_of_quotient_eq_one
    (H : Subgroup Gamma) [H.Normal]
    (theta : Theta)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (a : Gamma)
    (haKernel :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      QuotientGroup.mk' (effectiveConjugationKernel H) a = 1)
    (haTheta : a • theta = theta) :
    ∃ h : inertiaSubgroup H theta,
      (conjugationOnInertia H theta a haTheta)⁻¹ = MulAut.conj h := by
  obtain ⟨h, hh⟩ :=
    conjugationOnInertia_eq_inner_of_quotient_eq_one H theta
      centralizer_fixes a haKernel haTheta
  refine ⟨h⁻¹, ?_⟩
  rw [hh]
  exact (map_inv (MulAut.conj :
    inertiaSubgroup H theta →* MulAut (inertiaSubgroup H theta)) h).symm

/-- Opposite-automorphism form of the inverse-conjugation conclusion.  This
has the orientation required by the function-valued Brauer-character action.
It is deliberately pointwise: only the stabiliser of `theta` acts on the
fixed inertia subgroup, so no action of all of `Gamma` on that subgroup is
postulated. -/
theorem op_inverse_conjugationOnInertia_eq_inner_of_quotient_eq_one
    (H : Subgroup Gamma) [H.Normal]
    (theta : Theta)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (a : Gamma)
    (haKernel :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      QuotientGroup.mk' (effectiveConjugationKernel H) a = 1)
    (haTheta : a • theta = theta) :
    ∃ h : inertiaSubgroup H theta,
      MulOpposite.op ((conjugationOnInertia H theta a haTheta)⁻¹) =
        MulOpposite.op (MulAut.conj h) := by
  obtain ⟨h, hh⟩ :=
    inverse_conjugationOnInertia_eq_inner_of_quotient_eq_one H theta
      centralizer_fixes a haKernel haTheta
  exact ⟨h, congrArg MulOpposite.op hh⟩

/-- Source-shaped kernel theorem on the correct fixed carrier.  If an
element of the ambient stabiliser is trivial in the effective conjugation
quotient, its right-conjugation action on the inertia group is inner.

Unlike the discarded global adapter, this theorem does not postulate an
action of elements that move `theta` on the fixed group `H_theta`. -/
theorem rightConjugationOnInertiaHom_inner_of_quotient_eq_one
    (H : Subgroup Gamma) [H.Normal]
    (theta : Theta)
    (centralizer_fixes : ∀ c : Gamma,
      c ∈ Subgroup.centralizer (H : Set Gamma) → c • theta = theta)
    (a : ambientStabilizer (Gamma := Gamma) theta)
    (haKernel :
      letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
      QuotientGroup.mk' (effectiveConjugationKernel H) (a : Gamma) = 1) :
    ∃ h : inertiaInAmbientStabilizer (Gamma := Gamma) H theta,
      rightConjugationOnInertiaHom H theta a =
        MulOpposite.op (MulAut.conj h) := by
  have haInvTheta : (a : Gamma)⁻¹ • theta = theta := by
    exact (MulAction.stabilizer Gamma theta).inv_mem a.property
  have haInvKernel :
      (letI : (effectiveConjugationKernel H).Normal :=
        effectiveConjugationKernel_normal H
       QuotientGroup.mk' (effectiveConjugationKernel H) (a : Gamma)⁻¹ = 1) := by
    let _ : (effectiveConjugationKernel H).Normal :=
      effectiveConjugationKernel_normal H
    rw [map_inv, haKernel]
    exact inv_one
  obtain ⟨h, hh, hhTheta, hconj⟩ :=
    quotientKernel_acts_inner_on_inertia H theta centralizer_fixes
      (a : Gamma)⁻¹ haInvKernel haInvTheta
  let hA : ambientStabilizer (Gamma := Gamma) theta := ⟨h, hhTheta⟩
  let hI : inertiaInAmbientStabilizer (Gamma := Gamma) H theta := ⟨hA, hh⟩
  refine ⟨hI, ?_⟩
  apply congrArg MulOpposite.op
  ext x
  exact hconj ((x : ambientStabilizer (Gamma := Gamma) theta) : Gamma)
    x.property

end Inertia

end ModularRep.PaperProofs.TypeBCharacteristicTwoCliffordKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
