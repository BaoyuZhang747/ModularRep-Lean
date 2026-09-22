import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import ModularRep.PaperProofs.OddTwoProposition33Relative

/-!
# The corrected even multiplicity factor in Proposition 3.3

Feng--Yu--Zhang construct the corrected basic factor
`R^{0,-}_{d,1,1}` on a tensor product `W ⊗ U`: the quaternion group acts
as `I_W ⊗ E_-^3`, whereas the manuscript's excluding reflection acts as
`t ⊗ I_U`.  This file checks the literal bridge from that source-shaped
Kronecker construction to the permutation-wreath and Sylow obstruction
already formalised in `OddTwoWreathReflection` and
`OddTwoProposition33Relative`.

The source-specific claims that the quaternion representation is the
corrected Feng--Yu--Zhang factor and that the final block diagonal map has
the stated image in the finite symplectic group remain external inputs.  The
orthogonal existence and nonscalarity of `t` also remain the routine sourced
fact `SF-ORTHOGONAL-REFLECTION`.  No principal-weight exclusion, BAW-goodness,
or iBAW conclusion is accepted as an input.
-/

namespace ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter

open Matrix
open scoped Kronecker
open OddTwoWreathReflection

universe u v w x y z

section KroneckerFactor

variable {F : Type u} {I : Type v} {J : Type w}
variable [Field F]
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Left Kronecker multiplication by the identity, lifted to general linear
groups.  It models `t ⊗ I_U` on the multiplicity tensor factor. -/
def leftKroneckerHom : GL I F →* GL (I × J) F where
  toFun t := Matrix.GeneralLinearGroup.kronecker t 1
  map_one' := by
    apply Units.ext
    change (1 : Matrix I I F) ⊗ₖ (1 : Matrix J J F) = 1
    simp
  map_mul' t s := by
    apply Units.ext
    change (↑(t * s) : Matrix I I F) ⊗ₖ (1 : Matrix J J F) =
      ((↑t : Matrix I I F) ⊗ₖ (1 : Matrix J J F)) *
        ((↑s : Matrix I I F) ⊗ₖ (1 : Matrix J J F))
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [← Matrix.mul_kronecker_mul]
    simp

/-- Right Kronecker multiplication by the identity, lifted to general linear
groups.  It models the corrected subgroup `I_W ⊗ E_-^3`. -/
def rightKroneckerHom : GL J F →* GL (I × J) F where
  toFun e := Matrix.GeneralLinearGroup.kronecker 1 e
  map_one' := by
    apply Units.ext
    change (1 : Matrix I I F) ⊗ₖ (1 : Matrix J J F) = 1
    simp
  map_mul' e d := by
    apply Units.ext
    change (1 : Matrix I I F) ⊗ₖ (↑(e * d) : Matrix J J F) =
      ((1 : Matrix I I F) ⊗ₖ (↑e : Matrix J J F)) *
        ((1 : Matrix I I F) ⊗ₖ (↑d : Matrix J J F))
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [← Matrix.mul_kronecker_mul]
    simp

@[simp]
theorem leftKroneckerHom_coe (t : GL I F) :
    ↑(leftKroneckerHom (I := I) (J := J) t) =
      (↑t : Matrix I I F) ⊗ₖ (1 : Matrix J J F) := rfl

@[simp]
theorem rightKroneckerHom_coe (e : GL J F) :
    ↑(rightKroneckerHom (I := I) (J := J) e) =
      (1 : Matrix I I F) ⊗ₖ (↑e : Matrix J J F) := rfl

/-- Left and right Kronecker images commute. -/
theorem leftKroneckerHom_commute_rightKroneckerHom
    (t : GL I F) (e : GL J F) :
    Commute (leftKroneckerHom (I := I) (J := J) t)
      (rightKroneckerHom (I := I) (J := J) e) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, leftKroneckerHom_coe,
    rightKroneckerHom_coe]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- The literal right Kronecker image of the source basic subgroup. -/
def correctedTensorBaseSubgroup (E : Subgroup (GL J F)) :
    Subgroup (GL (I × J) F) :=
  E.map (rightKroneckerHom (I := I) (J := J))

/-- A nonscalar involution in the left tensor factor centralises, but does
not lie in, the right Kronecker image of any subgroup of `GL(J,F)`.

The nonmembership statement is derived from the matrix equality: if
`t ⊗ I = I ⊗ e`, then `t` is scalar. -/
theorem leftReflection_involution_centralises_outside_correctedBase
    [Nonempty J] (E : Subgroup (GL J F)) (t : GL I F)
    (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ a : F,
      (↑t : Matrix I I F) ≠ a • (1 : Matrix I I F)) :
    let T := leftKroneckerHom (I := I) (J := J) t
    T ^ 2 = 1 ∧
      T ∈ Subgroup.centralizer
        (correctedTensorBaseSubgroup (I := I) E : Set (GL (I × J) F)) ∧
      T ∉ correctedTensorBaseSubgroup (I := I) E := by
  dsimp only
  constructor
  · simpa using congrArg (leftKroneckerHom (I := I) (J := J)) htSq
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    rcases he with ⟨e, he, rfl⟩
    exact (leftKroneckerHom_commute_rightKroneckerHom t e).symm
  · intro hmem
    rcases hmem with ⟨e, he, hEq⟩
    have hMatrix :
        (↑t : Matrix I I F) ⊗ₖ (1 : Matrix J J F) =
          (1 : Matrix I I F) ⊗ₖ (↑e : Matrix J J F) := by
      exact congrArg Units.val hEq.symm
    obtain ⟨a, ha⟩ :=
      leftKronecker_eq_rightKronecker_forces_scalar
        (↑t : Matrix I I F) (↑e : Matrix J J F) hMatrix
    exact htNonscalar a ha

/-- The matrix group preserving the bilinear form with Gram matrix `J0`.
This is used only to make the source block diagonal realisation instantiable:
the full general linear group does not embed in the ambient symplectic group,
whereas this form preserving subgroup does. -/
def formIsometrySubgroup (J0 : Matrix I I F) : Subgroup (GL I F) where
  carrier := {g | (↑g : Matrix I I F)ᵀ * J0 * ↑g = J0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (↑g : Matrix I I F)ᵀ * J0 * (↑g : Matrix I I F) = J0 at hg
    change (↑h : Matrix I I F)ᵀ * J0 * (↑h : Matrix I I F) = J0 at hh
    change (↑(g * h) : Matrix I I F)ᵀ * J0 *
      (↑(g * h) : Matrix I I F) = J0
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul]
    calc
      (↑h : Matrix I I F)ᵀ * (↑g : Matrix I I F)ᵀ * J0 *
          ((↑g : Matrix I I F) * (↑h : Matrix I I F)) =
        (↑h : Matrix I I F)ᵀ *
          ((↑g : Matrix I I F)ᵀ * J0 * (↑g : Matrix I I F)) *
            (↑h : Matrix I I F) := by simp only [mul_assoc]
      _ = J0 := by rw [hg]; exact hh
  inv_mem' := by
    intro g hg
    change (↑g : Matrix I I F)ᵀ * J0 * (↑g : Matrix I I F) = J0 at hg
    change (↑g⁻¹ : Matrix I I F)ᵀ * J0 * (↑g⁻¹ : Matrix I I F) = J0
    have hleft :
        (↑g⁻¹ : Matrix I I F)ᵀ * (↑g : Matrix I I F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul]
      simp
    have hright :
        (↑g : Matrix I I F) * (↑g⁻¹ : Matrix I I F) = 1 := by
      simp
    calc
      (↑g⁻¹ : Matrix I I F)ᵀ * J0 * (↑g⁻¹ : Matrix I I F) =
          (↑g⁻¹ : Matrix I I F)ᵀ *
            ((↑g : Matrix I I F)ᵀ * J0 * (↑g : Matrix I I F)) *
              (↑g⁻¹ : Matrix I I F) := by rw [hg]
      _ = J0 := by
        simp only [mul_assoc]
        rw [hright, mul_one, ← mul_assoc, hleft, one_mul]

abbrev FormIsometryGroup (J0 : Matrix I I F) := formIsometrySubgroup J0

/-- An isometry of the left form gives an isometry of the tensor form. -/
def leftTensorIsometryHom (JI : Matrix I I F) (JJ : Matrix J J F) :
    FormIsometryGroup JI →* FormIsometryGroup (JI ⊗ₖ JJ) where
  toFun t := ⟨leftKroneckerHom (I := I) (J := J) t.1, by
    exact leftKronecker_preserves_tensorForm
      (↑t.1 : Matrix I I F) JI JJ t.2⟩
  map_one' := by ext; simp
  map_mul' t s := by ext; simp

omit [DecidableEq J] in
/-- The right-factor analogue of
`OddTwoWreathReflection.leftKronecker_preserves_tensorForm`. -/
theorem rightKronecker_preserves_tensorForm
    (e : Matrix J J F) (JI : Matrix I I F) (JJ : Matrix J J F)
    (he : eᵀ * JJ * e = JJ) :
    ((1 : Matrix I I F) ⊗ₖ e)ᵀ * (JI ⊗ₖ JJ) *
        ((1 : Matrix I I F) ⊗ₖ e) = JI ⊗ₖ JJ := by
  have hTranspose :
      ((1 : Matrix I I F) ⊗ₖ e)ᵀ =
        (1 : Matrix I I F) ⊗ₖ eᵀ := by
    rw [← Matrix.kroneckerMap_transpose]
    simp
  rw [hTranspose, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, he]
  simp

/-- An isometry of the right form gives an isometry of the tensor form. -/
def rightTensorIsometryHom (JI : Matrix I I F) (JJ : Matrix J J F) :
    FormIsometryGroup JJ →* FormIsometryGroup (JI ⊗ₖ JJ) where
  toFun e := ⟨rightKroneckerHom (I := I) (J := J) e.1, by
    exact rightKronecker_preserves_tensorForm
      (↑e.1 : Matrix J J F) JI JJ e.2⟩
  map_one' := by ext; simp
  map_mul' e d := by ext; simp

/-- The corrected quaternion factor inside the isometry group of the tensor
form. -/
def correctedIsometryBase
    (JI : Matrix I I F) (JJ : Matrix J J F)
    (E : Subgroup (FormIsometryGroup JJ)) :
    Subgroup (FormIsometryGroup (JI ⊗ₖ JJ)) :=
  E.map (rightTensorIsometryHom JI JJ)

/-- The form-preserving version of the literal corrected-factor bridge. -/
theorem leftIsometryReflection_involution_centralises_outside
    [Nonempty J] (JI : Matrix I I F) (JJ : Matrix J J F)
    (E : Subgroup (FormIsometryGroup JJ)) (t : FormIsometryGroup JI)
    (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ a : F,
      (↑t.1 : Matrix I I F) ≠ a • (1 : Matrix I I F)) :
    let T := leftTensorIsometryHom JI JJ t
    T ^ 2 = 1 ∧
      T ∈ Subgroup.centralizer
        (correctedIsometryBase JI JJ E :
          Set (FormIsometryGroup (JI ⊗ₖ JJ))) ∧
      T ∉ correctedIsometryBase JI JJ E := by
  dsimp only
  constructor
  · simpa using congrArg (leftTensorIsometryHom JI JJ) htSq
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    rcases he with ⟨e, he, rfl⟩
    apply Subtype.ext
    exact (leftKroneckerHom_commute_rightKroneckerHom t.1 e.1).symm
  · intro hmem
    rcases hmem with ⟨e, he, hEq⟩
    have hGL :
        leftKroneckerHom (I := I) (J := J) t.1 =
          rightKroneckerHom (I := I) (J := J) e.1 := by
      exact congrArg Subtype.val hEq.symm
    have hMatrix :
        (↑t.1 : Matrix I I F) ⊗ₖ (1 : Matrix J J F) =
          (1 : Matrix I I F) ⊗ₖ (↑e.1 : Matrix J J F) := by
      exact congrArg Units.val hGL
    obtain ⟨a, ha⟩ := leftKronecker_eq_rightKronecker_forces_scalar
      (↑t.1 : Matrix I I F) (↑e.1 : Matrix J J F) hMatrix
    exact htNonscalar a ha

end KroneckerFactor

section WreathAndAmbientRealisation

variable {F : Type u} {I : Type v} {J : Type w}
variable {A : Type x} {Omega : Type y} {K : Type z} {G : Type*}
variable [Field F]
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable [Group A] [Group K] [Group G] [Nonempty J] [Nonempty Omega]

abbrev CorrectedTensorGroup
    (JI : Matrix I I F) (JJ : Matrix J J F) :=
  FormIsometryGroup (JI ⊗ₖ JJ)

abbrev CorrectedWreathGroup
    (JI : Matrix I I F) (JJ : Matrix J J F)
    (rho : A →* Equiv.Perm Omega) :=
  PermutationWreathProduct (CorrectedTensorGroup JI JJ) rho

/-- The corrected base factor repeated over the coordinates and extended by
the source permutation group. -/
def correctedWreathSubgroup
    (JI : Matrix I I F) (JJ : Matrix J J F)
    (rho : A →* Equiv.Perm Omega)
    (E : Subgroup (FormIsometryGroup JJ)) :
    Subgroup (CorrectedWreathGroup JI JJ rho) :=
  PermutationWreathProduct.coefficientSubgroup
    (rho := rho) (correctedIsometryBase JI JJ E)

/-- The actual subgroup produced after adjoining all remaining direct factors
and applying the source block diagonal realisation. -/
def correctedAmbientSubgroup
    (JI : Matrix I I F) (JJ : Matrix J J F)
    (rho : A →* Equiv.Perm Omega)
    (E : Subgroup (FormIsometryGroup JJ))
    (C : Subgroup K)
    (f : (CorrectedWreathGroup JI JJ rho × K) →* G) :
    Subgroup G :=
  ((correctedWreathSubgroup JI JJ rho E).prod C).map f

/-- The constant left Kronecker reflection on all wreath coordinates,
extended by the identity on the remaining factors and mapped to the ambient
group. -/
def correctedAmbientReflection
    (JI : Matrix I I F) (JJ : Matrix J J F)
    (rho : A →* Equiv.Perm Omega)
    (f : (CorrectedWreathGroup JI JJ rho × K) →* G)
    (t : FormIsometryGroup JI) : G :=
  f (PermutationWreathProduct.constantCoordinate
      (rho := rho) (leftTensorIsometryHom JI JJ t), 1)

/-- The full tensor, wreath, remaining-factor, and injective-image bridge.
Only the source subgroup `E`, its permutation action, the remaining factors,
and the block diagonal realisation are parameters.  The involution,
centralisation, and nonmembership conclusions are proved. -/
theorem correctedAmbientReflection_involution_centralises_outside
    (JI : Matrix I I F) (JJ : Matrix J J F)
    (rho : A →* Equiv.Perm Omega)
    (E : Subgroup (FormIsometryGroup JJ))
    (C : Subgroup K)
    (f : (CorrectedWreathGroup JI JJ rho × K) →* G)
    (hf : Function.Injective f)
    (t : FormIsometryGroup JI) (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ a : F,
      (↑t.1 : Matrix I I F) ≠ a • (1 : Matrix I I F)) :
    let R := correctedAmbientSubgroup JI JJ rho E C f
    let T := correctedAmbientReflection JI JJ rho f t
    T ^ 2 = 1 ∧
      T ∈ Subgroup.centralizer (R : Set G) ∧ T ∉ R := by
  dsimp only [correctedAmbientReflection, correctedAmbientSubgroup,
    correctedWreathSubgroup]
  have hBase :=
    leftIsometryReflection_involution_centralises_outside
      JI JJ E t htSq htNonscalar
  have hWreath :=
    PermutationWreathProduct.constantCoordinate_involution_centralises_outside
      (rho := rho) (correctedIsometryBase JI JJ E)
        hBase.1 hBase.2.1 hBase.2.2
  have hProd := prod_involution_centralises_outside
    (PermutationWreathProduct.coefficientSubgroup
      (rho := rho) (correctedIsometryBase JI JJ E))
    C hWreath.1 hWreath.2.1 hWreath.2.2
  exact map_involution_centralises_outside_of_injective
    f hf _ hProd.1 hProd.2.1 hProd.2.2

/-- The source-shaped endpoint for the principal-block exclusion.

Feng--Yu--Zhang's principal-weight criterion is represented only by the
statement that the literal copy of `Z(R)` is Sylow in the literal centraliser
of the constructed subgroup `R`.  Lean constructs the excluding reflection
and the larger `2`-subgroup. -/
theorem corrected_even_multiplicity_factor_not_principal
    (JI : Matrix I I F) (JJ : Matrix J J F)
    (rho : A →* Equiv.Perm Omega)
    (E : Subgroup (FormIsometryGroup JJ))
    (C : Subgroup K)
    (f : (CorrectedWreathGroup JI JJ rho × K) →* G)
    (hf : Function.Injective f)
    (t : FormIsometryGroup JI) (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ a : F,
      (↑t.1 : Matrix I I F) ≠ a • (1 : Matrix I I F))
    (IsPrincipalWeight : Prop)
    (principalCentreSylow : IsPrincipalWeight →
      let R := correctedAmbientSubgroup JI JJ rho E C f
      ∃ P : Sylow 2 (Subgroup.centralizer (R : Set G)),
        (P : Subgroup (Subgroup.centralizer (R : Set G))) =
          centreInCentralizer R) :
    ¬ IsPrincipalWeight := by
  intro hPrincipal
  let R := correctedAmbientSubgroup JI JJ rho E C f
  let T := correctedAmbientReflection JI JJ rho f t
  have hT := correctedAmbientReflection_involution_centralises_outside
    JI JJ rho E C f hf t htSq htNonscalar
  let X := geometryOfCentralisingInvolution R T hT.1 hT.2.1 hT.2.2
  let D : OddTwoProposition33Relative.EvenMultiplicityCandidateData Unit := {
    IsPrincipalWeight := fun _ ↦ IsPrincipalWeight
    geometry := fun _ ↦ X
    principalCentreSylow := fun _ _ ↦ by
      dsimp [X, geometryOfCentralisingInvolution]
      exact principalCentreSylow hPrincipal }
  exact OddTwoProposition33Relative.omitted_even_multiplicity_not_principal D ()
    hPrincipal

/-- The precise remaining source-identification contract.  To apply the
kernel-checked argument to a subgroup named in the literature, one must
identify that subgroup with the explicit form-preserving tensor, wreath, and
block diagonal construction above.  After this equality is supplied, no
reflection or larger `2`-subgroup is an input. -/
theorem source_identified_corrected_even_multiplicity_factor_not_principal
    (JI : Matrix I I F) (JJ : Matrix J J F)
    (rho : A →* Equiv.Perm Omega)
    (E : Subgroup (FormIsometryGroup JJ))
    (C : Subgroup K)
    (f : (CorrectedWreathGroup JI JJ rho × K) →* G)
    (hf : Function.Injective f)
    (t : FormIsometryGroup JI) (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ a : F,
      (↑t.1 : Matrix I I F) ≠ a • (1 : Matrix I I F))
    (Rsource : Subgroup G)
    (hR : Rsource = correctedAmbientSubgroup JI JJ rho E C f)
    (IsPrincipalWeight : Prop)
    (principalCentreSylow : IsPrincipalWeight →
      ∃ P : Sylow 2 (Subgroup.centralizer (Rsource : Set G)),
        (P : Subgroup (Subgroup.centralizer (Rsource : Set G))) =
          centreInCentralizer Rsource) :
    ¬ IsPrincipalWeight := by
  subst Rsource
  exact corrected_even_multiplicity_factor_not_principal
    JI JJ rho E C f hf t htSq htNonscalar IsPrincipalWeight
      principalCentreSylow

end WreathAndAmbientRealisation

end ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
