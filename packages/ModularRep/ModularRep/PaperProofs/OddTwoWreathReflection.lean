import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The wreath-product reflection used in manuscript Proposition 3.3

This file contains the group-theoretic calculation behind the corrected
even-multiplicity factor in the proof of `prop:odd-two`.  It does not construct
the orthogonal reflection or identify the abstract wreath product below with a
particular subgroup of a finite symplectic group.  Those are respectively a
routine geometric source fact and a source-specific realisation of the
Feng--Yu--Zhang corrected factor.

The kernel-checked part is the following.  An involution which centralises but
does not belong to a coefficient subgroup gives a constant-coordinate
involution which centralises but does not belong to the corresponding
permutation wreath subgroup.  A separate constructor packages an involution
of an ambient group as an element of the actual centraliser and identifies the
copy of the subgroup centre inside that centraliser.
-/

namespace ModularRep.PaperProofs.OddTwoWreathReflection

universe u v w x y

section CentralizerGeometry

variable {G : Type u} [Group G]

/-- The copy of `Z(R)` inside `C_G(R)`, expressed without choosing a separate
embedding.  Its elements are precisely the elements of `R` which centralise
all of `R`. -/
def centreInCentralizer (R : Subgroup G) :
    Subgroup (Subgroup.centralizer (R : Set G)) :=
  R.comap (Subgroup.centralizer (R : Set G)).subtype

/-- The centraliser data consumed by the Sylow obstruction in Proposition 3.3. -/
structure CentralizerReflectionGeometry where
  CentralizerGroup : Type u
  group : Group CentralizerGroup
  centre : @Subgroup CentralizerGroup group
  reflection : CentralizerGroup
  reflection_sq : reflection ^ 2 = 1
  reflection_centralises_centre :
    reflection ∈ @Subgroup.centralizer CentralizerGroup group
      (centre : Set CentralizerGroup)
  reflection_outside_centre : reflection ∉ centre

/-- Package an involution of `G` which centralises but does not belong to `R`
as reflection geometry inside the actual centraliser `C_G(R)`.

No centralisation or nonmembership assertion about the packed centraliser is
assumed: both are deduced from the two ambient membership statements. -/
def geometryOfCentralisingInvolution
    (R : Subgroup G) (t : G)
    (htSq : t ^ 2 = 1)
    (htCentral : t ∈ Subgroup.centralizer (R : Set G))
    (htOutside : t ∉ R) : CentralizerReflectionGeometry where
  CentralizerGroup := Subgroup.centralizer (R : Set G)
  group := inferInstance
  centre := centreInCentralizer R
  reflection := ⟨t, htCentral⟩
  reflection_sq := by
    apply Subtype.ext
    exact htSq
  reflection_centralises_centre := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact htCentral z.1 (show z.1 ∈ R from hz)
  reflection_outside_centre := by
    intro ht
    exact htOutside ht

/-- An injective homomorphism transfers an involution, its centralisation of a
subgroup, and its nonmembership to the image subgroup. -/
theorem map_involution_centralises_outside_of_injective
    {H : Type v} [Group H]
    (f : H →* G) (hf : Function.Injective f)
    (B : Subgroup H) {t : H}
    (htSq : t ^ 2 = 1)
    (htCentral : t ∈ Subgroup.centralizer (B : Set H))
    (htOutside : t ∉ B) :
    (f t) ^ 2 = 1 ∧
      f t ∈ Subgroup.centralizer (B.map f : Set G) ∧
      f t ∉ B.map f := by
  constructor
  · simpa using congrArg f htSq
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    simpa using congrArg f (htCentral b hb)
  · intro hmem
    rcases hmem with ⟨b, hb, hbt⟩
    have : b = t := hf hbt
    exact htOutside (this ▸ hb)

/-- Extending an involution by the identity on another direct factor
preserves its order, centralisation, and nonmembership properties. -/
theorem prod_involution_centralises_outside
    {H : Type v} {K : Type w} [Group H] [Group K]
    (B : Subgroup H) (C : Subgroup K) {t : H}
    (htSq : t ^ 2 = 1)
    (htCentral : t ∈ Subgroup.centralizer (B : Set H))
    (htOutside : t ∉ B) :
    (t, (1 : K)) ^ 2 = 1 ∧
      (t, (1 : K)) ∈ Subgroup.centralizer (B.prod C : Set (H × K)) ∧
      (t, (1 : K)) ∉ B.prod C := by
  constructor
  · ext
    · exact htSq
    · simp
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases z with ⟨b, c⟩
    rcases hz with ⟨hb, hc⟩
    ext
    · exact htCentral b hb
    · simp
  · intro hmem
    exact htOutside hmem.1

end CentralizerGeometry

section TensorCalculation

open Matrix
open scoped Kronecker

variable {F : Type u} [Field F]
variable {I : Type v} {J : Type w}
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] in
/-- Equality between a left and a right Kronecker factor forces the left
factor to be scalar.  Only one diagonal coordinate in the right factor is
used. -/
theorem leftKronecker_eq_rightKronecker_forces_scalar
    [Nonempty J] (t : Matrix I I F) (e : Matrix J J F)
    (h : t ⊗ₖ (1 : Matrix J J F) =
      (1 : Matrix I I F) ⊗ₖ e) :
    ∃ a : F, t = a • (1 : Matrix I I F) := by
  classical
  let j : J := Classical.choice inferInstance
  refine ⟨e j j, ?_⟩
  ext i k
  have hEntry := congrArg (fun M ↦ M (i, j) (k, j)) h
  simpa [Matrix.kronecker_apply, mul_comm] using hEntry

omit [DecidableEq I] in
/-- An isometry of the left form tensored with the identity preserves the
tensor-product form.  In the manuscript the left form is orthogonal and the
right form is alternating. -/
theorem leftKronecker_preserves_tensorForm
    (t JI : Matrix I I F) (JJ : Matrix J J F)
    (ht : tᵀ * JI * t = JI) :
    (t ⊗ₖ (1 : Matrix J J F))ᵀ * (JI ⊗ₖ JJ) *
        (t ⊗ₖ (1 : Matrix J J F)) = JI ⊗ₖ JJ := by
  have hTranspose :
      (t ⊗ₖ (1 : Matrix J J F))ᵀ =
        tᵀ ⊗ₖ (1 : Matrix J J F) := by
    rw [← Matrix.kroneckerMap_transpose]
    simp
  rw [hTranspose, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ht]
  simp

/-- The tensor element `t ⊗ 1` is an involution, commutes with every
right-factor element `1 ⊗ e`, and is distinct from all such elements when
`t` is nonscalar.  These are the finite-matrix identities used before the
permutation-wreath argument in Proposition 3.3. -/
theorem leftKronecker_involution_commutes_and_ne_rightKronecker
    [Nonempty J] (t : Matrix I I F)
    (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ a : F, t ≠ a • (1 : Matrix I I F)) :
    (t ⊗ₖ (1 : Matrix J J F)) ^ 2 = 1 ∧
      ∀ e : Matrix J J F,
        (t ⊗ₖ (1 : Matrix J J F)) *
            ((1 : Matrix I I F) ⊗ₖ e) =
          ((1 : Matrix I I F) ⊗ₖ e) *
            (t ⊗ₖ (1 : Matrix J J F)) ∧
        t ⊗ₖ (1 : Matrix J J F) ≠
          (1 : Matrix I I F) ⊗ₖ e := by
  have htt : t * t = 1 := by
    simpa [pow_two] using htSq
  constructor
  · rw [pow_two, ← Matrix.mul_kronecker_mul, htt]
    simp
  intro e
  constructor
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  · intro hEq
    obtain ⟨a, ha⟩ :=
      leftKronecker_eq_rightKronecker_forces_scalar t e hEq
    exact htNonscalar a ha

end TensorCalculation

section PermutationWreath

variable {H : Type u} {A : Type v} {Omega : Type w}
variable [Group H] [Group A]

/-- The permutation wreath product `(Omega → H) ⋊ A` associated with a
permutation representation `rho : A → Perm(Omega)`.

We use the equivalent right-action convention
`(f,a)(g,b) = (f^b g,ab)`, where `f^b(omega)=f(rho(b)(omega))`.
Constant coordinate functions are fixed by the permutation factor. -/
@[ext]
structure PermutationWreathProduct (H : Type u)
    (rho : A →* Equiv.Perm Omega) where
  left : Omega → H
  right : A

namespace PermutationWreathProduct

variable {rho : A →* Equiv.Perm Omega}

instance : Mul (PermutationWreathProduct H rho) where
  mul x y :=
    ⟨fun omega ↦ x.left ((rho y.right) omega) * y.left omega,
      x.right * y.right⟩

@[simp]
theorem mul_left (x y : PermutationWreathProduct H rho) (omega : Omega) :
    (x * y).left omega =
      x.left ((rho y.right) omega) * y.left omega := rfl

@[simp]
theorem mul_right (x y : PermutationWreathProduct H rho) :
    (x * y).right = x.right * y.right := rfl

instance : One (PermutationWreathProduct H rho) where
  one := ⟨1, 1⟩

@[simp]
theorem one_left (omega : Omega) :
    (1 : PermutationWreathProduct H rho).left omega = 1 := rfl

@[simp]
theorem one_right : (1 : PermutationWreathProduct H rho).right = 1 := rfl

instance : Inv (PermutationWreathProduct H rho) where
  inv x :=
    ⟨fun omega ↦ (x.left ((rho x.right⁻¹) omega))⁻¹, x.right⁻¹⟩

@[simp]
theorem inv_left (x : PermutationWreathProduct H rho) (omega : Omega) :
    x⁻¹.left omega = (x.left ((rho x.right⁻¹) omega))⁻¹ := rfl

@[simp]
theorem inv_right (x : PermutationWreathProduct H rho) :
    x⁻¹.right = x.right⁻¹ := rfl

instance : Group (PermutationWreathProduct H rho) where
  mul_assoc x y z := by
    ext omega <;> simp [mul_assoc]
  one_mul x := by
    ext omega <;> simp
  mul_one x := by
    ext omega <;> simp
  inv_mul_cancel x := by
    ext omega <;> simp

/-- The subgroup whose coordinate entries lie in `B`; its permutation
coordinate is unrestricted.  This is the honest subgroup `B^Omega ⋊ A` of
`H^Omega ⋊ A`. -/
def coefficientSubgroup (B : Subgroup H) :
    Subgroup (PermutationWreathProduct H rho) where
  carrier := {x | ∀ omega, x.left omega ∈ B}
  one_mem' _ := B.one_mem
  mul_mem' hx hy omega :=
    B.mul_mem (hx ((rho _) omega)) (hy omega)
  inv_mem' hx omega := B.inv_mem (hx ((rho _) omega))

@[simp]
theorem mem_coefficientSubgroup_iff
    (B : Subgroup H) (x : PermutationWreathProduct H rho) :
    x ∈ coefficientSubgroup B ↔ ∀ omega, x.left omega ∈ B := Iff.rfl

/-- The constant-coordinate element with trivial permutation coordinate. -/
def constantCoordinate (t : H) : PermutationWreathProduct H rho :=
  ⟨fun _ ↦ t, 1⟩

omit [Group H] in
@[simp]
theorem constantCoordinate_left (t : H) (omega : Omega) :
    (constantCoordinate (rho := rho) t).left omega = t := rfl

omit [Group H] in
@[simp]
theorem constantCoordinate_right (t : H) :
    (constantCoordinate (rho := rho) t).right = 1 := rfl

/-- A base involution which centralises but lies outside `B` gives a
constant-coordinate involution with the same two properties for the full
permutation wreath subgroup. -/
theorem constantCoordinate_involution_centralises_outside
    [Nonempty Omega] (B : Subgroup H) {t : H}
    (htSq : t ^ 2 = 1)
    (htCentral : t ∈ Subgroup.centralizer (B : Set H))
    (htOutside : t ∉ B) :
    let T := constantCoordinate (rho := rho) t
    T ^ 2 = 1 ∧
      T ∈ Subgroup.centralizer (coefficientSubgroup (rho := rho) B :
        Set (PermutationWreathProduct H rho)) ∧
      T ∉ coefficientSubgroup (rho := rho) B := by
  dsimp only
  constructor
  · apply PermutationWreathProduct.ext
    · funext omega
      simpa [pow_two] using htSq
    · simp [pow_two]
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply PermutationWreathProduct.ext
    · funext omega
      simpa using htCentral (x.left omega) (hx omega)
    · simp
  · intro hmem
    let omega : Omega := Classical.choice inferInstance
    exact htOutside (hmem omega)

/-- Construct the centraliser geometry of the constant-coordinate element
directly from the base involution.  The three wreath conclusions are supplied
by `constantCoordinate_involution_centralises_outside`, rather than repeated
as premises of this constructor. -/
def geometryOfConstantCoordinateInvolution
    [Nonempty Omega] (B : Subgroup H) (t : H)
    (htSq : t ^ 2 = 1)
    (htCentral : t ∈ Subgroup.centralizer (B : Set H))
    (htOutside : t ∉ B) : CentralizerReflectionGeometry := by
  let T := constantCoordinate (rho := rho) t
  have h := constantCoordinate_involution_centralises_outside
    (rho := rho) B htSq htCentral htOutside
  exact geometryOfCentralisingInvolution
    (coefficientSubgroup (rho := rho) B) T h.1 h.2.1 h.2.2

/-- Map the constant-coordinate wreath reflection through an injective
homomorphism and construct its centraliser geometry in the target group.  Thus
an application to the corrected factor needs only the concrete injective
block-matrix realisation and the equality identifying its image. -/
def geometryOfMappedConstantCoordinateInvolution
    {G : Type x} [Group G] [Nonempty Omega]
    (f : PermutationWreathProduct H rho →* G)
    (hf : Function.Injective f)
    (B : Subgroup H) (t : H)
    (htSq : t ^ 2 = 1)
    (htCentral : t ∈ Subgroup.centralizer (B : Set H))
    (htOutside : t ∉ B) : CentralizerReflectionGeometry := by
  let T := constantCoordinate (rho := rho) t
  let R := coefficientSubgroup (rho := rho) B
  have hWreath := constantCoordinate_involution_centralises_outside
    (rho := rho) B htSq htCentral htOutside
  have hMap := map_involution_centralises_outside_of_injective
    f hf R hWreath.1 hWreath.2.1 hWreath.2.2
  exact geometryOfCentralisingInvolution
    (R.map f) (f T) hMap.1 hMap.2.1 hMap.2.2

/-- Extend the constant-coordinate reflection by the identity on all
remaining factors, map the resulting direct product injectively into the
ambient group, and construct the target centraliser geometry. -/
def geometryOfMappedConstantCoordinateInvolutionWithRest
    {K : Type y} {G : Type x} [Group K] [Group G] [Nonempty Omega]
    (C : Subgroup K)
    (f : (PermutationWreathProduct H rho × K) →* G)
    (hf : Function.Injective f)
    (B : Subgroup H) (t : H)
    (htSq : t ^ 2 = 1)
    (htCentral : t ∈ Subgroup.centralizer (B : Set H))
    (htOutside : t ∉ B) : CentralizerReflectionGeometry := by
  let T := constantCoordinate (rho := rho) t
  let R := coefficientSubgroup (rho := rho) B
  have hWreath := constantCoordinate_involution_centralises_outside
    (rho := rho) B htSq htCentral htOutside
  have hProd := prod_involution_centralises_outside
    R C hWreath.1 hWreath.2.1 hWreath.2.2
  have hMap := map_involution_centralises_outside_of_injective
    f hf (R.prod C) hProd.1 hProd.2.1 hProd.2.2
  exact geometryOfCentralisingInvolution
    ((R.prod C).map f) (f (T, 1)) hMap.1 hMap.2.1 hMap.2.2

end PermutationWreathProduct

end PermutationWreath

end ModularRep.PaperProofs.OddTwoWreathReflection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
