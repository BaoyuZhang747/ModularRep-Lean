import ModularRep.PaperProofs.OddTwoSourceWreathAction
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Ambient realisation of the corrected odd characteristic factor

This file replaces the arbitrary ambient homomorphism in the earlier
Proposition 3.3 adapter by literal finite matrices.  It constructs the
block-monomial representation of the source permutation wreath product,
proves that it is faithful and preserves the repeated tensor form, and
extends it by an injective orthogonal block sum on all remaining factors.

The left diagonal reflection is written explicitly.  Its existence and its
interpretation as a reflection of a negative orthogonal multiplicity space
are routine E1 geometry and receive no manuscript-specific credit.  The
manuscript-specific endpoint instead uses only the proved ambient image and
transports the centralising involution to any conjugate source
representative.  This matches the classification literature, which fixes
the radical subgroup only up to conjugacy, rather than demanding equality
with an arbitrary matrix representative.

The source-shaped endpoint is parameterised by the right tensor factor.
This is essential because the source permits two isometry-group conjugacy
classes for the relevant `E_-` factor in some dimensions.  For even
multiplicity, equation (3.35) uses the source-labelled `alpha = 0` right
factor to define a full factor carrying index `alpha = 1`.  The
noncomputably chosen quaternion matrices below have not been proved to
represent that `alpha = 0` class.  The endpoint therefore still
requires two exact source adapters: the assertion that the named
Feng--Yu--Zhang subgroup, with the correct source class supplied as a
parameter, is conjugate to the constructed standard image, and the
principal-weight statement identifying its centre as a Sylow `2`-subgroup
of its centraliser.  It assumes no BAW-goodness or iBAW conclusion and does
not address the remaining local character or block label comparison.
-/

namespace ModularRep.PaperProofs.OddTwoAmbientRealisation


open Matrix
open scoped Kronecker
open ModularRep.PaperProofs.OddTwoWreathReflection
open ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter
open ModularRep.PaperProofs.OddTwoQuaternionFactor
open ModularRep.PaperProofs.OddTwoSourceWreathAction

universe u v w x

variable {F : Type u} {V : Type v} {A : Type w} {Omega : Type x}
variable [Field F] [Fintype V] [DecidableEq V]
variable [Fintype Omega] [DecidableEq Omega]
variable [Group A]

def isometryMatrix (J : Matrix V V F) (h : FormIsometryGroup J) : Matrix V V F :=
  ↑h.1

@[simp] theorem isometryMatrix_one (J : Matrix V V F) :
    isometryMatrix J (1 : FormIsometryGroup J) = 1 := rfl

@[simp] theorem isometryMatrix_mul (J : Matrix V V F)
    (g h : FormIsometryGroup J) :
    isometryMatrix J (g * h) = isometryMatrix J g * isometryMatrix J h := rfl

def wreathMatrix
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (x : PermutationWreathProduct (FormIsometryGroup J) rho) :
    Matrix (V × Omega) (V × Omega) F :=
  fun r c ↦ if r.2 = rho x.right c.2 then
    isometryMatrix J (x.left c.2) r.1 c.1 else 0

omit [Fintype Omega] in
@[simp] theorem wreathMatrix_one
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega) :
    wreathMatrix J rho (1 : PermutationWreathProduct (FormIsometryGroup J) rho) = 1 := by
  ext r c
  rcases r with ⟨i, ω⟩
  rcases c with ⟨j, τ⟩
  by_cases h : ω = τ
  · subst τ
    simp [wreathMatrix, Matrix.one_apply]
  · simp [wreathMatrix, h]

theorem wreathMatrix_mul
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (x y : PermutationWreathProduct (FormIsometryGroup J) rho) :
    wreathMatrix J rho (x * y) = wreathMatrix J rho x * wreathMatrix J rho y := by
  ext r c
  rcases r with ⟨i, ω⟩
  rcases c with ⟨k, τ⟩
  simp only [wreathMatrix, PermutationWreathProduct.mul_left,
    PermutationWreathProduct.mul_right, map_mul, isometryMatrix_mul, Matrix.mul_apply,
    ← Finset.univ_product_univ, Finset.sum_product]
  by_cases h : ω = rho (x.right * y.right) τ
  · have hxy : ω = (rho x.right * rho y.right) τ := by simpa using h
    rw [if_pos hxy]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single (rho y.right τ)]
    · simp [hxy]
    · intro σ _ hne
      have hne' : ω ≠ rho x.right σ := by
        intro heq
        apply hne
        apply (rho x.right).injective
        rw [← heq, h, map_mul]
        rfl
      simp [hne, hne']
    · simp
  · have hxy : ω ≠ (rho x.right * rho y.right) τ := by simpa using h
    rw [if_neg hxy]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro σ _
    by_cases hσ : σ = rho y.right τ
    · subst σ
      have : ω ≠ rho x.right (rho y.right τ) := by
        simpa [map_mul] using h
      simp [this]
    · simp [hσ]

noncomputable def wreathGL
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (x : PermutationWreathProduct (FormIsometryGroup J) rho) :
    GL (V × Omega) F where
  val := wreathMatrix J rho x
  inv := wreathMatrix J rho x⁻¹
  val_inv := by rw [← wreathMatrix_mul]; simp
  inv_val := by rw [← wreathMatrix_mul]; simp

@[simp] theorem wreathGL_coe
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (x : PermutationWreathProduct (FormIsometryGroup J) rho) :
    ↑(wreathGL J rho x) = wreathMatrix J rho x := rfl

noncomputable def wreathGLHom
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega) :
    PermutationWreathProduct (FormIsometryGroup J) rho →* GL (V × Omega) F where
  toFun := wreathGL J rho
  map_one' := by apply Units.ext; simp
  map_mul' x y := by
    apply Units.ext
    exact wreathMatrix_mul J rho x y

theorem wreathGLHom_injective
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (hrho : Function.Injective rho) [Nonempty V] :
    Function.Injective (wreathGLHom J rho) := by
  intro x y hxy
  have hMatrix : wreathMatrix J rho x = wreathMatrix J rho y := by
    exact congrArg Units.val hxy
  have hRightPerm : rho x.right = rho y.right := by
    ext ω
    have hnonzero : isometryMatrix J (x.left ω) ≠ 0 := by
      exact Units.ne_zero (x.left ω).1
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hnonzero
    obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
    by_contra hne
    have hEntry := congrArg
      (fun M ↦ M (i, rho x.right ω) (j, ω)) hMatrix
    simp [wreathMatrix, hne] at hEntry
    have hij' : isometryMatrix J (x.left ω) i j ≠ 0 := by simpa using hij
    exact hij' hEntry
  have hRight : x.right = y.right := hrho hRightPerm
  apply PermutationWreathProduct.ext
  · funext ω
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    have hEntry := congrArg
      (fun M ↦ M (i, rho x.right ω) (j, ω)) hMatrix
    change isometryMatrix J (x.left ω) i j =
      isometryMatrix J (y.left ω) i j
    simpa [wreathMatrix, hRight] using hEntry
  · exact hRight

def liftedCoordinatePerm (sigma : Equiv.Perm Omega) : Equiv.Perm (V × Omega) :=
  Equiv.prodCongr (Equiv.refl V) sigma

def coordinatePermMatrix (sigma : Equiv.Perm Omega) :
    Matrix (V × Omega) (V × Omega) F :=
  ((liftedCoordinatePerm (V := V) sigma)⁻¹).permMatrix F

def coefficientBlockMatrix (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (x : PermutationWreathProduct (FormIsometryGroup J) rho) :
    Matrix (V × Omega) (V × Omega) F :=
  Matrix.blockDiagonal (fun ω ↦ isometryMatrix J (x.left ω))

theorem wreathMatrix_eq_coordinatePerm_mul_coefficient
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (x : PermutationWreathProduct (FormIsometryGroup J) rho) :
    wreathMatrix J rho x =
      coordinatePermMatrix (V := V) (F := F) (rho x.right) *
        coefficientBlockMatrix J rho x := by
  rw [coordinatePermMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]
  ext r c
  rcases r with ⟨i, ω⟩
  rcases c with ⟨j, τ⟩
  simp only [Matrix.submatrix_apply, coefficientBlockMatrix,
    Matrix.blockDiagonal_apply, liftedCoordinatePerm]
  by_cases h : ω = rho x.right τ
  · subst ω
    simp [wreathMatrix]
  · have h' : (rho x.right).symm ω ≠ τ := by
      intro heq
      apply h
      calc
        ω = rho x.right ((rho x.right).symm ω) := by simp
        _ = rho x.right τ := congrArg (rho x.right) heq
    simp [wreathMatrix, h, h']

def repeatedGram (J : Matrix V V F) :
    Matrix (V × Omega) (V × Omega) F :=
  Matrix.blockDiagonal (fun _ : Omega ↦ J)

theorem coefficientBlockMatrix_preserves
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (x : PermutationWreathProduct (FormIsometryGroup J) rho) :
    (coefficientBlockMatrix J rho x)ᵀ * repeatedGram (Omega := Omega) J *
        coefficientBlockMatrix J rho x = repeatedGram (Omega := Omega) J := by
  rw [coefficientBlockMatrix, repeatedGram, Matrix.blockDiagonal_transpose,
    ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
  congr 1
  funext ω
  exact (x.left ω).2

theorem coordinatePermMatrix_preserves_repeatedGram
    (J : Matrix V V F) (sigma : Equiv.Perm Omega) :
    (coordinatePermMatrix (V := V) (F := F) sigma)ᵀ *
        repeatedGram (Omega := Omega) J *
      coordinatePermMatrix (V := V) (F := F) sigma =
        repeatedGram (Omega := Omega) J := by
  rw [coordinatePermMatrix, Matrix.transpose_permMatrix]
  simp only [inv_inv]
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rw [show ((liftedCoordinatePerm (V := V) sigma)⁻¹).symm =
      liftedCoordinatePerm (V := V) sigma by rfl]
  ext r c
  rcases r with ⟨i, ω⟩
  rcases c with ⟨j, τ⟩
  simp [repeatedGram, Matrix.blockDiagonal_apply, liftedCoordinatePerm]

theorem wreathMatrix_preserves_repeatedGram
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (x : PermutationWreathProduct (FormIsometryGroup J) rho) :
    (wreathMatrix J rho x)ᵀ * repeatedGram (Omega := Omega) J *
        wreathMatrix J rho x = repeatedGram (Omega := Omega) J := by
  rw [wreathMatrix_eq_coordinatePerm_mul_coefficient]
  rw [Matrix.transpose_mul]
  calc
    (coefficientBlockMatrix J rho x)ᵀ *
          (coordinatePermMatrix (V := V) (F := F) (rho x.right))ᵀ *
          repeatedGram (Omega := Omega) J *
          (coordinatePermMatrix (V := V) (F := F) (rho x.right) *
            coefficientBlockMatrix J rho x) =
        (coefficientBlockMatrix J rho x)ᵀ *
          ((coordinatePermMatrix (V := V) (F := F) (rho x.right))ᵀ *
            repeatedGram (Omega := Omega) J *
            coordinatePermMatrix (V := V) (F := F) (rho x.right)) *
          coefficientBlockMatrix J rho x := by
            simp only [mul_assoc]
    _ = (coefficientBlockMatrix J rho x)ᵀ *
          repeatedGram (Omega := Omega) J *
          coefficientBlockMatrix J rho x := by
            rw [coordinatePermMatrix_preserves_repeatedGram]
    _ = repeatedGram (Omega := Omega) J :=
      coefficientBlockMatrix_preserves J rho x

noncomputable def wreathIsometryHom
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega) :
    PermutationWreathProduct (FormIsometryGroup J) rho →*
      FormIsometryGroup (repeatedGram (Omega := Omega) J) where
  toFun x := ⟨wreathGL J rho x, wreathMatrix_preserves_repeatedGram J rho x⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact wreathMatrix_one J rho
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact wreathMatrix_mul J rho x y

theorem wreathIsometryHom_injective
    (J : Matrix V V F) (rho : A →* Equiv.Perm Omega)
    (hrho : Function.Injective rho) [Nonempty V] :
    Function.Injective (wreathIsometryHom J rho) := by
  intro x y hxy
  apply wreathGLHom_injective J rho hrho
  exact congrArg Subtype.val hxy

section ExplicitReflection

variable (n : ℕ)

def reflectionSign (i : Fin (n + 2)) : F := if i = 0 then -1 else 1

def coordinateReflectionMatrix : Matrix (Fin (n + 2)) (Fin (n + 2)) F :=
  Matrix.diagonal (reflectionSign (F := F) n)

theorem coordinateReflectionMatrix_sq :
    coordinateReflectionMatrix (F := F) n * coordinateReflectionMatrix n = 1 := by
  rw [coordinateReflectionMatrix, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp [reflectionSign]
  · simp [reflectionSign, hi]

noncomputable def coordinateReflectionGL : GL (Fin (n + 2)) F where
  val := coordinateReflectionMatrix n
  inv := coordinateReflectionMatrix n
  val_inv := coordinateReflectionMatrix_sq n
  inv_val := coordinateReflectionMatrix_sq n

@[simp] theorem coordinateReflectionGL_coe :
    ↑(coordinateReflectionGL (F := F) n) =
      coordinateReflectionMatrix (F := F) n := rfl

def diagonalGram (d : Fin (n + 2) → F) : Matrix (Fin (n + 2)) (Fin (n + 2)) F :=
  Matrix.diagonal d

theorem coordinateReflectionMatrix_transpose :
    (coordinateReflectionMatrix (F := F) n)ᵀ = coordinateReflectionMatrix n := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [coordinateReflectionMatrix, Matrix.transpose_apply]
  · simp [coordinateReflectionMatrix, Matrix.transpose_apply, h, Ne.symm h]

theorem coordinateReflection_preserves_diagonalGram
    (d : Fin (n + 2) → F) :
    (coordinateReflectionMatrix (F := F) n)ᵀ * diagonalGram n d *
        coordinateReflectionMatrix n = diagonalGram n d := by
  rw [coordinateReflectionMatrix_transpose, coordinateReflectionMatrix, diagonalGram,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp [reflectionSign]
  · simp [reflectionSign, hi]

noncomputable def diagonalFormReflection (d : Fin (n + 2) → F) :
    FormIsometryGroup (diagonalGram n d) :=
  ⟨coordinateReflectionGL (F := F) n,
    coordinateReflection_preserves_diagonalGram n d⟩

theorem diagonalFormReflection_sq (d : Fin (n + 2) → F) :
    diagonalFormReflection n d ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change coordinateReflectionMatrix (F := F) n ^ 2 = 1
  simpa [pow_two] using coordinateReflectionMatrix_sq (F := F) n

theorem diagonalFormReflection_nonscalar (hTwo : (2 : F) ≠ 0)
    (d : Fin (n + 2) → F) (a : F) :
    (↑(diagonalFormReflection n d).1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) ≠
      a • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) := by
  intro h
  have h00 := congrArg (fun M ↦ M (0 : Fin (n + 2)) 0) h
  have h11 := congrArg (fun M ↦ M (1 : Fin (n + 2)) 1) h
  have haNeg : -1 = a := by
    simpa [diagonalFormReflection, coordinateReflectionGL,
      coordinateReflectionMatrix, reflectionSign] using h00
  have haOne : 1 = a := by
    simpa [diagonalFormReflection, coordinateReflectionGL,
      coordinateReflectionMatrix, reflectionSign] using h11
  apply hTwo
  have honeNeg : (1 : F) = -1 := haOne.trans haNeg.symm
  calc
    (2 : F) = 1 + 1 := by norm_num
    _ = -1 + 1 := congrArg (fun x : F ↦ x + 1) honeNeg
    _ = 0 := by simp

end ExplicitReflection

section OrthogonalBlockSum

variable {W : Type*} [Fintype W] [DecidableEq W]

def orthogonalSumGram (J : Matrix V V F) (K : Matrix W W F) :
    Matrix (V ⊕ W) (V ⊕ W) F :=
  Matrix.fromBlocks J 0 0 K

def twoBlockDiagonalMatrix (g : GL V F) (h : GL W F) :
    Matrix (V ⊕ W) (V ⊕ W) F :=
  Matrix.fromBlocks (↑g : Matrix V V F) 0 0 (↑h : Matrix W W F)

theorem twoBlockDiagonalMatrix_mul (g g' : GL V F) (h h' : GL W F) :
    twoBlockDiagonalMatrix (g * g') (h * h') =
      twoBlockDiagonalMatrix g h * twoBlockDiagonalMatrix g' h' := by
  simp [twoBlockDiagonalMatrix, Matrix.fromBlocks_multiply]

theorem twoBlockDiagonalMatrix_one :
    twoBlockDiagonalMatrix (1 : GL V F) (1 : GL W F) = 1 := by
  exact Matrix.fromBlocks_one

noncomputable def twoBlockDiagonalGL (g : GL V F) (h : GL W F) : GL (V ⊕ W) F where
  val := twoBlockDiagonalMatrix g h
  inv := twoBlockDiagonalMatrix g⁻¹ h⁻¹
  val_inv := by rw [← twoBlockDiagonalMatrix_mul]; simp [twoBlockDiagonalMatrix_one]
  inv_val := by rw [← twoBlockDiagonalMatrix_mul]; simp [twoBlockDiagonalMatrix_one]

@[simp] theorem twoBlockDiagonalGL_coe (g : GL V F) (h : GL W F) :
    ↑(twoBlockDiagonalGL g h) = twoBlockDiagonalMatrix g h := rfl

theorem twoBlockDiagonal_preserves
    (J : Matrix V V F) (K : Matrix W W F)
    (g : FormIsometryGroup J) (h : FormIsometryGroup K) :
    (twoBlockDiagonalMatrix g.1 h.1)ᵀ * orthogonalSumGram J K *
        twoBlockDiagonalMatrix g.1 h.1 = orthogonalSumGram J K := by
  rw [twoBlockDiagonalMatrix, orthogonalSumGram, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]
  rw [g.2, h.2]

noncomputable def orthogonalBlockSumHom
    (J : Matrix V V F) (K : Matrix W W F) :
    FormIsometryGroup J × FormIsometryGroup K →*
      FormIsometryGroup (orthogonalSumGram J K) where
  toFun gh := ⟨twoBlockDiagonalGL gh.1.1 gh.2.1,
    twoBlockDiagonal_preserves J K gh.1 gh.2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact twoBlockDiagonalMatrix_one
  map_mul' gh gh' := by
    apply Subtype.ext
    apply Units.ext
    exact twoBlockDiagonalMatrix_mul gh.1.1 gh'.1.1 gh.2.1 gh'.2.1

theorem orthogonalBlockSumHom_injective
    (J : Matrix V V F) (K : Matrix W W F) :
    Function.Injective (orthogonalBlockSumHom J K) := by
  intro gh gh' h
  rcases gh with ⟨g, k⟩
  rcases gh' with ⟨g', k'⟩
  have hMatrix : twoBlockDiagonalMatrix g.1 k.1 =
      twoBlockDiagonalMatrix g'.1 k'.1 := by
    exact congrArg (fun x ↦ (↑x.1 : Matrix (V ⊕ W) (V ⊕ W) F)) h
  have hgMatrix : (↑g.1 : Matrix V V F) = ↑g'.1 := by
    exact congrArg Matrix.toBlocks₁₁ hMatrix
  have hkMatrix : (↑k.1 : Matrix W W F) = ↑k'.1 := by
    exact congrArg Matrix.toBlocks₂₂ hMatrix
  have hg : g = g' := by
    apply Subtype.ext
    apply Units.ext
    exact hgMatrix
  have hk : k = k' := by
    apply Subtype.ext
    apply Units.ext
    exact hkMatrix
  simp [hg, hk]

end OrthogonalBlockSum

section CanonicalCorrectedSourceModel

variable [Finite F]

noncomputable local instance sourceWreathPointsFintype (cs : List ℕ) :
    Fintype (SourceWreathPoints cs) := Fintype.ofFinite _

noncomputable local instance sourceWreathPointsDecidableEq (cs : List ℕ) :
    DecidableEq (SourceWreathPoints cs) := Classical.decEq _

abbrev CorrectedTensorIndex (n : ℕ) := Fin (n + 2) × Fin 2

abbrev CorrectedRepeatedIndex (n : ℕ) (cs : List ℕ) :=
  CorrectedTensorIndex n × SourceWreathPoints cs

def correctedTensorGram (n : ℕ) (d : Fin (n + 2) → F) :
    Matrix (CorrectedTensorIndex n) (CorrectedTensorIndex n) F :=
  diagonalGram n d ⊗ₖ omega

noncomputable def correctedRepeatedGram (n : ℕ) (cs : List ℕ)
    (d : Fin (n + 2) → F) :
    Matrix (CorrectedRepeatedIndex n cs) (CorrectedRepeatedIndex n cs) F :=
  repeatedGram (Omega := SourceWreathPoints cs) (correctedTensorGram n d)

noncomputable def canonicalCorrectedWreathHom
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F) :
    CorrectedWreathGroup (diagonalGram n d) (omega (F := F))
        (sourceWreathAction cs) →*
      FormIsometryGroup (correctedRepeatedGram n cs d) := by
  exact wreathIsometryHom (correctedTensorGram n d) (sourceWreathAction cs)

omit [Finite F] in
theorem canonicalCorrectedWreathHom_injective
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F) :
    Function.Injective (canonicalCorrectedWreathHom n cs d) := by
  exact wreathIsometryHom_injective _ _ (sourceWreathAction_injective cs)

/-! The next definition leaves the right tensor factor as a parameter.  This
is the source-faithful form of the construction: choosing a group merely
isomorphic to `Q_8` does not determine which source conjugacy class it
represents. -/

noncomputable def correctedBasicSubgroupWithFactor
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (E : Subgroup (FormIsometryGroup (omega (F := F)))) :
    Subgroup (FormIsometryGroup (correctedRepeatedGram n cs d)) :=
  (correctedWreathSubgroup (diagonalGram n d) (omega (F := F))
      (sourceWreathAction cs) E).map
    (canonicalCorrectedWreathHom n cs d)

/-- A convenient explicit quaternion specialization.  No claim is made here
that this noncomputably chosen copy belongs to the source-labelled
`alpha = 0` conjugacy class used on the right in equation (3.35). -/
noncomputable def canonicalCorrectedBasicSubgroup
    (p : ℕ) [NeZero p] [CharP F p]
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F) :
    Subgroup (FormIsometryGroup (correctedRepeatedGram n cs d)) :=
  correctedBasicSubgroupWithFactor n cs d
    (canonicalQuaternionSubgroup (F := F) p)

noncomputable def canonicalCorrectedReflection
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F) :
    FormIsometryGroup (correctedRepeatedGram n cs d) :=
  canonicalCorrectedWreathHom n cs d
    (PermutationWreathProduct.constantCoordinate
      (rho := sourceWreathAction cs)
      (leftTensorIsometryHom (diagonalGram n d) (omega (F := F))
        (diagonalFormReflection n d)))

omit [Finite F] in
theorem correctedReflection_involution_centralises_outside_withFactor
    (hTwo : (2 : F) ≠ 0)
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (E : Subgroup (FormIsometryGroup (omega (F := F)))) :
    let R := correctedBasicSubgroupWithFactor n cs d E
    let T := canonicalCorrectedReflection n cs d
    T ^ 2 = 1 ∧ T ∈ Subgroup.centralizer (R : Set _) ∧ T ∉ R := by
  let t := diagonalFormReflection n d
  have hBase := leftIsometryReflection_involution_centralises_outside
    (diagonalGram n d) (omega (F := F)) E t
      (diagonalFormReflection_sq n d)
      (diagonalFormReflection_nonscalar n hTwo d)
  have hWreath :=
    PermutationWreathProduct.constantCoordinate_involution_centralises_outside
      (rho := sourceWreathAction cs)
      (correctedIsometryBase (diagonalGram n d) (omega (F := F)) E)
      hBase.1 hBase.2.1 hBase.2.2
  exact map_involution_centralises_outside_of_injective
    (canonicalCorrectedWreathHom n cs d)
    (canonicalCorrectedWreathHom_injective n cs d)
    (correctedWreathSubgroup (diagonalGram n d) (omega (F := F))
      (sourceWreathAction cs) E)
    hWreath.1 hWreath.2.1 hWreath.2.2

omit [Finite F] in
theorem canonicalCorrectedReflection_involution_centralises_outside
    (p : ℕ) [NeZero p] [CharP F p] (hp : ¬ p ∣ 2)
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F) :
    let R := canonicalCorrectedBasicSubgroup p n cs d
    let T := canonicalCorrectedReflection n cs d
    T ^ 2 = 1 ∧ T ∈ Subgroup.centralizer (R : Set _) ∧ T ∉ R := by
  exact correctedReflection_involution_centralises_outside_withFactor
    (two_ne_zero_of_charP p hp) n cs d
      (canonicalQuaternionSubgroup (F := F) p)

section RemainingOrthogonalFactors

variable {Rest : Type*} [Fintype Rest] [DecidableEq Rest]

noncomputable def correctedFullGram
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (K : Matrix Rest Rest F) :
    Matrix (CorrectedRepeatedIndex n cs ⊕ Rest)
      (CorrectedRepeatedIndex n cs ⊕ Rest) F :=
  orthogonalSumGram (correctedRepeatedGram n cs d) K

noncomputable def correctedFullSubgroupWithFactor
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (E : Subgroup (FormIsometryGroup (omega (F := F))))
    (K : Matrix Rest Rest F) (C : Subgroup (FormIsometryGroup K)) :
    Subgroup (FormIsometryGroup (correctedFullGram n cs d K)) :=
  ((correctedBasicSubgroupWithFactor n cs d E).prod C).map
    (orthogonalBlockSumHom (correctedRepeatedGram n cs d) K)

noncomputable def canonicalCorrectedFullSubgroup
    (p : ℕ) [NeZero p] [CharP F p]
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (K : Matrix Rest Rest F) (C : Subgroup (FormIsometryGroup K)) :
    Subgroup (FormIsometryGroup (correctedFullGram n cs d K)) :=
  correctedFullSubgroupWithFactor n cs d
    (canonicalQuaternionSubgroup (F := F) p) K C

noncomputable def canonicalCorrectedFullReflection
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (K : Matrix Rest Rest F) :
    FormIsometryGroup (correctedFullGram n cs d K) :=
  orthogonalBlockSumHom (correctedRepeatedGram n cs d) K
    (canonicalCorrectedReflection n cs d, 1)

omit [Finite F] in
theorem correctedFullReflection_involution_centralises_outside_withFactor
    (hTwo : (2 : F) ≠ 0)
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (E : Subgroup (FormIsometryGroup (omega (F := F))))
    (K : Matrix Rest Rest F) (C : Subgroup (FormIsometryGroup K)) :
    let R := correctedFullSubgroupWithFactor n cs d E K C
    let T := canonicalCorrectedFullReflection n cs d K
    T ^ 2 = 1 ∧ T ∈ Subgroup.centralizer (R : Set _) ∧ T ∉ R := by
  have hFactor := correctedReflection_involution_centralises_outside_withFactor
    hTwo n cs d E
  have hProd := prod_involution_centralises_outside
    (correctedBasicSubgroupWithFactor n cs d E) C
    hFactor.1 hFactor.2.1 hFactor.2.2
  exact map_involution_centralises_outside_of_injective
    (orthogonalBlockSumHom (correctedRepeatedGram n cs d) K)
    (orthogonalBlockSumHom_injective (correctedRepeatedGram n cs d) K)
    ((correctedBasicSubgroupWithFactor n cs d E).prod C)
    hProd.1 hProd.2.1 hProd.2.2

omit [Finite F] in
theorem canonicalCorrectedFullReflection_involution_centralises_outside
    (p : ℕ) [NeZero p] [CharP F p] (hp : ¬ p ∣ 2)
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (K : Matrix Rest Rest F) (C : Subgroup (FormIsometryGroup K)) :
    let R := canonicalCorrectedFullSubgroup p n cs d K C
    let T := canonicalCorrectedFullReflection n cs d K
    T ^ 2 = 1 ∧ T ∈ Subgroup.centralizer (R : Set _) ∧ T ∉ R := by
  exact correctedFullReflection_involution_centralises_outside_withFactor
    (two_ne_zero_of_charP p hp) n cs d
      (canonicalQuaternionSubgroup (F := F) p) K C

omit [Finite F] in
/-- If the source representative is conjugate to the block model built from
the supplied right tensor factor, the excluding reflection transports by the
same conjugation.  Literal equality with a particular matrix representative
is not required.  Supplying the right factor is deliberate: this theorem
does not identify an arbitrary quaternion copy with either source `alpha`
class. -/
theorem sourceConjugate_correctedFullReflection_involution_centralises_outside
    (hTwo : (2 : F) ≠ 0)
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (E : Subgroup (FormIsometryGroup (omega (F := F))))
    (K : Matrix Rest Rest F) (C : Subgroup (FormIsometryGroup K))
    (Rsource : Subgroup (FormIsometryGroup (correctedFullGram n cs d K)))
    (g : FormIsometryGroup (correctedFullGram n cs d K))
    (hConj : Rsource =
      (correctedFullSubgroupWithFactor n cs d E K C).map
        (MulAut.conj g).toMonoidHom) :
    let T := (MulAut.conj g) (canonicalCorrectedFullReflection n cs d K)
    T ^ 2 = 1 ∧
      T ∈ Subgroup.centralizer (Rsource : Set _) ∧ T ∉ Rsource := by
  have hModel := correctedFullReflection_involution_centralises_outside_withFactor
    hTwo n cs d E K C
  have hMapped := map_involution_centralises_outside_of_injective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    (correctedFullSubgroupWithFactor n cs d E K C)
    hModel.1 hModel.2.1 hModel.2.2
  simpa [hConj] using hMapped

omit [Finite F] in
/-- Source-shaped principal-block exclusion.  The source class of the right
tensor factor and conjugacy of the named full subgroup with its block model
remain explicit inputs; literal equality is not required. -/
theorem sourceConjugate_correctedFullFactor_not_principal
    (hTwo : (2 : F) ≠ 0)
    (n : ℕ) (cs : List ℕ) (d : Fin (n + 2) → F)
    (E : Subgroup (FormIsometryGroup (omega (F := F))))
    (K : Matrix Rest Rest F) (C : Subgroup (FormIsometryGroup K))
    (Rsource : Subgroup (FormIsometryGroup (correctedFullGram n cs d K)))
    (g : FormIsometryGroup (correctedFullGram n cs d K))
    (hConj : Rsource =
      (correctedFullSubgroupWithFactor n cs d E K C).map
        (MulAut.conj g).toMonoidHom)
    (IsPrincipalWeight : Prop)
    (principalCentreSylow : IsPrincipalWeight →
      ∃ P : Sylow 2 (Subgroup.centralizer
          (Rsource : Set (FormIsometryGroup (correctedFullGram n cs d K)))),
        (P : Subgroup (Subgroup.centralizer
          (Rsource : Set (FormIsometryGroup (correctedFullGram n cs d K))))) =
          centreInCentralizer Rsource) :
    ¬ IsPrincipalWeight := by
  intro hPrincipal
  let T := (MulAut.conj g) (canonicalCorrectedFullReflection n cs d K)
  have hT := sourceConjugate_correctedFullReflection_involution_centralises_outside
    hTwo n cs d E K C Rsource g hConj
  let X := geometryOfCentralisingInvolution Rsource T hT.1 hT.2.1 hT.2.2
  let D :
      ModularRep.PaperProofs.OddTwoProposition33Relative.EvenMultiplicityCandidateData
        Unit := {
    IsPrincipalWeight := fun _ ↦ IsPrincipalWeight
    geometry := fun _ ↦ X
    principalCentreSylow := fun _ _ ↦ by
      dsimp [X, geometryOfCentralisingInvolution]
      exact principalCentreSylow hPrincipal }
  exact ModularRep.PaperProofs.OddTwoProposition33Relative.omitted_even_multiplicity_not_principal
    D () hPrincipal

end RemainingOrthogonalFactors

end CanonicalCorrectedSourceModel

end ModularRep.PaperProofs.OddTwoAmbientRealisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
