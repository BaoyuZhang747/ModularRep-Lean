import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Paper proof: the GGGR rank argument for the principal 2-block in type B

This file checks the finite combinatorics and linear algebra used in manuscript
Proposition 4.9.  The construction of generalised Gelfand--Graev characters,
the published character correspondences, unipotent supports and wave front
sets, and the standard projective-character interpretation remain explicit
source inputs.

Lean proves the two deductions that are particular to the manuscript.  First,
the restriction calculation on the unique two-element fibre forces its
nonnegative scalar-product matrix to be a permutation matrix.  Secondly,
permutation diagonal blocks together with the closure-order vanishing give a
unimodular matrix and hence a basis of the projective character space.

No BAW or iBAW statement is encoded here.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBGGGRRankProposition412Relative

open scoped BigOperators
open Module

section FibreCombinatorics

/-- The transitivity argument for a fibre of size one.  If all restriction
constituents have the same nonnegative scalar product and their sum is one,
there is exactly one constituent and its scalar product is one. -/
theorem singleton_fibre_forces_irreducible
    {Constituent : Type*} [Fintype Constituent] [Nonempty Constituent]
    (entry : Constituent -> Nat)
    (equal_entry : forall i j, entry i = entry j)
    (sum_entry : (Finset.univ.sum entry) = 1) :
    Fintype.card Constituent = 1 ∧ forall i, entry i = 1 := by
  let i0 : Constituent := Classical.choice inferInstance
  have hsum_const : Fintype.card Constituent * entry i0 = 1 := by
    calc
      Fintype.card Constituent * entry i0 = Finset.univ.sum entry := by
        rw [Finset.sum_congr rfl (fun i _ => equal_entry i i0)]
        simp
      _ = 1 := sum_entry
  have hcard : Fintype.card Constituent = 1 :=
    Nat.dvd_one.mp ⟨entry i0, hsum_const.symm⟩
  have hi0 : entry i0 = 1 := by
    simpa [hcard] using hsum_const
  constructor
  · exact hcard
  · intro i
    exact (equal_entry i i0).trans hi0

/-- The transposition of the two constituents in the exceptional fibre. -/
def swapTwo : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

@[simp] theorem swapTwo_zero : swapTwo 0 = 1 := by
  simp [swapTwo]

@[simp] theorem swapTwo_one : swapTwo 1 = 0 := by
  simp [swapTwo]

/-- The manuscript-specific two-fibre deduction.

`entry i j` is the scalar product of the `i`th restriction constituent with
the GGGR attached to the `j`th rational class.  The ambient class has scalar
product one, so each column sum is one.  Equivariance swaps the two rows and
acts on the two columns through `classAction`.  Lean first proves that this
column action has no fixed point and then constructs the resulting
permutation block. -/
theorem two_fibre_permutation_block
    (entry : Fin 2 -> Fin 2 -> Nat)
    (classAction : Equiv.Perm (Fin 2))
    (equivariant : forall i j,
      entry (swapTwo i) (classAction j) = entry i j)
    (column_sum_one : forall j, entry 0 j + entry 1 j = 1) :
    exists p : Equiv.Perm (Fin 2), forall i j,
      entry i j = if i = p j then 1 else 0 := by
  have haction0_ne : classAction 0 ≠ 0 := by
    intro hfix
    have heq := equivariant 0 0
    rw [swapTwo_zero, hfix] at heq
    have hsum := column_sum_one 0
    omega
  have haction0 : classAction 0 = 1 := by
    exact Fin.eq_one_of_ne_zero _ haction0_ne
  have haction1 : classAction 1 = 0 := by
    apply Fin.ext
    have hne : classAction 1 ≠ 1 := by
      intro hfix
      have hzero : (0 : Fin 2) = 1 := classAction.injective
        (haction0.trans hfix.symm)
      exact Fin.zero_ne_one hzero
    have hne_val : (classAction 1).val ≠ 1 := by
      intro hval
      exact hne (Fin.ext hval)
    have hlt := (classAction 1).isLt
    omega
  have haction : classAction = swapTwo := by
    apply Equiv.ext
    intro j
    fin_cases j
    · simpa using haction0
    · simpa using haction1
  have hdiag : entry 1 1 = entry 0 0 := by
    simpa [haction] using equivariant 0 0
  have hoffdiag : entry 0 1 = entry 1 0 := by
    simpa [haction] using equivariant 1 0
  have hsum0 := column_sum_one 0
  have hsum1 := column_sum_one 1
  by_cases h00 : entry 0 0 = 0
  · refine ⟨swapTwo, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h00] at * <;> omega
  · refine ⟨Equiv.refl (Fin 2), ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp at * <;> omega

/-- Combine the singleton fibres and the unique two-element fibre.  The
singleton part is an identity block and the two-element part is a permutation
block; all cross-fibre entries vanish. -/
def assembledFibreMatrix {Singleton : Type*} [DecidableEq Singleton]
    (twoEntry : Fin 2 -> Fin 2 -> Nat) :
    Sum Singleton (Fin 2) -> Sum Singleton (Fin 2) -> Nat
  | Sum.inl i, Sum.inl j => if i = j then 1 else 0
  | Sum.inr i, Sum.inr j => twoEntry i j
  | _, _ => 0

/-- The explicit permutation for the combined diagonal block. -/
def assembledFibrePermutation {Singleton : Type*}
    (p : Equiv.Perm (Fin 2)) :
    Equiv.Perm (Sum Singleton (Fin 2)) :=
  Equiv.sumCongr (Equiv.refl Singleton) p

theorem assembled_fibre_matrix_is_permutation
    {Singleton : Type*} [DecidableEq Singleton]
    (twoEntry : Fin 2 -> Fin 2 -> Nat)
    (p : Equiv.Perm (Fin 2))
    (twoEntry_eq : forall i j,
      twoEntry i j = if i = p j then 1 else 0) :
    forall i j,
      assembledFibreMatrix twoEntry i j =
        if i = assembledFibrePermutation (Singleton := Singleton) p j
          then 1 else 0 := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp [assembledFibreMatrix, assembledFibrePermutation]
  · simp [assembledFibreMatrix, assembledFibrePermutation]
  · simp [assembledFibreMatrix, assembledFibrePermutation]
  · simpa [assembledFibreMatrix, assembledFibrePermutation] using
      twoEntry_eq i j

/-- The representation theoretic input specific to a nonabelian component
group, after the rational classes and restriction constituents have been
relabelled as singleton fibres together with the unique two-element fibre.
The fields are precisely the published fibre description, Frobenius
reciprocity column sums and equivariance.  No permutation-block conclusion is
a field. -/
structure NonabelianFibreModel
    {Index : Type*} [DecidableEq Index]
    (entry : Index -> Index -> Nat) where
  Singleton : Type*
  singletonDecidableEq : DecidableEq Singleton
  relabel : Index ≃ Sum Singleton (Fin 2)
  twoEntry : Fin 2 -> Fin 2 -> Nat
  entry_relabel : forall i j,
    entry i j = assembledFibreMatrix twoEntry (relabel i) (relabel j)
  classAction : Equiv.Perm (Fin 2)
  equivariant : forall i j,
    twoEntry (swapTwo i) (classAction j) = twoEntry i j
  column_sum_one : forall j, twoEntry 0 j + twoEntry 1 j = 1

/-- The exact published input in the abelian component-group case. -/
structure AbelianIdentityModel
    {Index : Type*} [DecidableEq Index]
    (entry : Index -> Index -> Nat) : Type where
  identity_entry : forall i j,
    entry i j = if i = j then 1 else 0

/-- The complete component-group case split for one geometric unipotent
class.  The abelian branch is the exact identity block supplied by the
published theorem.  In the nonabelian branch Lean constructs the permutation
block from the source-shaped fibre data. -/
theorem diagonal_block_from_component_cases
    {Index : Type*} [DecidableEq Index]
    (entry : Index -> Index -> Nat)
    (source :
      Sum (AbelianIdentityModel entry)
        (NonabelianFibreModel entry)) :
    exists p : Equiv.Perm Index, forall i j,
      entry i j = if i = p j then 1 else 0 := by
  rcases source with hab | D
  · refine ⟨Equiv.refl Index, ?_⟩
    intro i j
    rw [hab.identity_entry]
    by_cases hij : i = j <;> simp [hij]
  · let _ : DecidableEq D.Singleton := D.singletonDecidableEq
    obtain ⟨q, hq⟩ := two_fibre_permutation_block D.twoEntry
      D.classAction D.equivariant D.column_sum_one
    have hassembled := assembled_fibre_matrix_is_permutation
      (Singleton := D.Singleton) D.twoEntry q hq
    let qAssembled : Equiv.Perm (Sum D.Singleton (Fin 2)) :=
      assembledFibrePermutation q
    let p : Equiv.Perm Index :=
      D.relabel.trans (qAssembled.trans D.relabel.symm)
    refine ⟨p, ?_⟩
    intro i j
    rw [D.entry_relabel]
    have h := hassembled (D.relabel i) (D.relabel j)
    rw [h]
    by_cases hc : D.relabel i = qAssembled (D.relabel j)
    · have hp : i = p j := by
        apply D.relabel.injective
        simpa [p] using hc
      have hc' : D.relabel i =
          assembledFibrePermutation q (D.relabel j) := by
        simpa [qAssembled] using hc
      rw [if_pos hc', if_pos hp]
    · have hp : i ≠ p j := by
        intro hij
        apply hc
        have himage := congrArg D.relabel hij
        simpa [p] using himage
      have hc' : D.relabel i ≠
          assembledFibrePermutation q (D.relabel j) := by
        simpa [qAssembled] using hc
      rw [if_neg hc', if_neg hp]

end FibreCombinatorics

section PrincipalBlockProjection

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- A source-shaped interface for taking the component of a character in a
fixed block.  Orthogonality of block components is expressed by the
self-adjointness formula. -/
structure OrthogonalBlockProjection where
  pairing : V -> V -> R
  project : V →ₗ[R] V
  idempotent : project.comp project = project
  selfAdjoint : forall x y, pairing x (project y) = pairing (project x) y

namespace OrthogonalBlockProjection

/-- If an ordinary character already belongs to the selected block, its
pairing with the selected block component of a GGGR equals its pairing with
the full GGGR. -/
theorem pairing_project_eq
    (D : OrthogonalBlockProjection (R := R) (V := V))
    {eta gamma : V} (eta_in_block : D.project eta = eta) :
    D.pairing eta (D.project gamma) = D.pairing eta gamma := by
  rw [D.selfAdjoint, eta_in_block]

end OrthogonalBlockProjection

end PrincipalBlockProjection

section ClosureTriangularity

variable {R : Type*} [CommRing R]

/-- The source-shaped data obtained after ordering geometric classes by a
linear extension of closure order and ordering rational classes within each
geometric class.  `rowPermutation` records the permutation blocks already
constructed on the diagonal. -/
structure ClosurePermutationData (n : Nat) where
  matrix : Matrix (Fin n) (Fin n) R
  geometricClass : Fin n -> Nat
  geometricClass_mono : Monotone geometricClass
  rowPermutation : Equiv.Perm (Fin n)
  rowPermutation_preserves_class : forall i,
    geometricClass (rowPermutation i) = geometricClass i
  same_class_entry : forall i j,
    geometricClass i = geometricClass j ->
      matrix (rowPermutation i) j = if i = j then 1 else 0
  closure_vanishing : forall i j,
    geometricClass (rowPermutation i) < geometricClass j ->
      matrix (rowPermutation i) j = 0

namespace ClosurePermutationData

/-- Reindex the rows so that every diagonal permutation block becomes the
identity. -/
def reindexed {n : Nat} (D : ClosurePermutationData (R := R) n) :
    Matrix (Fin n) (Fin n) R :=
  D.matrix.submatrix D.rowPermutation id

theorem reindexed_isLowerTriangular {n : Nat}
    (D : ClosurePermutationData (R := R) n) :
    D.reindexed.IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  change D.matrix (D.rowPermutation i) j = 0
  have hclass := D.geometricClass_mono (le_of_lt hij)
  rcases hclass.eq_or_lt with heq | hlt
  · rw [D.same_class_entry i j heq]
    simp [ne_of_lt hij]
  · apply D.closure_vanishing i j
    rwa [D.rowPermutation_preserves_class]

theorem reindexed_diagonal {n : Nat}
    (D : ClosurePermutationData (R := R) n) (i : Fin n) :
    D.reindexed i i = 1 := by
  change D.matrix (D.rowPermutation i) i = 1
  rw [D.same_class_entry i i rfl]
  simp

theorem reindexed_det {n : Nat}
    (D : ClosurePermutationData (R := R) n) :
    D.reindexed.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular D.reindexed D.reindexed_isLowerTriangular]
  simp [D.reindexed_diagonal]

/-- The full scalar-product matrix is unimodular.  This is derived from the
closure-order zeroes and the diagonal permutation blocks, not assumed. -/
theorem det_isUnit {n : Nat}
    (D : ClosurePermutationData (R := R) n) :
    IsUnit D.matrix.det := by
  let signUnit : Rˣ := Units.map (Int.castRingHom R).toMonoidHom
    D.rowPermutation.sign
  refine ⟨signUnit⁻¹, ?_⟩
  have hperm := Matrix.det_permute D.rowPermutation D.matrix
  change D.reindexed.det =
    ((D.rowPermutation.sign : ℤˣ) : R) * D.matrix.det at hperm
  have hcoe : (↑signUnit : R) =
      ((D.rowPermutation.sign : ℤˣ) : R) := by
    simp [signUnit]
  rw [← hcoe] at hperm
  rw [D.reindexed_det] at hperm
  calc
    (↑(signUnit⁻¹) : R) = (↑(signUnit⁻¹) : R) * 1 := by simp
    _ = (↑(signUnit⁻¹) : R) *
        ((↑signUnit : R) * D.matrix.det) := by rw [← hperm]
    _ = ((↑(signUnit⁻¹) : R) * (↑signUnit : R)) *
        D.matrix.det := by rw [mul_assoc]
    _ = D.matrix.det := by rw [Units.inv_mul, one_mul]

theorem det_ne_zero {n : Nat} [Nontrivial R]
    (D : ClosurePermutationData (R := R) n) :
    D.matrix.det ≠ 0 :=
  D.det_isUnit.ne_zero

end ClosurePermutationData

end ClosureTriangularity

section RationalBasis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Nonsingularity of the scalar-product coordinate matrix gives linear
independence of the projective block components. -/
theorem projective_components_linearIndependent
    {n : Nat} [FiniteDimensional K V]
    (projectiveComponent : Fin n -> V)
    (coordinate : V →ₗ[K] (Fin n -> K))
    (pairingMatrix : Matrix (Fin n) (Fin n) K)
    (coordinate_eq_column : forall j,
      coordinate (projectiveComponent j) = pairingMatrix.col j)
    (det_ne_zero : pairingMatrix.det ≠ 0) :
    LinearIndependent K projectiveComponent := by
  have hcolumns : LinearIndependent K pairingMatrix.col :=
    Matrix.linearIndependent_cols_of_det_ne_zero det_ne_zero
  have hcomp : (coordinate ∘ projectiveComponent) = pairingMatrix.col := by
    funext j
    exact coordinate_eq_column j
  have hprojective : LinearIndependent K projectiveComponent := by
    apply LinearIndependent.of_comp coordinate
    simpa only [hcomp] using hcolumns
  exact hprojective

/-- Equality between the number of projective block components and the
dimension of the projective character space upgrades their independence to
an actual basis. -/
noncomputable def projectiveBasisOfPairingMatrix
    {n : Nat} [FiniteDimensional K V]
    (projectiveComponent : Fin n -> V)
    (coordinate : V →ₗ[K] (Fin n -> K))
    (pairingMatrix : Matrix (Fin n) (Fin n) K)
    (coordinate_eq_column : forall j,
      coordinate (projectiveComponent j) = pairingMatrix.col j)
    (det_ne_zero : pairingMatrix.det ≠ 0)
    (card_eq_finrank : Fintype.card (Fin n) = finrank K V) :
    Basis (Fin n) K V :=
  basisOfLinearIndependentOfCardEqFinrank' projectiveComponent
    (projective_components_linearIndependent projectiveComponent coordinate
      pairingMatrix coordinate_eq_column det_ne_zero)
    card_eq_finrank

@[simp] theorem coe_projectiveBasisOfPairingMatrix
    {n : Nat} [FiniteDimensional K V]
    (projectiveComponent : Fin n -> V)
    (coordinate : V →ₗ[K] (Fin n -> K))
    (pairingMatrix : Matrix (Fin n) (Fin n) K)
    (coordinate_eq_column : forall j,
      coordinate (projectiveComponent j) = pairingMatrix.col j)
    (det_ne_zero : pairingMatrix.det ≠ 0)
    (card_eq_finrank : Fintype.card (Fin n) = finrank K V) :
    ⇑(projectiveBasisOfPairingMatrix projectiveComponent coordinate
      pairingMatrix coordinate_eq_column det_ne_zero card_eq_finrank) =
        projectiveComponent := by
  simp [projectiveBasisOfPairingMatrix]

/-- Protected manuscript-facing endpoint for the rank conclusion.  The
published representation theoretic inputs enter only through the concrete
pairing matrix, its closure-order data, the projective-coordinate map and the
standard dimension count.  Unimodularity and the basis conclusion are both
derived. -/
theorem proposition_4_12_rank_relative
    {n : Nat} [FiniteDimensional K V]
    (D : ClosurePermutationData (R := K) n)
    (projectiveComponent : Fin n -> V)
    (coordinate : V →ₗ[K] (Fin n -> K))
    (coordinate_eq_column : forall j,
      coordinate (projectiveComponent j) = D.matrix.col j)
    (card_eq_finrank : Fintype.card (Fin n) = finrank K V) :
    IsUnit D.matrix.det ∧ exists B : Basis (Fin n) K V,
      (B : Fin n -> V) = projectiveComponent := by
  refine ⟨D.det_isUnit, ?_⟩
  let B := projectiveBasisOfPairingMatrix projectiveComponent coordinate
    D.matrix coordinate_eq_column D.det_ne_zero card_eq_finrank
  exact ⟨B, coe_projectiveBasisOfPairingMatrix projectiveComponent coordinate
    D.matrix coordinate_eq_column D.det_ne_zero card_eq_finrank⟩

end RationalBasis

end ModularRep.PaperProofs.TypeBGGGRRankProposition412Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
