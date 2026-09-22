import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.PaperProofs.TypeBGGGRRankProposition412Relative

/-!
# Actual-character instantiation of Proposition 4.9

This file places the GGGRs and selected ordinary irreducible characters in
literal function-valued carriers.  The principal-block projective-character
space is a submodule of `G → K`, exactly the carrier used by the
source-instantiated Corollary 4.10.

The source interface records the published scalar-product multiplicities,
the abelian/nonabelian component-group alternatives on each geometric class,
closure-order vanishing, the literal self-adjoint block projection, and the
standard dimension count.  It contains no permutation matrix, determinant,
linear-independence, basis, fixedness, BAW, or iBAW field.

Lean constructs the scalar-product matrix and coordinate map, derives the
permutation on every diagonal block from the existing fibre argument,
combines those permutations over the geometric-class fibres, and invokes
the kernel-checked rank chain to construct the projective basis.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBGGGRRankProposition412SourceInstantiation

open Module
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.TypeBGGGRRankProposition412Relative

universe u

variable {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Finite G]

/-- The indices lying over one geometric unipotent class. -/
abbrev GeometricFibre {n : Nat} (geometricClass : Fin n → Nat) (c : Nat) :=
  {i : Fin n // geometricClass i = c}

/-- Literal source data for the GGGR rank argument.

The deep fields have the following exact source roles.

* `diagonalSource` packages Chaneb, Proposition 2.8(i)--(iii), in the
  abelian case, and Taylor 2013, Section 2 and Propositions 3.2, 4.4,
  together with Lemma 4.3, Taylor 2013, Lemma 5.2 and Corollary 5.3, and
  Geck--Hezard, Proposition 4.3, in the nonabelian case.  In particular it
  supplies only the fibre relabelling, equivariance, and column sums required
  by `NonabelianFibreModel`.
* `scalarProduct_full_eq_multiplicity` is the corresponding published GGGR
  scalar-product formula, with Taylor 2016, Theorem 13.4 and Corollary 13.6,
  removing the old size restrictions.
* `closure_vanishing` is Taylor 2016, Lemma 14.15 and Proposition 15.2,
  after the selected-support identification.
* `card_eq_finrank` combines Chaneb, Proposition 2.7, Cabanes--Enguehard,
  Theorem 21.14, and standard projective--Brauer duality.

Those are exact E2/E1 inputs and receive no K credit.  The projection fields
are the literal E1/U match to the standard principal-block decomposition.
No conclusion of Proposition 4.9 occurs among the fields. -/
structure GGGRBasisSource
    (n : Nat) (projectiveSpace : Submodule K (G → K))
    [FiniteDimensional K projectiveSpace] where
  /-- Literal function-valued generalised Gelfand--Graev characters. -/
  gggr : Fin n → G → K
  /-- Literal function-valued selected ordinary irreducible characters. -/
  selectedOrdinary : Fin n → Irr K G
  /-- Scalar product, linear in the projective-character argument. -/
  scalarProductRight : (G → K) → (G → K) →ₗ[K] K
  /-- Literal projection onto the principal-block summand. -/
  principalProjection : (G → K) →ₗ[K] (G → K)
  principalProjection_idempotent :
    principalProjection.comp principalProjection = principalProjection
  principalProjection_selfAdjoint : ∀ x y,
    scalarProductRight x (principalProjection y) =
      scalarProductRight (principalProjection x) y
  /-- Each selected ordinary character lies in the principal block. -/
  selectedOrdinary_in_principal : ∀ i,
    principalProjection (selectedOrdinary i).1 = (selectedOrdinary i).1
  /-- Projectivity of each principal-block GGGR component. -/
  principalGGGR_mem_projective : ∀ j,
    principalProjection (gggr j) ∈ projectiveSpace
  /-- Nonnegative GGGR scalar-product multiplicities. -/
  multiplicity : Fin n → Fin n → Nat
  scalarProduct_full_eq_multiplicity : ∀ i j,
    scalarProductRight (selectedOrdinary i).1 (gggr j) =
      (multiplicity i j : K)
  /-- Closure-compatible enumeration of the geometric classes. -/
  geometricClass : Fin n → Nat
  geometricClass_mono : Monotone geometricClass
  /-- Exact component-group alternative on each geometric-class fibre. -/
  diagonalSource : ∀ c : Nat,
    Sum
      (AbelianIdentityModel
        (fun i j : GeometricFibre geometricClass c ↦
          multiplicity i.1 j.1))
      (NonabelianFibreModel.{0, 0}
        (fun i j : GeometricFibre geometricClass c ↦
          multiplicity i.1 j.1))
  /-- Source-shaped support/wave-front vanishing for the full GGGR. -/
  closure_vanishing : ∀ i j,
    geometricClass i < geometricClass j →
      scalarProductRight (selectedOrdinary i).1 (gggr j) = 0
  /-- The standard projective--Brauer dimension count. -/
  card_eq_finrank : Fintype.card (Fin n) = finrank K projectiveSpace

namespace GGGRBasisSource

variable {n : Nat} {projectiveSpace : Submodule K (G → K)}
variable [FiniteDimensional K projectiveSpace]

/-- The source fields instantiate the abstract orthogonal block projection. -/
def orthogonalBlockProjection
    (S : GGGRBasisSource n projectiveSpace) :
    OrthogonalBlockProjection (R := K) (V := G → K) where
  pairing x y := S.scalarProductRight x y
  project := S.principalProjection
  idempotent := S.principalProjection_idempotent
  selfAdjoint := S.principalProjection_selfAdjoint

/-- The actual principal-block component of a literal GGGR, as an element of
the literal projective-character submodule. -/
def principalGGGRComponent
    (S : GGGRBasisSource n projectiveSpace) (j : Fin n) : projectiveSpace :=
  ⟨S.principalProjection (S.gggr j), S.principalGGGR_mem_projective j⟩

/-- The actual scalar-product matrix of selected ordinary characters against
the principal-block GGGR components. -/
def scalarProductMatrix
    (S : GGGRBasisSource n projectiveSpace) : Matrix (Fin n) (Fin n) K :=
  fun i j ↦
    S.scalarProductRight (S.selectedOrdinary i).1
      (S.principalGGGRComponent j).1

/-- Passing to the principal-block GGGR component preserves the relevant
scalar product; hence every actual matrix entry is the cast of the published
nonnegative multiplicity. -/
theorem scalarProductMatrix_apply
    (S : GGGRBasisSource n projectiveSpace) (i j : Fin n) :
    S.scalarProductMatrix i j = (S.multiplicity i j : K) := by
  calc
    S.scalarProductMatrix i j =
        S.scalarProductRight (S.selectedOrdinary i).1
          (S.principalProjection (S.gggr j)) := rfl
    _ = S.scalarProductRight (S.selectedOrdinary i).1 (S.gggr j) :=
      (S.orthogonalBlockProjection.pairing_project_eq
        (S.selectedOrdinary_in_principal i))
    _ = (S.multiplicity i j : K) :=
      S.scalarProduct_full_eq_multiplicity i j

/-- Scalar products with the selected literal ordinary characters give the
projective-coordinate map.  Its linearity is constructed from the supplied
right-linear scalar product, rather than assumed as a separate U adapter. -/
def projectiveCoordinate
    (S : GGGRBasisSource n projectiveSpace) :
    projectiveSpace →ₗ[K] (Fin n → K) where
  toFun P i := S.scalarProductRight (S.selectedOrdinary i).1 P.1
  map_add' P Q := by
    funext i
    exact (S.scalarProductRight (S.selectedOrdinary i).1).map_add P.1 Q.1
  map_smul' c P := by
    funext i
    exact (S.scalarProductRight (S.selectedOrdinary i).1).map_smul c P.1

@[simp]
theorem projectiveCoordinate_apply
    (S : GGGRBasisSource n projectiveSpace)
    (P : projectiveSpace) (i : Fin n) :
    S.projectiveCoordinate P i =
      S.scalarProductRight (S.selectedOrdinary i).1 P.1 :=
  rfl

/-- The constructed coordinate map sends each actual GGGR component to the
corresponding column of the actual scalar-product matrix. -/
theorem projectiveCoordinate_principalGGGRComponent
    (S : GGGRBasisSource n projectiveSpace) (j : Fin n) :
    S.projectiveCoordinate (S.principalGGGRComponent j) =
      S.scalarProductMatrix.col j := by
  rfl

/-- The diagonal permutation on one geometric-class fibre, derived from the
published component-group alternative. -/
def diagonalPermutation
    (S : GGGRBasisSource n projectiveSpace) (c : Nat) :
    Equiv.Perm (GeometricFibre S.geometricClass c) :=
  Classical.choose
    (diagonal_block_from_component_cases
      (fun i j : GeometricFibre S.geometricClass c ↦
        S.multiplicity i.1 j.1)
      (S.diagonalSource c))

theorem diagonalPermutation_spec
    (S : GGGRBasisSource n projectiveSpace) (c : Nat)
    (i j : GeometricFibre S.geometricClass c) :
    S.multiplicity i.1 j.1 =
      if i = S.diagonalPermutation c j then 1 else 0 :=
  Classical.choose_spec
    (diagonal_block_from_component_cases
      (fun a b : GeometricFibre S.geometricClass c ↦
        S.multiplicity a.1 b.1)
      (S.diagonalSource c)) i j

/-- Regroup the global index set as the disjoint union of its geometric-class
fibres. -/
def groupedByGeometricClass
    (S : GGGRBasisSource n projectiveSpace) :
    Fin n ≃ Σ c : Nat, GeometricFibre S.geometricClass c where
  toFun i := ⟨S.geometricClass i, ⟨i, rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨c, i, hi⟩
    subst c
    rfl

/-- Combine the kernel-derived diagonal permutations over all geometric
classes. -/
def rowPermutation
    (S : GGGRBasisSource n projectiveSpace) : Equiv.Perm (Fin n) :=
  S.groupedByGeometricClass.trans
    ((Equiv.sigmaCongrRight fun c ↦ S.diagonalPermutation c).trans
      S.groupedByGeometricClass.symm)

@[simp]
theorem rowPermutation_apply
    (S : GGGRBasisSource n projectiveSpace) (i : Fin n) :
    S.rowPermutation i =
      (S.diagonalPermutation (S.geometricClass i) ⟨i, rfl⟩).1 :=
  rfl

theorem rowPermutation_preserves_class
    (S : GGGRBasisSource n projectiveSpace) (i : Fin n) :
    S.geometricClass (S.rowPermutation i) = S.geometricClass i :=
  (S.diagonalPermutation (S.geometricClass i) ⟨i, rfl⟩).2

/-- The actual scalar-product data instantiate the closure-permutation
interface.  Its `same_class_entry` field is proved from
`diagonal_block_from_component_cases`; it is not a source premise. -/
def closurePermutationData
    (S : GGGRBasisSource n projectiveSpace) :
    ClosurePermutationData (R := K) n where
  matrix := S.scalarProductMatrix
  geometricClass := S.geometricClass
  geometricClass_mono := S.geometricClass_mono
  rowPermutation := S.rowPermutation
  rowPermutation_preserves_class := S.rowPermutation_preserves_class
  same_class_entry := by
    intro i j hij
    have hj : S.geometricClass j = S.geometricClass i := hij.symm
    let i' : GeometricFibre S.geometricClass (S.geometricClass i) := ⟨i, rfl⟩
    let j' : GeometricFibre S.geometricClass (S.geometricClass i) := ⟨j, hj⟩
    have hdiag := S.diagonalPermutation_spec (S.geometricClass i)
      (S.diagonalPermutation (S.geometricClass i) i') j'
    rw [S.scalarProductMatrix_apply]
    change ((S.multiplicity
      (S.diagonalPermutation (S.geometricClass i) i').1 j : Nat) : K) = _
    rw [hdiag]
    by_cases h : i = j
    · subst j
      simp [i', j']
    · have hsub :
          S.diagonalPermutation (S.geometricClass i) i' ≠
            S.diagonalPermutation (S.geometricClass i) j' := by
        intro heq
        have hij' : i' = j' :=
          (S.diagonalPermutation (S.geometricClass i)).injective heq
        apply h
        exact congrArg Subtype.val hij'
      rw [if_neg hsub, if_neg h]
      exact Nat.cast_zero
  closure_vanishing := by
    intro i j hij
    change S.scalarProductMatrix (S.rowPermutation i) j = 0
    rw [S.scalarProductMatrix_apply]
    have hzero := S.closure_vanishing (S.rowPermutation i) j hij
    rw [S.scalarProduct_full_eq_multiplicity] at hzero
    exact hzero

/-- The strongest actual-carrier endpoint for Proposition 4.9.

The basis is constructed by the existing fibre/projection/closure/rank K
chain.  In particular, it is not an argument of this theorem.  Its carrier
and index type are definitionally the concrete GGGR-basis input expected by
the source-instantiated Corollary 4.10 (with `I := Fin n`). -/
theorem proposition_4_12_source_instantiated
    (S : GGGRBasisSource n projectiveSpace) :
    IsUnit S.scalarProductMatrix.det ∧
      ∃ B : Basis (Fin n) K projectiveSpace,
        (B : Fin n → projectiveSpace) = S.principalGGGRComponent := by
  exact proposition_4_12_rank_relative S.closurePermutationData
    S.principalGGGRComponent S.projectiveCoordinate
    S.projectiveCoordinate_principalGGGRComponent S.card_eq_finrank

/-- A canonical choice of the actual GGGR projective basis produced by
Proposition 4.9.  This definition is a direct adapter to the `gggrBasis`
argument of Corollary 4.10; it chooses from the proved endpoint and does not
take a basis as input. -/
def gggrProjectiveBasis
    (S : GGGRBasisSource n projectiveSpace) :
    Basis (Fin n) K projectiveSpace :=
  Classical.choose S.proposition_4_12_source_instantiated.2

@[simp]
theorem coe_gggrProjectiveBasis
    (S : GGGRBasisSource n projectiveSpace) :
    (S.gggrProjectiveBasis : Fin n → projectiveSpace) =
      S.principalGGGRComponent :=
  Classical.choose_spec S.proposition_4_12_source_instantiated.2

end GGGRBasisSource

end ModularRep.PaperProofs.TypeBGGGRRankProposition412SourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
