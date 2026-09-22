import ModularRep.PaperProofs.EvenFieldConcreteTypeC
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The finite coefficient field in the concrete type C model

This module constructs the bridge from the usual finite matrix model to the
fixed-point group used in the algebraic-group argument.  It defines the
subfield of the algebraic closure fixed by the `a`th power of the standard
Frobenius, and, for positive `a`, proves that it has `2^a` elements and
identifies it with `GaloisField 2 a`.  It then lifts that identification to
the corresponding symplectic groups.

No character-theoretic or Deligne--Lusztig input occurs here.
-/

namespace ModularRep.PaperProofs.EvenFieldConcreteTypeCFiniteModel

open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open Matrix LinearMap

noncomputable section

/-- The `a`th iterate of the coefficient Frobenius as a ring automorphism. -/
noncomputable def coefficientDefiningFrobenius (a : ℕ) :
    AlgebraicField ≃+* AlgebraicField :=
  coefficientFrobenius ^ a

@[simp]
theorem coefficientDefiningFrobenius_apply (a : ℕ) (x : AlgebraicField) :
    coefficientDefiningFrobenius a x = x ^ (2 ^ a) := by
  induction a generalizing x with
  | zero => simp [coefficientDefiningFrobenius]
  | succ a ih =>
      change (coefficientFrobenius ^ (a + 1)) x = x ^ (2 ^ (a + 1))
      rw [pow_succ]
      change (coefficientFrobenius ^ a) (coefficientFrobenius x) = _
      have h := ih (coefficientFrobenius x)
      change (coefficientFrobenius ^ a) (coefficientFrobenius x) =
        (coefficientFrobenius x) ^ (2 ^ a) at h
      rw [h, coefficientFrobenius_apply]
      rw [← pow_mul]
      congr 1
      simp [pow_succ, mul_comm]

/-- The subfield of the algebraic closure fixed by `x |-> x^(2^a)`. -/
noncomputable def FixedCoefficientField (a : ℕ) : Subfield AlgebraicField where
  carrier := {x | coefficientDefiningFrobenius a x = x}
  zero_mem' := by simp [coefficientDefiningFrobenius]
  one_mem' := by simp [coefficientDefiningFrobenius]
  add_mem' := by
    intro x y hx hy
    change coefficientDefiningFrobenius a (x + y) = x + y
    rw [map_add, hx, hy]
  neg_mem' := by
    intro x hx
    change coefficientDefiningFrobenius a (-x) = -x
    rw [map_neg, hx]
  mul_mem' := by
    intro x y hx hy
    change coefficientDefiningFrobenius a (x * y) = x * y
    rw [map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change coefficientDefiningFrobenius a x⁻¹ = x⁻¹
    rw [map_inv₀, hx]

@[simp]
theorem mem_FixedCoefficientField_iff (a : ℕ) (x : AlgebraicField) :
    x ∈ FixedCoefficientField a ↔ x ^ (2 ^ a) = x := by
  change coefficientDefiningFrobenius a x = x ↔ _
  rw [coefficientDefiningFrobenius_apply]

/-- For positive `a`, the fixed coefficient subfield is finite.  The proof
injects it into the roots of the nonzero polynomial `X^(2^a) - X`. -/
theorem finite_carrier_FixedCoefficientField (a : ℕ) (ha : 0 < a) :
    Set.Finite (FixedCoefficientField a : Set AlgebraicField) := by
  have hp :
      (Polynomial.X ^ (2 ^ a) - Polynomial.X : Polynomial AlgebraicField) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero AlgebraicField (p := 2) (n := a)
      (Nat.ne_of_gt ha) (by norm_num)
  have hroots := Polynomial.finite_setOfPred_isRoot hp
  have hcarrier :
      (FixedCoefficientField a : Set AlgebraicField) =
        {x | Polynomial.IsRoot
          (Polynomial.X ^ (2 ^ a) - Polynomial.X) x} := by
    ext x
    simp only [SetLike.mem_coe, mem_FixedCoefficientField_iff,
      Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
  rw [hcarrier]
  exact hroots

/-- A `Finite` instance for the literal fixed coefficient field. -/
theorem finiteFixedCoefficientField (a : ℕ) (ha : 0 < a) :
    Finite (FixedCoefficientField a) :=
  (finite_carrier_FixedCoefficientField a ha).to_subtype

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The fixed coefficient field has exactly `2^a` elements. -/
theorem natCard_FixedCoefficientField (a : ℕ) (ha : 0 < a) :
    Nat.card (FixedCoefficientField a) = 2 ^ a := by
  let _ : Finite (FixedCoefficientField a) :=
    finiteFixedCoefficientField a ha
  let _ : Fintype (FixedCoefficientField a) := Fintype.ofFinite _
  let p : Polynomial AlgebraicField :=
    Polynomial.X ^ (2 ^ a) - Polynomial.X
  have hp : p ≠ 0 := by
    dsimp [p]
    exact FiniteField.X_pow_card_pow_sub_X_ne_zero AlgebraicField
      (p := 2) (n := a) (Nat.ne_of_gt ha) (by norm_num)
  have hcarrier :
      (FixedCoefficientField a : Set AlgebraicField) =
        p.rootSet AlgebraicField := by
    ext x
    rw [SetLike.mem_coe, mem_FixedCoefficientField_iff,
      Polynomial.mem_rootSet_of_ne hp, Polynomial.aeval_def,
      Algebra.algebraMap_self]
    simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X]
    exact sub_eq_zero.symm
  let e : FixedCoefficientField a ≃ p.rootSet AlgebraicField :=
    Equiv.setCongr hcarrier
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (FixedCoefficientField a) =
        Fintype.card (p.rootSet AlgebraicField) :=
      Fintype.card_congr e
    _ = p.natDegree := by
      apply Polynomial.card_rootSet_eq_natDegree
      · dsimp [p]
        exact galois_poly_separable 2 (2 ^ a)
          (dvd_pow (dvd_refl 2) (Nat.ne_of_gt ha))
      · simpa [p] using (IsAlgClosed.splits p)
    _ = 2 ^ a := by
      dsimp [p]
      exact FiniteField.X_pow_card_pow_sub_X_natDegree_eq AlgebraicField
        (p := 2) (n := a) (Nat.ne_of_gt ha) (by norm_num)

/-- The standard finite field used for the concrete matrix model. -/
abbrev StandardEvenField (a : ℕ) := GaloisField 2 a

/-- A finite-field isomorphism from the standard `GaloisField 2 a` model to
the literal Frobenius-fixed subfield of the algebraic closure.  It is
necessarily noncanonical. -/
noncomputable def standardEvenFieldEquivFixedCoefficientField
    (a : ℕ) (ha : 0 < a) :
    StandardEvenField a ≃+* FixedCoefficientField a := by
  letI : Finite (FixedCoefficientField a) :=
    finiteFixedCoefficientField a ha
  letI : Fintype (FixedCoefficientField a) := Fintype.ofFinite _
  letI : Fintype (StandardEvenField a) := Fintype.ofFinite _
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    GaloisField.card 2 a (Nat.ne_of_gt ha),
    natCard_FixedCoefficientField a ha]

/-! ## Symplectic groups over equivalent coefficient fields -/

/-- A ring isomorphism induces a group isomorphism between the corresponding
symplectic matrix groups. -/
noncomputable def symplecticGroupRingEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (r : ℕ) (e : R ≃+* S) :
    Matrix.symplecticGroup (Fin r) R ≃*
      Matrix.symplecticGroup (Fin r) S where
  toFun A :=
    ⟨(A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) R).map e,
      SymplecticGroup.map_mem A.property e⟩
  invFun A :=
    ⟨(A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) S).map e.symm,
      SymplecticGroup.map_mem A.property e.symm⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp
  right_inv A := by
    apply Subtype.ext
    ext i j
    simp
  map_mul' A B := by
    apply Subtype.ext
    exact e.toRingHom.mapMatrix.map_mul A.1 B.1

/-- The literal finite symplectic matrix model over `GaloisField 2 a`. -/
abbrev StandardEvenSymplectic (r a : ℕ) :=
  Matrix.symplecticGroup (Fin r) (StandardEvenField a)

/-- In characteristic two, the canonical matrix `J` still defines an
alternating form.  This makes the intended meaning of the matrix group
explicit rather than relying on the phrase "symplectic group". -/
theorem standardCanonicalJ_isAlt (r a : ℕ) :
    (Matrix.J (Fin r) (StandardEvenField a)).toBilin'.IsAlt := by
  intro x
  simp [Matrix.toBilin'_apply, Matrix.J, Matrix.one_apply, mul_comm]

/-- The canonical alternating form used in the standard finite matrix model
is nondegenerate. -/
theorem standardCanonicalJ_nondegenerate (r a : ℕ) :
    (Matrix.J (Fin r) (StandardEvenField a)).toBilin'.Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
  exact (Matrix.isUnit_det_J (Fin r) (StandardEvenField a)).ne_zero

/-- Symplectic matrices over the Frobenius-fixed coefficient subfield. -/
abbrev FixedCoefficientSymplectic (r a : ℕ) :=
  Matrix.symplecticGroup (Fin r) (FixedCoefficientField a)

/-- The standard finite matrix group transported to the literal fixed
coefficient field inside the algebraic closure. -/
noncomputable def standardEvenSymplecticEquivFixedCoefficient
    (r a : ℕ) (ha : 0 < a) :
    StandardEvenSymplectic r a ≃* FixedCoefficientSymplectic r a :=
  symplecticGroupRingEquiv r
    (standardEvenFieldEquivFixedCoefficientField a ha)

/-! ## Identification with the Frobenius fixed-point group -/

/-- Include a symplectic matrix over the fixed coefficient field in the
ambient algebraic symplectic group. -/
noncomputable def fixedCoefficientSymplecticToAmbient (r a : ℕ)
    (A : FixedCoefficientSymplectic r a) : AmbientSymplectic r :=
  ⟨(A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
      (FixedCoefficientField a)).map
      (FixedCoefficientField a).subtype,
    SymplecticGroup.map_mem A.property
      (FixedCoefficientField a).subtype⟩

@[simp]
theorem fixedCoefficientSymplecticToAmbient_entry (r a : ℕ)
    (A : FixedCoefficientSymplectic r a) (i j : Fin r ⊕ Fin r) :
    ((fixedCoefficientSymplecticToAmbient r a A : AmbientSymplectic r) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j =
      ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
        (FixedCoefficientField a)) i j : AlgebraicField) :=
  rfl

/-- Inclusion of a matrix over the fixed coefficient field is fixed by the
defining Frobenius. -/
theorem fixedCoefficientSymplecticToAmbient_fixed (r a : ℕ)
    (A : FixedCoefficientSymplectic r a) :
    definingFrobenius r a (fixedCoefficientSymplecticToAmbient r a A) =
      fixedCoefficientSymplecticToAmbient r a A := by
  apply Subtype.ext
  ext i j
  rw [ambientFrobenius_iterate_entry]
  change ((A.1 i j : FixedCoefficientField a) : AlgebraicField) ^
      (2 ^ a) = (A.1 i j : AlgebraicField)
  exact (mem_FixedCoefficientField_iff a _).mp (A.1 i j).property

/-- Regard a fixed ambient symplectic matrix as a matrix over the fixed
coefficient subfield. -/
noncomputable def fixedPointCoefficientMatrix (r a : ℕ)
    (A : FiniteSymplecticFixed r a) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
      (FixedCoefficientField a) :=
  fun i j =>
    ⟨((A : AmbientSymplectic r) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j, by
      change coefficientDefiningFrobenius a _ = _
      rw [coefficientDefiningFrobenius_apply]
      have hfixed := congrArg
        (fun B : AmbientSymplectic r =>
          ((B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
            AlgebraicField) i j)) A.property
      rw [ambientFrobenius_iterate_entry] at hfixed
      exact hfixed⟩

@[simp]
theorem fixedPointCoefficientMatrix_map (r a : ℕ)
    (A : FiniteSymplecticFixed r a) :
    (fixedPointCoefficientMatrix r a A).map
        (FixedCoefficientField a).subtype =
      ((A : AmbientSymplectic r) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) := by
  ext i j
  rfl

/-- A fixed ambient symplectic matrix is symplectic over the fixed
coefficient subfield. -/
theorem fixedPointCoefficientMatrix_mem (r a : ℕ)
    (A : FiniteSymplecticFixed r a) :
    fixedPointCoefficientMatrix r a A ∈
      Matrix.symplecticGroup (Fin r) (FixedCoefficientField a) := by
  rw [SymplecticGroup.mem_iff]
  apply Matrix.map_injective (FixedCoefficientField a).subtype.injective
  simp only [Matrix.map_mul, Matrix.transpose_map,
    Matrix.map_J, fixedPointCoefficientMatrix_map]
  exact SymplecticGroup.mem_iff.mp (A : AmbientSymplectic r).property

/-- The inverse construction, from ambient fixed points to symplectic
matrices over the fixed coefficient field. -/
noncomputable def fixedPointToFixedCoefficientSymplectic (r a : ℕ)
    (A : FiniteSymplecticFixed r a) :
    FixedCoefficientSymplectic r a :=
  ⟨fixedPointCoefficientMatrix r a A,
    fixedPointCoefficientMatrix_mem r a A⟩

/-- The literal Frobenius fixed-point group is isomorphic to the symplectic
group over its fixed coefficient field. -/
noncomputable def fixedCoefficientSymplecticEquivFixedPoints (r a : ℕ) :
    FixedCoefficientSymplectic r a ≃* FiniteSymplecticFixed r a where
  toFun A :=
    ⟨fixedCoefficientSymplecticToAmbient r a A,
      fixedCoefficientSymplecticToAmbient_fixed r a A⟩
  invFun := fixedPointToFixedCoefficientSymplectic r a
  left_inv A := by
    apply Subtype.ext
    ext i j
    rfl
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    rfl
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    exact (FixedCoefficientField a).subtype.mapMatrix.map_mul A.1 B.1

/-- The load-bearing carrier identification: the usual finite matrix group
`Sp_(2r)(2^a)` is isomorphic to the fixed points of `F_2^[a]` in the
algebraic symplectic group. -/
noncomputable def standardEvenSymplecticEquivFixedPoints
    (r a : ℕ) (ha : 0 < a) :
    StandardEvenSymplectic r a ≃* FiniteSymplecticFixed r a :=
  (standardEvenSymplecticEquivFixedCoefficient r a ha).trans
    (fixedCoefficientSymplecticEquivFixedPoints r a)

end

end ModularRep.PaperProofs.EvenFieldConcreteTypeCFiniteModel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
