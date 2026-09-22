import ModularRep.PaperProofs.EvenFieldCyclicFieldAction
import ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Concrete type C carrier and field action

This module constructs the actual matrix group underlying the even-field
argument in Lemma 3.6.  The ambient group is the symplectic group over an
algebraic closure of `ZMod 2`.  The standard Frobenius acts entrywise by
`x |-> x^2`, the defining Frobenius is its `a`th iterate, and the finite group
is the corresponding fixed-point subgroup.

The cyclic field group is `Multiplicative (ZMod a)`.  Its action on the fixed
points is a genuine group homomorphism.  Its lifts to the ambient group are
only a pointwise family of Frobenius powers, because reduction of exponents
modulo `a` is valid on the fixed points but not on the ambient algebraic
group.

No block, character, Lusztig-series, Levi, weight, or fixation conclusion is
defined or assumed here.  Its finiteness for positive `a` is proved directly
below from the matrix entries.  The companion module
`EvenFieldConcreteTypeCFiniteModel` identifies it with the usual finite matrix
model over `GaloisField 2 a`.
-/

namespace ModularRep.PaperProofs.EvenFieldConcreteTypeC

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldCyclicFieldAction
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldFrobeniusPowers
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldSourceShaped

noncomputable section

/-- The coefficient field of the ambient algebraic symplectic group. -/
abbrev AlgebraicField := AlgebraicClosure (ZMod 2)

/-- The group of symplectic matrices of size `2r` over the algebraic closure
of the prime field of characteristic two. -/
abbrev AmbientSymplectic (r : ℕ) :=
  Matrix.symplecticGroup (Fin r) AlgebraicField

/-- Entrywise application of a coefficient field automorphism restricts to
an automorphism of the symplectic matrix group. -/
noncomputable def mapCoefficientAut (r : ℕ)
    (sigma : AlgebraicField ≃+* AlgebraicField) :
    MulAut (AmbientSymplectic r) where
  toFun A :=
    ⟨(A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField).map sigma,
      SymplecticGroup.map_mem A.property sigma⟩
  invFun A :=
    ⟨(A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField).map sigma.symm,
      SymplecticGroup.map_mem A.property sigma.symm⟩
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
    exact sigma.toRingHom.mapMatrix.map_mul A.1 B.1

@[simp]
theorem mapCoefficientAut_coe (r : ℕ)
    (sigma : AlgebraicField ≃+* AlgebraicField)
    (A : AmbientSymplectic r) :
    ((mapCoefficientAut r sigma A : AmbientSymplectic r) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) =
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField).map sigma :=
  rfl

/-- The Frobenius automorphism `x |-> x^2` of the algebraic closure. -/
noncomputable def coefficientFrobenius :
    AlgebraicField ≃+* AlgebraicField :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic
    (ZMod 2) AlgebraicField).toRingEquiv

@[simp]
theorem coefficientFrobenius_apply (x : AlgebraicField) :
    coefficientFrobenius x = x ^ 2 := by
  change x ^ Fintype.card (ZMod 2) = x ^ 2
  norm_num [ZMod.card]

/-- The standard Frobenius automorphism of the ambient symplectic group. -/
noncomputable def ambientFrobeniusAut (r : ℕ) :
    MulAut (AmbientSymplectic r) :=
  mapCoefficientAut r coefficientFrobenius

/-- The standard Frobenius regarded as a group endomorphism. -/
noncomputable def ambientFrobenius (r : ℕ) :
    AmbientSymplectic r →* AmbientSymplectic r :=
  (ambientFrobeniusAut r).toMonoidHom

@[simp]
theorem ambientFrobenius_entry (r : ℕ) (A : AmbientSymplectic r)
    (i j : Fin r ⊕ Fin r) :
    ((ambientFrobenius r A : AmbientSymplectic r) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j =
      ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j) ^ 2 := by
  exact coefficientFrobenius_apply _

/-- The `n`th Frobenius iterate raises every matrix entry to `2^n`. -/
theorem ambientFrobenius_iterate_entry (r n : ℕ)
    (A : AmbientSymplectic r) (i j : Fin r ⊕ Fin r) :
    ((iterateMonoidHom (ambientFrobenius r) n A : AmbientSymplectic r) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j =
      ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j) ^
        (2 ^ n) := by
  induction n generalizing A with
  | zero => simp [iterateMonoidHom]
  | succ n ih =>
      change (((ambientFrobenius r : AmbientSymplectic r → AmbientSymplectic r)^[n + 1]
        A : AmbientSymplectic r) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j = _
      rw [Function.iterate_succ_apply', ambientFrobenius_entry]
      have h := ih A
      change (((ambientFrobenius r : AmbientSymplectic r → AmbientSymplectic r)^[n]
        A : AmbientSymplectic r) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j = _ at h
      rw [h]
      rw [← pow_mul]
      congr 2

/-- The defining Frobenius `F' = F_2^[a]`. -/
abbrev definingFrobenius (r a : ℕ) :
    AmbientSymplectic r →* AmbientSymplectic r :=
  iterateMonoidHom (ambientFrobenius r) a

/-- The literal fixed-point group of the defining Frobenius. -/
abbrev FiniteSymplecticFixed (r a : ℕ) :=
  frobeniusFixedSubgroup (definingFrobenius r a)

/-! ## Finiteness of the fixed-point group -/

/-- Coefficients fixed by the `a`th iterate of the standard Frobenius. -/
abbrev FrobeniusFixedCoefficient (a : ℕ) :=
  {x : AlgebraicField // x ^ (2 ^ a) = x}

/-- For positive `a`, the Frobenius fixed coefficients are the roots of the
nonzero polynomial `X^(2^a) - X`, and hence form a finite set. -/
theorem frobeniusFixedCoefficients_finite (a : ℕ) (ha : 0 < a) :
    Set.Finite {x : AlgebraicField | x ^ (2 ^ a) = x} := by
  let p : Polynomial AlgebraicField := Polynomial.X ^ (2 ^ a) - Polynomial.X
  have hpow : 2 ^ a ≠ 1 :=
    ne_of_gt (Nat.one_lt_two_pow (Nat.ne_of_gt ha))
  have hp : p ≠ 0 := by
    intro hzero
    have hcoeff :=
      congrArg (fun q : Polynomial AlgebraicField => q.coeff (2 ^ a)) hzero
    simp [p, Polynomial.coeff_X, Ne.symm hpow] at hcoeff
  have hfinite := Polynomial.finite_setOfPred_isRoot hp
  simpa only [Polynomial.IsRoot.def, p, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero] using hfinite

/-- Encode a fixed symplectic matrix by its entries, each regarded as a root
of `X^(2^a) - X`. -/
noncomputable def fixedEntryMatrix (r a : ℕ)
    (A : FiniteSymplecticFixed r a) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
      (FrobeniusFixedCoefficient a) :=
  fun i j =>
    ⟨((A : AmbientSymplectic r) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j, by
      have hfixed := congrArg
        (fun B : AmbientSymplectic r =>
          ((B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j))
        A.property
      rw [ambientFrobenius_iterate_entry] at hfixed
      exact hfixed⟩

/-- The entry encoding of fixed symplectic matrices is injective. -/
theorem fixedEntryMatrix_injective (r a : ℕ) :
    Function.Injective (fixedEntryMatrix r a) := by
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  exact congrArg Subtype.val (congrFun (congrFun h i) j)

/-- A concrete `Fintype` structure on the fixed-point symplectic group for
positive Frobenius exponent. -/
@[instance_reducible]
noncomputable def finiteSymplecticFixedFintype (r a : ℕ) (ha : 0 < a) :
    Fintype (FiniteSymplecticFixed r a) := by
  letI : Fintype (FrobeniusFixedCoefficient a) :=
    (frobeniusFixedCoefficients_finite a ha).fintype
  exact Fintype.ofInjective (fixedEntryMatrix r a)
    (fixedEntryMatrix_injective r a)

/-- The fixed-point symplectic group is finite when the Frobenius exponent is
positive. -/
theorem finite_finiteSymplecticFixed (r a : ℕ) (ha : 0 < a) :
    Finite (FiniteSymplecticFixed r a) := by
  exact @Finite.of_fintype _ (finiteSymplecticFixedFintype r a ha)

/-- The cyclic field group used in the manuscript. -/
abbrev FieldGroup (a : ℕ) := Multiplicative (ZMod a)

/-- The genuine action of the cyclic field group on the fixed-point group. -/
noncomputable def fieldAction (r a : ℕ) (ha : 0 < a) :
    FieldGroup a →* MulAut (FiniteSymplecticFixed r a) :=
  fieldActionHom (ambientFrobenius r) a ha

/-- The manuscript writes field automorphisms on the right.  Passing to the
opposite groups turns the concrete field action into the homomorphism used by
the canonical left actions on characters, blocks, and weights. -/
def oppositeFieldAction (r a : ℕ) (ha : 0 < a) :
    (FieldGroup a)ᵐᵒᵖ →* (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ :=
  MonoidHom.op (fieldAction r a ha)

/-- Pointwise algebraic lifts of field automorphisms.  This is deliberately
not asserted to be a homomorphism on the ambient group. -/
noncomputable def algebraicLift (r a : ℕ) (sigma : FieldGroup a) :
    MulAut (AmbientSymplectic r) :=
  ambientFrobeniusAut r ^ sigma.toAdd.val

theorem mulAut_pow_apply_eq_iterate
    {G : Type*} [Group G] (sigma : MulAut G) (n : ℕ) (x : G) :
    (sigma ^ n) x = (sigma : G → G)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change (sigma ^ n) (sigma x) = _
      rw [ih]
      rfl

/-- Every pointwise lift commutes with the defining Frobenius. -/
theorem algebraicLift_commutes (r a : ℕ) (sigma : FieldGroup a)
    (x : AmbientSymplectic r) :
    definingFrobenius r a (algebraicLift r a sigma x) =
      algebraicLift r a sigma (definingFrobenius r a x) := by
  simp only [definingFrobenius, algebraicLift]
  rw [mulAut_pow_apply_eq_iterate, mulAut_pow_apply_eq_iterate]
  exact iterateMonoidHom_commute (ambientFrobenius r) a sigma.toAdd.val x

/-- The genuine finite action is the restriction of the chosen pointwise
algebraic lift. -/
theorem fieldAction_coe (r a : ℕ) (ha : 0 < a)
    (sigma : FieldGroup a) (x : FiniteSymplecticFixed r a) :
    (((fieldAction r a ha sigma) x : FiniteSymplecticFixed r a) :
      AmbientSymplectic r) =
      algebraicLift r a sigma (x : AmbientSymplectic r) := by
  change (((fieldActionHom (ambientFrobenius r) a ha sigma) x :
      FiniteSymplecticFixed r a) : AmbientSymplectic r) = _
  rw [fieldActionHom_apply_val]
  change iterateMonoidHom (ambientFrobenius r) sigma.toAdd.val
      (x : AmbientSymplectic r) =
    (ambientFrobeniusAut r ^ sigma.toAdd.val) (x : AmbientSymplectic r)
  rw [mulAut_pow_apply_eq_iterate]
  rfl

/-! ## Adapter to the exact E1--E4 source contract -/

/-- The representation theoretic E1--E4 inputs after the algebraic group,
defining Frobenius, finite fixed-point group, and field action have been fixed
to the concrete type C objects above.

Every field is a theorem-level or semantic input from the cited block and
Deligne--Lusztig theory.  The structure contains no field action, algebraic
lift, character fixation conclusion, generic-pair fixation, or final
conclusion of Lemma 3.6. -/
structure E1E4RepresentationInputs
    {A Block Dual : Type} [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A Block)
    (C : Block) where
  ellPrime : Nat.Prime ell
  blocks : OrdinaryBlockCarrier (FiniteSymplecticFixed r a) Block
  globalSeries : RationalSeriesSource (FiniteSymplecticFixed r a) Dual
  e1BlockSeries : ∀ chi : Irr ℂ (FiniteSymplecticFixed r a),
    blocks.blockOf chi = C →
      ∃ t : Dual, globalSeries.series chi t ∧
        ∃ n : ℕ, t ^ (ell ^ n) = 1
  e3FieldFixesUnipotent :
    ∀ (sigma : FieldGroup a)
      (chi : Irr ℂ (FiniteSymplecticFixed r a)),
      globalSeries.series chi 1 →
        twist ℂ (FiniteSymplecticFixed r a) chi
          (fieldAction r a ha sigma) = chi
  blockLabel : Dual
  blockLabel_eq_one : blockLabel = 1
  localSeries : LocalLeviSeriesSource D globalSeries
  e4LocalLabelComparison :
    ∀ (P : LocalPair ℂ (FiniteSymplecticFixed r a) A)
      (generic : GenericWitness D C P),
      ∃ (s : localSeries.dualLevi P.1) (x : Dual),
        localSeries.series P.1 generic.lambda s ∧
          (s : Dual) = x * blockLabel * x⁻¹

/-- Construct the exact E1--E4 provider on the concrete type C carrier.
Only the representation theoretic source package remains an argument. -/
noncomputable def E1E4RepresentationInputs.toExactProvider
    {A Block Dual : Type} [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    {D : Definitions ℂ (FiniteSymplecticFixed r a) A Block}
    {C : Block}
    (S : E1E4RepresentationInputs (A := A) (Block := Block) (Dual := Dual)
      r a ell ha D C) :
    ExactE1E4Provider
      (Dual := Dual) (definingFrobenius r a) (algebraicLift r a)
      ell D C := by
  letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  exact
    { ellPrime := S.ellPrime
      fieldGroupFintype := inferInstance
      blocks := S.blocks
      globalSeries := S.globalSeries
      algebraicLift_commutes := algebraicLift_commutes r a
      fieldAction := fieldAction r a ha
      fieldAction_coe := fieldAction_coe r a ha
      e1BlockSeries := S.e1BlockSeries
      e3FieldFixesUnipotent := S.e3FieldFixesUnipotent
      blockLabel := S.blockLabel
      blockLabel_eq_one := S.blockLabel_eq_one
      localSeries := S.localSeries
      e4LocalLabelComparison := S.e4LocalLabelComparison }

end

end ModularRep.PaperProofs.EvenFieldConcreteTypeC


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
