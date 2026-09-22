import ModularRep.PaperProofs.EvenFieldConcreteTypeCFiniteModel

/-!
# The field action on the standard finite type C model

This module transports the cyclic field action on the Frobenius fixed-point
group to the literal matrix group over `GaloisField 2 a`.  The entry formula
below verifies that the transported action is exactly the expected
coefficientwise Frobenius action, rather than merely an abstract action on an
isomorphic carrier.
-/

namespace ModularRep.PaperProofs.EvenFieldConcreteTypeCFieldAction

open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldConcreteTypeCFiniteModel
open ModularRep.PaperProofs.EvenFieldFrobeniusPowers

noncomputable section

/-- The cyclic field action transported from the fixed-point model to the
standard finite symplectic matrix group. -/
noncomputable def standardFieldAction (r a : ℕ) (ha : 0 < a) :
    FieldGroup a →* MulAut (StandardEvenSymplectic r a) where
  toFun sigma :=
    (standardEvenSymplecticEquivFixedPoints r a ha).trans
      ((fieldAction r a ha sigma).trans
        (standardEvenSymplecticEquivFixedPoints r a ha).symm)
  map_one' := by
    apply DFunLike.ext _ _
    intro A
    simp
  map_mul' sigma tau := by
    apply DFunLike.ext _ _
    intro A
    change (standardEvenSymplecticEquivFixedPoints r a ha).symm
      (fieldAction r a ha (sigma * tau)
        (standardEvenSymplecticEquivFixedPoints r a ha A)) = _
    rw [map_mul, MulAut.mul_apply]
    change (standardEvenSymplecticEquivFixedPoints r a ha).symm
      (fieldAction r a ha sigma
        (fieldAction r a ha tau
          (standardEvenSymplecticEquivFixedPoints r a ha A))) =
      (standardEvenSymplecticEquivFixedPoints r a ha).symm
        (fieldAction r a ha sigma
          (standardEvenSymplecticEquivFixedPoints r a ha
            ((standardEvenSymplecticEquivFixedPoints r a ha).symm
              (fieldAction r a ha tau
                (standardEvenSymplecticEquivFixedPoints r a ha A)))))
    rw [MulEquiv.apply_symm_apply]

/-- The carrier equivalence intertwines the transported action with the
original action on the Frobenius fixed points. -/
@[simp]
theorem standardEquiv_standardFieldAction (r a : ℕ) (ha : 0 < a)
    (sigma : FieldGroup a) (A : StandardEvenSymplectic r a) :
    standardEvenSymplecticEquivFixedPoints r a ha
      (standardFieldAction r a ha sigma A) =
      fieldAction r a ha sigma
        (standardEvenSymplecticEquivFixedPoints r a ha A) := by
  simp [standardFieldAction]

/-- The concrete carrier equivalence sends an entry through the chosen
finite-field isomorphism and then includes it in the algebraic closure. -/
@[simp]
theorem standardEvenSymplecticEquivFixedPoints_entry
    (r a : ℕ) (ha : 0 < a) (A : StandardEvenSymplectic r a)
    (i j : Fin r ⊕ Fin r) :
    (((standardEvenSymplecticEquivFixedPoints r a ha A :
      FiniteSymplecticFixed r a) : AmbientSymplectic r) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j =
      (((standardEvenFieldEquivFixedCoefficientField a ha
        (((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
          (StandardEvenField a)) i j)) : FixedCoefficientField a) :
        AlgebraicField)) := by
  rfl

/-- The pointwise algebraic lift raises every matrix entry to the indicated
power of two. -/
@[simp]
theorem algebraicLift_entry (r a : ℕ) (sigma : FieldGroup a)
    (A : AmbientSymplectic r) (i j : Fin r ⊕ Fin r) :
    (((algebraicLift r a sigma A : AmbientSymplectic r) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) AlgebraicField) i j) =
      (((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
        AlgebraicField) i j) ^ (2 ^ sigma.toAdd.val)) := by
  change ((((ambientFrobeniusAut r ^ sigma.toAdd.val) A :
    AmbientSymplectic r) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
      AlgebraicField) i j) = _
  rw [mulAut_pow_apply_eq_iterate]
  change (((iterateMonoidHom (ambientFrobenius r) sigma.toAdd.val A :
    AmbientSymplectic r) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
      AlgebraicField) i j) = _
  exact ambientFrobenius_iterate_entry r sigma.toAdd.val A i j

/-- On the literal standard matrix model, the transported field action raises
each coefficient to `2 ^ sigma.toAdd.val`. -/
@[simp]
theorem standardFieldAction_entry (r a : ℕ) (ha : 0 < a)
    (sigma : FieldGroup a) (A : StandardEvenSymplectic r a)
    (i j : Fin r ⊕ Fin r) :
    (((standardFieldAction r a ha sigma A : StandardEvenSymplectic r a) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
        (StandardEvenField a)) i j) =
      (((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
        (StandardEvenField a)) i j) ^ (2 ^ sigma.toAdd.val)) := by
  let e := standardEvenSymplecticEquivFixedPoints r a ha
  let k := standardEvenFieldEquivFixedCoefficientField a ha
  apply k.injective
  apply Subtype.ext
  have h := congrArg
    (fun B : AmbientSymplectic r ↦
      ((B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
        AlgebraicField) i j))
    (fieldAction_coe r a ha sigma (e A))
  rw [← standardEquiv_standardFieldAction] at h
  rw [algebraicLift_entry] at h
  rw [standardEvenSymplecticEquivFixedPoints_entry,
    standardEvenSymplecticEquivFixedPoints_entry] at h
  change _ = ((k ((((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r)
      (StandardEvenField a)) i j)) ^ (2 ^ sigma.toAdd.val)) :
      FixedCoefficientField a) : AlgebraicField)
  rw [map_pow]
  exact h

end

end ModularRep.PaperProofs.EvenFieldConcreteTypeCFieldAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
