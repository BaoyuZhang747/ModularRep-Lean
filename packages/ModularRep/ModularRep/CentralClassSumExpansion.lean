import ModularRep.GroupAlgebraClassSums

/-!
# Expansion of central group algebra elements in conjugacy class sums

For a finite group, every central group algebra element is the finite sum of
its classwise coefficient times the corresponding unnormalised conjugacy class
sum.  This construction uses no class-size division, averaging, block data,
central Brauer map, or representation theoretic source.
-/

namespace ModularRep

open MonoidAlgebra
open scoped BigOperators

noncomputable section

variable {k H : Type*} [CommSemiring k] [Group H] [Fintype H]

local instance centralClassExpansionPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- A chosen representative of a conjugacy class. -/
noncomputable def conjugacyClassRepresentative
    (K : ConjClasses H) : H :=
  Classical.choose (ConjClasses.exists_rep K)

/-- The chosen representative represents the class from which it was chosen. -/
theorem conjugacyClassRepresentative_spec
    (K : ConjClasses H) :
    ConjClasses.mk (conjugacyClassRepresentative K) = K :=
  Classical.choose_spec (ConjClasses.exists_rep K)

/-- The unnormalised conjugacy class sum indexed by a quotient class. -/
noncomputable def conjugacyClassSumOfClass
    (K : ConjClasses H) : GroupAlgebraCenter k H :=
  conjugacyClassSum (k := k) (conjugacyClassRepresentative K)

/-- The coefficient of an unnormalised conjugacy class sum is one exactly on
that class and zero elsewhere. -/
theorem conjugacyClassSum_coeff
    (g x : H) :
    ((conjugacyClassSum (k := k) g : GroupAlgebraCenter k H) : k[H]).coeff x =
      if ConjClasses.mk x = ConjClasses.mk g then 1 else 0 := by
  classical
  change
    (∑ y : (ConjClasses.mk g).carrier,
      MonoidAlgebra.single (y : H) 1).coeff x = _
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single]
  by_cases hx : ConjClasses.mk x = ConjClasses.mk g
  · let y : (ConjClasses.mk g).carrier :=
      ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr hx⟩
    rw [Finset.sum_eq_single y]
    · simp [y, hx]
    · intro z _ hzy
      have hzx : (z : H) ≠ x := by
        intro hz
        exact hzy (Subtype.ext hz)
      simp [Finsupp.single_apply, hzx]
    · simp [y]
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro y _
    have hyx : (y : H) ≠ x := by
      intro hyx
      apply hx
      calc
        ConjClasses.mk x = ConjClasses.mk (y : H) := by simpa [hyx]
        _ = ConjClasses.mk g :=
          ConjClasses.mem_carrier_iff_mk_eq.mp y.property
    simp [Finsupp.single_apply, hyx]

/-- Coefficients of a quotient-indexed class sum. -/
theorem conjugacyClassSumOfClass_coeff
    (K : ConjClasses H) (x : H) :
    ((conjugacyClassSumOfClass (k := k) K :
      GroupAlgebraCenter k H) : k[H]).coeff x =
      if ConjClasses.mk x = K then 1 else 0 := by
  simpa [conjugacyClassSumOfClass,
    conjugacyClassRepresentative_spec] using
    conjugacyClassSum_coeff (k := k)
      (conjugacyClassRepresentative K) x

/-- The coefficient of a central element on a conjugacy class.  Centrality
makes this independent of the chosen representative. -/
noncomputable def centralClassCoeff
    (z : GroupAlgebraCenter k H) : ConjClasses H → k :=
  Quotient.lift (fun x : H ↦ (z : k[H]).coeff x) (by
    intro x y hxy
    rcases isConj_iff.mp hxy with ⟨u, hu⟩
    rw [← hu]
    exact (GroupAlgebraCenter.coeff_conjugate z u x).symm)

@[simp]
theorem centralClassCoeff_mk
    (z : GroupAlgebraCenter k H) (x : H) :
    centralClassCoeff z (ConjClasses.mk x) = (z : k[H]).coeff x :=
  rfl

/-- Every central group algebra element is the finite linear combination of
unnormalised conjugacy class sums determined by its class coefficients. -/
theorem centralClassSumExpansion
    (z : GroupAlgebraCenter k H) :
    (∑ K : ConjClasses H,
      centralClassCoeff z K • conjugacyClassSumOfClass (k := k) K) = z := by
  classical
  apply Subtype.ext
  ext x
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  change
    (∑ K : ConjClasses H,
      centralClassCoeff z K •
        ((conjugacyClassSumOfClass (k := k) K :
          GroupAlgebraCenter k H) : k[H])).coeff x =
      (z : k[H]).coeff x
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply,
    conjugacyClassSumOfClass_coeff, smul_eq_mul]
  rw [Finset.sum_eq_single (ConjClasses.mk x)]
  · simp
  · intro K _ hK
    have hne : ConjClasses.mk x ≠ K := Ne.symm hK
    simp [hne]
  · simp

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
