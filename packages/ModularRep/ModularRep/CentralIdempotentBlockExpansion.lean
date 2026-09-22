import ModularRep.PrimitiveCentralIdempotent

/-!
# Expansion of a central idempotent in a primitive central family

Every central idempotent in a ring is the sum of exactly those members of a
finite complete primitive central idempotent family that it fixes.  This file
is purely ring-theoretic and contains no block-theoretic or character-theoretic
input.
-/

open scoped BigOperators

namespace ModularRep

namespace IsPrimitiveCentralIdempotent

variable {A : Type*} [Ring A] {b c : A}

/-- Multiplication of a primitive central idempotent by any central
idempotent is either zero or the primitive idempotent itself. -/
theorem mul_eq_zero_or_eq_self_of_central_idempotent
    (hb : IsPrimitiveCentralIdempotent b)
    (hcIdempotent : IsIdempotentElem c) (hcCentral : IsMulCentral c) :
    b * c = 0 ∨ b * c = b := by
  apply hb.eq_zero_or_eq_self
  · exact IsIdempotentElem.mul_of_commute (hb.central.comm c)
      hb.idempotent hcIdempotent
  · exact Set.mul_mem_center hb.central hcCentral
  · calc
      (b * c) * b = b * (c * b) := mul_assoc _ _ _
      _ = b * (b * c) := by rw [hcCentral.comm b]
      _ = (b * b) * c := (mul_assoc _ _ _).symm
      _ = b * c := by rw [hb.idempotent.eq]

end IsPrimitiveCentralIdempotent

namespace CompleteOrthogonalCentralIdempotents

variable {A ι : Type*} [Ring A] [Fintype ι]
variable {e : ι → A}

/-- Indices on which multiplication by `c` is nonzero.  For a central
idempotent and a primitive family, these are exactly the indices fixed by
`c`. -/
noncomputable def centralIdempotentSupport
    (_E : CompleteOrthogonalCentralIdempotents e) (c : A) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ e i * c ≠ 0

@[simp]
theorem mem_centralIdempotentSupport
    (E : CompleteOrthogonalCentralIdempotents e) (c : A) (i : ι) :
    i ∈ E.centralIdempotentSupport c ↔ e i * c ≠ 0 := by
  classical
  simp [centralIdempotentSupport]

/-- For a central idempotent, nonzero support at a primitive family member is
equivalent to right multiplication fixing that member. -/
theorem mem_centralIdempotentSupport_iff_mul_eq_self
    (E : CompleteOrthogonalCentralIdempotents e)
    (hprimitive : ∀ i, IsPrimitiveCentralIdempotent (e i))
    {c : A} (hcIdempotent : IsIdempotentElem c) (hcCentral : IsMulCentral c)
    (i : ι) :
    i ∈ E.centralIdempotentSupport c ↔ e i * c = e i := by
  rw [E.mem_centralIdempotentSupport]
  constructor
  · intro hne
    exact ((hprimitive i).mul_eq_zero_or_eq_self_of_central_idempotent
      hcIdempotent hcCentral).resolve_left hne
  · intro hself hzero
    apply (hprimitive i).ne_zero
    calc
      e i = e i * c := hself.symm
      _ = 0 := hzero

/-- Equivalently, a supported primitive family member is fixed by left
multiplication by the central idempotent. -/
theorem mem_centralIdempotentSupport_iff_left_mul_eq_self
    (E : CompleteOrthogonalCentralIdempotents e)
    (hprimitive : ∀ i, IsPrimitiveCentralIdempotent (e i))
    {c : A} (hcIdempotent : IsIdempotentElem c) (hcCentral : IsMulCentral c)
    (i : ι) :
    i ∈ E.centralIdempotentSupport c ↔ c * e i = e i := by
  simpa only [(hcCentral.comm (e i)).eq] using
    E.mem_centralIdempotentSupport_iff_mul_eq_self hprimitive
      hcIdempotent hcCentral i

/-- A central idempotent is the sum of exactly its supported primitive
central family members. -/
theorem sum_centralIdempotentSupport_eq
    (E : CompleteOrthogonalCentralIdempotents e)
    (hprimitive : ∀ i, IsPrimitiveCentralIdempotent (e i))
    {c : A} (hcIdempotent : IsIdempotentElem c) (hcCentral : IsMulCentral c) :
    (∑ i ∈ E.centralIdempotentSupport c, e i) = c := by
  classical
  calc
    (∑ i ∈ E.centralIdempotentSupport c, e i) =
        ∑ i : ι, if e i * c ≠ 0 then e i else 0 := by
      simp only [centralIdempotentSupport, Finset.sum_filter]
    _ = ∑ i : ι, e i * c := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hzero : e i * c = 0
      · simp [hzero]
      · have hself : e i * c = e i :=
          ((hprimitive i).mul_eq_zero_or_eq_self_of_central_idempotent
            hcIdempotent hcCentral).resolve_left hzero
        rw [if_pos hzero, hself]
    _ = (∑ i : ι, e i) * c := by rw [Finset.sum_mul]
    _ = 1 * c := congrArg (fun x : A ↦ x * c) E.complete
    _ = c := one_mul c

/-- The supported index set is the unique subset of the primitive family
whose sum is the central idempotent. -/
theorem eq_centralIdempotentSupport_of_sum_eq
    (E : CompleteOrthogonalCentralIdempotents e)
    (hprimitive : ∀ i, IsPrimitiveCentralIdempotent (e i))
    {c : A} (hcIdempotent : IsIdempotentElem c) (hcCentral : IsMulCentral c)
    (s : Finset ι) (hs : (∑ i ∈ s, e i) = c) :
    s = E.centralIdempotentSupport c := by
  classical
  ext i
  constructor
  · intro hi
    apply (E.mem_centralIdempotentSupport_iff_mul_eq_self hprimitive
      hcIdempotent hcCentral i).2
    calc
      e i * c = e i * (∑ j ∈ s, e j) :=
        congrArg (fun x : A ↦ e i * x) hs.symm
      _ = ∑ j ∈ s, e i * e j := by rw [Finset.mul_sum]
      _ = e i * e i := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact E.ortho (Ne.symm hji)
        · intro hiNotMem
          exact (hiNotMem hi).elim
      _ = e i := (E.idem i).eq
  · intro hiSupport
    have hfix : e i * c = e i :=
      (E.mem_centralIdempotentSupport_iff_mul_eq_self hprimitive
        hcIdempotent hcCentral i).1 hiSupport
    by_contra hi
    apply (hprimitive i).ne_zero
    calc
      e i = e i * c := hfix.symm
      _ = e i * (∑ j ∈ s, e j) :=
        congrArg (fun x : A ↦ e i * x) hs.symm
      _ = ∑ j ∈ s, e i * e j := by rw [Finset.mul_sum]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hij : i ≠ j := by
          intro hij
          subst j
          exact hi hj
        exact E.ortho hij

end CompleteOrthogonalCentralIdempotents

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
