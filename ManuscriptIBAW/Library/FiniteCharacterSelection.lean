import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic

/-!
# Finite scalar products and character selection

When ordinary character values span the functions on a finite set of
conjugacy classes, a localized scalar product detects every nonzero restriction
of a dual generalized Gelfand--Graev character. This rules out an empty
column of multiplicities. Natural multiplicities with row sum one give
distinct characters with the required delta values.

The results below are finite linear algebra and arithmetic. They do not
construct character sheaves, geometric supports or Alvis--Curtis duality.
The trace expansions, Gram identities and scalar product formulas used in
an application must concern the same specified functions.
-/

noncomputable section

open scoped BigOperators

namespace ManuscriptIBAW.FiniteCharacterSelection

universe u v w x

attribute [local instance] Classical.propDecidable

section Pairing

variable {K : Type u} [Field K] {I : Type v} {J : Type w} {R : Type x}
variable [Fintype J]

/-- The finite expression obtained after restricting a scalar product to
the specified conjugacy classes. -/
def weightedPairing (weights values restriction : J → K) : K :=
  ∑ j, weights j * values j * restriction j

/-- With the second function fixed, the finite pairing is linear in values. -/
def weightedPairingLinear (weights restriction : J → K) : (J → K) →ₗ[K] K where
  toFun values := weightedPairing weights values restriction
  map_add' a b := by
    simp [weightedPairing, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    simp [weightedPairing, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Full span of the value rows detects a vector through nonzero class
weights. No rank condition on a multiplicity matrix is used. -/
theorem restriction_eq_zero_of_pairings_eq_zero
    (values : I → J → K) (weights restriction : J → K)
    (spanning : Submodule.span K (Set.range values) = ⊤)
    (weights_ne_zero : ∀ j, weights j ≠ 0)
    (pairings_zero : ∀ i, weightedPairing weights (values i) restriction = 0) :
    restriction = 0 := by
  classical
  let L := weightedPairingLinear weights restriction
  have span_le : Submodule.span K (Set.range values) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact pairings_zero i
  have all_mem : ∀ v : J → K, v ∈ LinearMap.ker L := by
    intro v
    apply span_le
    rw [spanning]
    trivial
  funext j
  have at_j := all_mem (fun k => if k = j then 1 else 0)
  have product_zero : weights j * restriction j = 0 := by
    simpa [LinearMap.mem_ker, L, weightedPairingLinear, weightedPairing] using at_j
  exact (mul_eq_zero.mp product_zero).resolve_left (weights_ne_zero j)

/-- Value rank and a nonzero restricted dual function rule out an empty
multiplicity column through the localized duality identity. The row factor
may include the sign in Alvis--Curtis duality. -/
theorem coverage_of_span
    (values : I → J → K) (restrictions : R → J → K)
    (weights : J → K) (entries : I → R → K) (rowFactor : I → K)
    (spanning : Submodule.span K (Set.range values) = ⊤)
    (weights_ne_zero : ∀ j, weights j ≠ 0)
    (restriction_ne_zero : ∀ r, restrictions r ≠ 0)
    (pairing_eq : ∀ i r,
      weightedPairing weights (values i) (restrictions r) = rowFactor i * entries i r) :
    ∀ r, ∃ i, entries i r ≠ 0 := by
  intro r
  by_contra empty_column
  push Not at empty_column
  apply restriction_ne_zero r
  apply restriction_eq_zero_of_pairings_eq_zero values weights (restrictions r)
    spanning weights_ne_zero
  intro i
  rw [pairing_eq, empty_column i, mul_zero]

end Pairing

section Spans

variable {K : Type u} [Field K] {I : Type v} {T : Type w}
variable {V : Type x} [AddCommGroup V] [Module K V]

/-- A spanning trace family contained in the span of ordinary value rows
forces those ordinary rows to span. -/
theorem span_eq_top_of_trace_mem
    (values : I → V) (traces : T → V)
    (trace_spanning : Submodule.span K (Set.range traces) = ⊤)
    (trace_mem : ∀ t, traces t ∈ Submodule.span K (Set.range values)) :
    Submodule.span K (Set.range values) = ⊤ := by
  apply top_unique
  rw [← trace_spanning]
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact trace_mem t

/-- Explicit finite trace expansions give the required containment. The
coefficient support is finite even when the entire character family is not
equipped with an enumeration. -/
theorem span_eq_top_of_trace_expansions
    (values : I → V) (traces : T → V) (coefficients : T → I →₀ K)
    (trace_spanning : Submodule.span K (Set.range traces) = ⊤)
    (expansion : ∀ t, traces t = Finsupp.linearCombination K values (coefficients t)) :
    Submodule.span K (Set.range values) = ⊤ := by
  apply span_eq_top_of_trace_mem values traces trace_spanning
  intro t
  rw [← Finsupp.range_linearCombination]
  exact ⟨coefficients t, (expansion t).symm⟩

variable {J : Type w} [Fintype J]

/-- A diagonal Gram identity with nonzero diagonal entries proves linear
independence by applying its linear functionals to a relation. -/
theorem linearIndependent_of_diagonal_pairings
    (vectors : J → V) (test : J → V →ₗ[K] K) (diagonal : J → K)
    (diagonal_ne_zero : ∀ j, diagonal j ≠ 0)
    (pairing : ∀ i j, test i (vectors j) = if i = j then diagonal i else 0) :
    LinearIndependent K vectors := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients relation i
  have paired := congrArg (test i) relation
  have product_zero : coefficients i * diagonal i = 0 := by
    simpa [map_sum, pairing, Finset.sum_ite_irrel, smul_eq_mul] using paired
  exact (mul_eq_zero.mp product_zero).resolve_right (diagonal_ne_zero i)

/-- In a finite function space, a square diagonal pairing also proves full
span of the tested value rows. -/
theorem span_eq_top_of_diagonal_pairings
    (vectors : J → J → K) (test : J → (J → K) →ₗ[K] K) (diagonal : J → K)
    (diagonal_ne_zero : ∀ j, diagonal j ≠ 0)
    (pairing : ∀ i j, test i (vectors j) = if i = j then diagonal i else 0) :
    Submodule.span K (Set.range vectors) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card
    (linearIndependent_of_diagonal_pairings vectors test diagonal diagonal_ne_zero pairing)]
  exact (Module.finrank_fintype_fun_eq_card K).symm

/-- Independent modified functions contained in the span of an equally
indexed family prove independence of that family. This is the finite
change of functions needed after a Gram calculation. -/
theorem linearIndependent_of_spanning_independent_family
    (vectors modified : J → V)
    (modified_independent : LinearIndependent K modified)
    (modified_mem : ∀ j, modified j ∈ Submodule.span K (Set.range vectors)) :
    LinearIndependent K vectors := by
  let : FiniteDimensional K (Submodule.span K (Set.range vectors)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range vectors)
  apply linearIndependent_iff_card_le_finrank_span.mpr
  rw [← finrank_span_eq_card modified_independent]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact modified_mem j

end Spans

section Selection

variable {I : Type v} {J : Type w} [Fintype J]

/-- A nonzero entry in a natural row of sum one is its unique entry one. -/
theorem nat_row_delta_at (row : J → ℕ) (sum_one : ∑ j, row j = 1)
    (j : J) (nonzero : row j ≠ 0) :
    ∀ k, row k = if k = j then 1 else 0 := by
  classical
  have le_one : row j ≤ 1 := by
    simpa [sum_one] using
      (Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (row k))
        (Finset.mem_univ j))
  have at_j : row j = 1 := by omega
  intro k
  by_cases same : k = j
  · simpa [same] using at_j
  · have pair_le : row j + row k ≤ 1 := by
      have bound := Finset.sum_le_sum_of_subset (f := row)
        (show ({j, k} : Finset J) ⊆ Finset.univ by simp)
      simpa [same, Ne.symm same, sum_one] using bound
    simp only [if_neg same]
    omega

/-- Coverage and natural row sums one yield distinct rows with prescribed
delta values. No bijection or selected row is assumed. -/
theorem exists_delta_injection
    (entries : I → J → ℕ) (sum_one : ∀ i, ∑ j, entries i j = 1)
    (coverage : ∀ j, ∃ i, entries i j ≠ 0) :
    ∃ select : J → I, Function.Injective select ∧
      ∀ j k, entries (select j) k = if k = j then 1 else 0 := by
  classical
  let select : J → I := fun j => Classical.choose (coverage j)
  have delta : ∀ j k, entries (select j) k = if k = j then 1 else 0 := by
    intro j
    exact nat_row_delta_at (entries (select j)) (sum_one (select j)) j
      (Classical.choose_spec (coverage j))
  refine ⟨select, ?_, delta⟩
  intro j k same
  by_contra different
  have equality := congrArg (fun i => entries i j) same
  rw [delta j j, delta k j] at equality
  simp [different] at equality

variable {K : Type u} [Field K] [CharZero K]

/-- The same selection for scalar products known to be natural numbers
inside a field of characteristic zero. -/
theorem exists_delta_injection_of_nonnegative
    (entries : I → J → K)
    (nonnegative : ∀ i j, ∃ a : ℕ, entries i j = (a : K))
    (sum_one : ∀ i, ∑ j, entries i j = 1)
    (coverage : ∀ j, ∃ i, entries i j ≠ 0) :
    ∃ select : J → I, Function.Injective select ∧
      ∀ j k, entries (select j) k = if k = j then 1 else 0 := by
  classical
  let a : I → J → ℕ := fun i j => Classical.choose (nonnegative i j)
  have cast_a : ∀ i j, (a i j : K) = entries i j := by
    intro i j
    exact (Classical.choose_spec (nonnegative i j)).symm
  have natural_sum : ∀ i, ∑ j, a i j = 1 := by
    intro i
    apply Nat.cast_injective (R := K)
    push_cast
    simpa only [cast_a] using sum_one i
  have natural_coverage : ∀ j, ∃ i, a i j ≠ 0 := by
    intro j
    obtain ⟨i, nonzero⟩ := coverage j
    refine ⟨i, ?_⟩
    intro zero
    apply nonzero
    rw [← cast_a, zero, Nat.cast_zero]
  obtain ⟨select, injective, delta⟩ :=
    exists_delta_injection a natural_sum natural_coverage
  refine ⟨select, injective, ?_⟩
  intro j k
  rw [← cast_a, delta]
  split_ifs <;> simp

/-- The finite coverage argument and natural row arithmetic together give
the desired delta selection. -/
theorem exists_delta_injection_of_span
    (values : I → J → K) (restrictions : J → J → K)
    (weights : J → K) (entries : I → J → K) (rowFactor : I → K)
    (spanning : Submodule.span K (Set.range values) = ⊤)
    (weights_ne_zero : ∀ j, weights j ≠ 0)
    (restriction_ne_zero : ∀ j, restrictions j ≠ 0)
    (pairing_eq : ∀ i j,
      weightedPairing weights (values i) (restrictions j) = rowFactor i * entries i j)
    (nonnegative : ∀ i j, ∃ a : ℕ, entries i j = (a : K))
    (sum_one : ∀ i, ∑ j, entries i j = 1) :
    ∃ select : J → I, Function.Injective select ∧
      ∀ j k, entries (select j) k = if k = j then 1 else 0 :=
  exists_delta_injection_of_nonnegative entries nonnegative sum_one
    (coverage_of_span values restrictions weights entries rowFactor spanning
      weights_ne_zero restriction_ne_zero pairing_eq)

end Selection

end ManuscriptIBAW.FiniteCharacterSelection

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
