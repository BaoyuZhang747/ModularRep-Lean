import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
import ModularRep.PaperProofs.CyclicOuterLemma37Concrete
import ManuscriptIBAW.Library.FiniteClassPairing
import ManuscriptIBAW.Library.FiniteCharacterSelection

/-!
# Character selection for the selected symplectic families

This file proves the finite deductions in manuscript Lemma 2.12 for the
actual conformal symplectic group. The chosen family is the family supplied
by Taylor 2014, Theorem 2.11, Proposition 10.2 and Section 10.3, for the
specified geometric class. Identifying that family and its geometric class
with the parameters below remains an external source interpretation.

The trace expansions concern the original rational Frobenius. The trace
rows are evaluated at inverse representatives. Their test functionals and
diagonal identities use the same convention. Their geometric justification, including condition (P4), the auxiliary Frobenius,
Geck's restriction theorem and Shoji's comparison, is not formalised here.
The modified GGGR, support and duality identities and the weighted scalar
product formula are separate assumptions on the same actual functions.
From them we prove value spanning, independence of restricted dual GGGRs,
localisation of scalar products, coverage and row sums equal to one. These
deductions give distinct characters with the required delta scalar products.

The positive dual is the irreducible character associated with
Alvis–Curtis duality, with its sign removed.

The argument does not require isolation. Restriction to Sp and P5
descent are treated separately.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeC.GGGRSelection

universe u

open ModularRep OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs
open OddTwoConformalProjectiveRealisation (CSp)
open scoped BigOperators

attribute [local instance] Classical.propDecidable

local instance (priority := low) finiteFintype (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {m p : ℕ} {F K : Type u} [Field F] [Finite F]
  [Field K] [CharZero K]

/-- Actual conjugacy classes containing an element of order a power of p.
Their identification with algebraic unipotent classes is part of the
geometric source interpretation, as in the Type B class carrier. -/
def UnipotentClass (m p : ℕ) (F : Type u) [Field F] : Type u :=
  {c : ConjClasses (CSp m F) //
    ∃ g : CSp m F, ConjClasses.mk g = c ∧ ∃ a : ℕ, g ^ (p ^ a) = 1}

instance unipotentClass_finite : Finite (UnipotentClass m p F) := by
  letI : Finite (ConjClasses (CSp m F)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  unfold UnipotentClass
  infer_instance

variable {GeometricClass : Type u}
  (geometricClass : UnipotentClass m p F → GeometricClass) (C : GeometricClass)

/-- The complete fibre of actual rational classes with the chosen geometric
label. The label's algebraic interpretation is supplied externally. -/
abbrev RationalFibre := {c : UnipotentClass m p F // geometricClass c = C}

/-- A representative of the actual rational class. -/
def representative (u : RationalFibre geometricClass C) : CSp m F :=
  Classical.choose u.val.property

theorem representative_class (u : RationalFibre geometricClass C) :
    ConjClasses.mk (representative geometricClass C u) = u.val.val :=
  (Classical.choose_spec u.val.property).1

/-- The normalised finite scalar product, using inverse values of the first
character. Over the complex numbers these are its conjugate values. -/
def scalarProduct (x y : CSp m F → K) : K :=
  (Nat.card (CSp m F) : K)⁻¹ * ∑ g, x g⁻¹ * y g

variable {geometricClass C}
  {family : Set (Irr K (CSp m F))}
  {dual : Irr K (CSp m F) → Irr K (CSp m F)}
  {gamma : RationalFibre geometricClass C → CSp m F → K}

/-- The actual fixed subgroup of a component Frobenius automorphism. -/
def componentFixedSubgroup {V : Type u} [Group V] (sigma : MulAut V) : Subgroup V where
  carrier := {v | sigma v = v}
  one_mem' := map_one sigma
  mul_mem' hx hy := (map_mul sigma _ _).trans (congrArg₂ (· * ·) hx hy)
  inv_mem' hx := (map_inv sigma _).trans (congrArg Inv.inv hx)

theorem componentFixedSubgroup_eq_top {V : Type u} [Group V] {sigma : MulAut V}
    (trivial : sigma = 1) : componentFixedSubgroup sigma = ⊤ := by
  subst sigma
  ext v
  simp [componentFixedSubgroup]

/-- The weighted formula and denominator for the chosen upper family.
The finite group V is the specified component group. Trivial component
Frobenius and the formula for the index of its fixed subgroup imply that
the weights are one. The unweighted row sum and column coverage are proved.
The formula and denominator equality are those used in Lemma 2.12 from
Taylor 2016, Lemma 14.15 and Proposition 15.4, with the stated family data. -/
structure WeightedSource (V : Type u) [Group V]
    (geometricClass : UnipotentClass m p F → GeometricClass) (C : GeometricClass)
    (family : Set (Irr K (CSp m F)))
    (dual : Irr K (CSp m F) → Irr K (CSp m F))
    (gamma : RationalFibre geometricClass C → CSp m F → K) where
  nonnegative : ∀ Phi ∈ family, ∀ u,
    ∃ a : ℕ, scalarProduct (dual Phi).val (gamma u) = (a : K)
  frobeniusIndex : RationalFibre geometricClass C → ℕ
  componentFrobenius : RationalFibre geometricClass C → MulAut V
  componentFrobenius_trivial : ∀ u, componentFrobenius u = 1
  frobeniusIndex_eq : ∀ u, frobeniusIndex u =
    (componentFixedSubgroup (componentFrobenius u)).index
  genericDenominator : Irr K (CSp m F) → ℕ
  dualDenominator_eq : ∀ Phi ∈ family, genericDenominator (dual Phi) = Nat.card V
  weightedSum : ∀ Phi ∈ family,
    ∑ u, (frobeniusIndex u : K) * scalarProduct (dual Phi).val (gamma u) =
      (Nat.card V : K) / (genericDenominator (dual Phi) : K)

variable {V : Type u} [Group V] [Finite V]

theorem WeightedSource.frobeniusIndex_one
    (source : WeightedSource V geometricClass C family dual gamma)
    (u : RationalFibre geometricClass C) : source.frobeniusIndex u = 1 := by
  rw [source.frobeniusIndex_eq, componentFixedSubgroup_eq_top
    (source.componentFrobenius_trivial u)]
  exact Subgroup.index_top

theorem WeightedSource.sum_one
    (source : WeightedSource V geometricClass C family dual gamma)
    (Phi : Irr K (CSp m F)) (hPhi : Phi ∈ family) :
    ∑ u, scalarProduct (dual Phi).val (gamma u) = 1 := by
  have nonzero : (Nat.card V : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  simpa only [source.frobeniusIndex_one, Nat.cast_one, one_mul,
    source.dualDenominator_eq Phi hPhi, div_self nonzero] using source.weightedSum Phi hPhi

/-- The finite trace and GGGR identities for the selected Type C family.
The first expansion uses character sheaf traces for the original Frobenius,
evaluated at inverse representatives, and Shoji's comparison. The source
interpretation transports the test functionals and diagonal identity along
inversion of the rational classes in the chosen geometric class. The
identities use inverse evaluations and require no conjugation operation
on K. The second expansion uses the modified GGGR functions and the
diagonal identities obtained from Taylor 2016, (11.15), Theorem 11.13
and Lemma 11.16. Support and duality are the identities used in the same
manuscript proof. Their validity for these actual functions is external.
Spanning, independence and coverage are proved below. -/
structure ValueSource
    (geometricClass : UnipotentClass m p F → GeometricClass) (C : GeometricClass)
    (family : Set (Irr K (CSp m F)))
    (dual : Irr K (CSp m F) → Irr K (CSp m F))
    (gamma : RationalFibre geometricClass C → CSp m F → K) where
  traceValues : RationalFibre geometricClass C → RationalFibre geometricClass C → K
  traceTest : RationalFibre geometricClass C →
    (RationalFibre geometricClass C → K) →ₗ[K] K
  traceDiagonal : RationalFibre geometricClass C → K
  traceDiagonal_ne_zero : ∀ j, traceDiagonal j ≠ 0
  tracePairing : ∀ i j, traceTest i (traceValues j) =
    if i = j then traceDiagonal i else 0
  traceCoefficients : RationalFibre geometricClass C → family →₀ K
  actualFTraceExpansion : ∀ j, traceValues j = Finsupp.linearCombination K
    (fun Phi : family => fun u : RationalFibre geometricClass C =>
      Phi.val.val ((representative geometricClass C u)⁻¹)) (traceCoefficients j)
  dualGamma : RationalFibre geometricClass C → CSp m F → K
  modifiedValues : RationalFibre geometricClass C → RationalFibre geometricClass C → K
  modifiedTest : RationalFibre geometricClass C →
    (RationalFibre geometricClass C → K) →ₗ[K] K
  modifiedDiagonal : RationalFibre geometricClass C → K
  modifiedDiagonal_ne_zero : ∀ j, modifiedDiagonal j ≠ 0
  modifiedPairing : ∀ i j, modifiedTest i (modifiedValues j) =
    if i = j then modifiedDiagonal i else 0
  modifiedCoefficients : RationalFibre geometricClass C →
    RationalFibre geometricClass C →₀ K
  modifiedExpansion : ∀ j, modifiedValues j = Finsupp.linearCombination K
    (fun u => fun v : RationalFibre geometricClass C =>
      dualGamma u (representative geometricClass C v)) (modifiedCoefficients j)
  dualGamma_class : ∀ (j u : RationalFibre geometricClass C) (x : CSp m F),
    ConjClasses.mk x = u.val.val →
      dualGamma j x = dualGamma j (representative geometricClass C u)
  dualSupport : RationalFibre geometricClass C → Set (CSp m F)
  dualGamma_support : ∀ j x, x ∉ dualSupport j → dualGamma j x = 0
  pointwiseVanishing : ∀ Phi ∈ family, ∀ j x, x ∈ dualSupport j →
    (∀ u : RationalFibre geometricClass C, ConjClasses.mk x ≠ u.val.val) →
      Phi.val x⁻¹ = 0
  dualityFactor : family → K
  alvisCurtisPairing : ∀ (Phi : family) j,
    scalarProduct Phi.val.val (dualGamma j) =
      dualityFactor Phi * scalarProduct (dual Phi.val).val (gamma j)

variable (source : ValueSource geometricClass C family dual gamma)

include source in
theorem ValueSource.value_span :
    Submodule.span K (Set.range (fun Phi : family =>
      fun u : RationalFibre geometricClass C =>
        Phi.val.val ((representative geometricClass C u)⁻¹))) = ⊤ := by
  apply FiniteCharacterSelection.span_eq_top_of_trace_expansions _
    source.traceValues source.traceCoefficients
  · exact FiniteCharacterSelection.span_eq_top_of_diagonal_pairings
      source.traceValues source.traceTest source.traceDiagonal
      source.traceDiagonal_ne_zero (by
        intro i j
        by_cases h : i = j <;> simpa [h] using source.tracePairing i j)
  · exact source.actualFTraceExpansion

theorem ValueSource.dualRestriction_independent :
    LinearIndependent K (fun u => fun v : RationalFibre geometricClass C =>
      source.dualGamma u (representative geometricClass C v)) := by
  apply FiniteCharacterSelection.linearIndependent_of_spanning_independent_family _
    source.modifiedValues
  · exact FiniteCharacterSelection.linearIndependent_of_diagonal_pairings
      source.modifiedValues source.modifiedTest source.modifiedDiagonal
      source.modifiedDiagonal_ne_zero (by
        intro i j
        by_cases h : i = j <;> simpa [h] using source.modifiedPairing i j)
  · intro j
    rw [← Finsupp.range_linearCombination]
    exact ⟨source.modifiedCoefficients j, (source.modifiedExpansion j).symm⟩

theorem ordinary_inverse_class (Phi : Irr K (CSp m F)) {x u : CSp m F}
    (same : ConjClasses.mk x = ConjClasses.mk u) : Phi.val x⁻¹ = Phi.val u⁻¹ := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp same)
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using
    (CyclicOuterLemma37Concrete.ordinaryCharacter_conj Phi g x⁻¹).symm

/-- The literal rational class size divided by the order of CSp. These
weights are distinct from the component indices in the weighted sum. -/
def rationalClassWeight (u : RationalFibre geometricClass C) : K :=
  ((FiniteClassPairing.fibre ConjClasses.mk
    (fun v : RationalFibre geometricClass C => v.val.val) u).card : K) /
      (Fintype.card (CSp m F) : K)

theorem rationalClassWeight_ne_zero (u : RationalFibre geometricClass C) :
    rationalClassWeight (K := K) u ≠ 0 :=
  FiniteClassPairing.weight_ne_zero _ _ (representative geometricClass C)
    (representative_class geometricClass C) u

theorem ValueSource.localized_pairing (Phi : family)
    (j : RationalFibre geometricClass C) :
    scalarProduct Phi.val.val (source.dualGamma j) =
      FiniteCharacterSelection.weightedPairing rationalClassWeight
        (fun u : RationalFibre geometricClass C =>
          Phi.val.val ((representative geometricClass C u)⁻¹))
        (fun u => source.dualGamma j (representative geometricClass C u)) := by
  have localized := FiniteClassPairing.sum_localize ConjClasses.mk
    (fun u : RationalFibre geometricClass C => u.val.val)
    (fun a b h => Subtype.ext (Subtype.ext h))
    (fun x => Phi.val.val x⁻¹ * source.dualGamma j x)
    (fun u => Phi.val.val ((representative geometricClass C u)⁻¹) *
      source.dualGamma j (representative geometricClass C u))
    (fun u x h => by
      rw [ordinary_inverse_class Phi.val
        (h.trans (representative_class geometricClass C u).symm), source.dualGamma_class j u x h])
    (fun x hx => by
      by_cases supported : x ∈ source.dualSupport j
      · rw [source.pointwiseVanishing Phi.val Phi.property j x supported hx, zero_mul]
      · rw [source.dualGamma_support j x supported, mul_zero])
  unfold scalarProduct
  rw [localized, Finset.mul_sum]
  unfold FiniteCharacterSelection.weightedPairing rationalClassWeight
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.card_eq_nat_card]
  simp only [div_eq_mul_inv]
  ring

include source in
theorem ValueSource.coverage :
    ∀ u, ∃ Phi ∈ family, scalarProduct (dual Phi).val (gamma u) ≠ 0 := by
  have covered := FiniteCharacterSelection.coverage_of_span
    (fun Phi : family => fun u => Phi.val.val ((representative geometricClass C u)⁻¹))
    (fun j => fun u => source.dualGamma j (representative geometricClass C u))
    rationalClassWeight
    (fun Phi : family => fun u => scalarProduct (dual Phi.val).val (gamma u))
    source.dualityFactor source.value_span rationalClassWeight_ne_zero
    (fun j => source.dualRestriction_independent.ne_zero j)
    (fun Phi j => (source.localized_pairing Phi j).symm.trans (source.alvisCurtisPairing Phi j))
  intro u
  obtain ⟨Phi, nonzero⟩ := covered u
  exact ⟨Phi.val, Phi.property, nonzero⟩

/-- Source assumptions for the particular family selected in Lemma 2.12.
The source requires rank at least three and an odd finite field. Its
interpretation identifies the family, geometric label, GGGRs, positive dual
and finite component group with Taylor's selected data. The geometric
justification of these identities for that family remains external. -/
structure SelectedFamilySource (V : Type u) [Group V] [Finite V]
    (geometricClass : UnipotentClass m p F → GeometricClass) (C : GeometricClass)
    (family : Set (Irr K (CSp m F)))
    (dual : Irr K (CSp m F) → Irr K (CSp m F))
    (gamma : RationalFibre geometricClass C → CSp m F → K) [CharP F p] where
  rank_ge_three : 3 ≤ m
  field_odd : Odd (Nat.card F)
  weights : WeightedSource V geometricClass C family dual gamma
  values : ValueSource geometricClass C family dual gamma

/-- Manuscript Lemma 2.12 under the explicit source assumptions above.
The selected characters belong to the specified actual CSp family. Their
distinctness and all delta scalar products are conclusions of the proof. -/
theorem delta_selection [CharP F p]
    (selected : SelectedFamilySource V geometricClass C family dual gamma) :
    ∃ select : RationalFibre geometricClass C → family,
      Function.Injective select ∧ ∀ j k,
        scalarProduct (dual (select j).val).val (gamma k) = if k = j then 1 else 0 := by
  have covered : ∀ j, ∃ Phi : family,
      scalarProduct (dual Phi.val).val (gamma j) ≠ 0 := by
    intro j
    obtain ⟨Phi, mem, nonzero⟩ := selected.values.coverage j
    exact ⟨⟨Phi, mem⟩, nonzero⟩
  obtain ⟨select, injective, delta⟩ :=
    FiniteCharacterSelection.exists_delta_injection_of_nonnegative
      (fun Phi : family => fun j => scalarProduct (dual Phi.val).val (gamma j))
      (fun Phi j => selected.weights.nonnegative Phi.val Phi.property j)
      (fun Phi => selected.weights.sum_one Phi.val Phi.property) covered
  refine ⟨select, injective, ?_⟩
  intro j k
  by_cases equal : k = j
  · simpa only [if_pos equal] using delta j k
  · simpa only [if_neg equal] using delta j k

end ManuscriptIBAW.TypeC.GGGRSelection

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
