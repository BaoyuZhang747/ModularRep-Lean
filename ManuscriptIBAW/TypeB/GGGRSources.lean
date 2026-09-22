import ModularRep.PaperProofs.TypeBCurrentPrincipalResults
import ManuscriptIBAW.Library.FiniteClassPairing
import ManuscriptIBAW.Library.FiniteCharacterSelection

/-!
# The two upper character families in the principal GGGR argument

The assumptions are stated in the form used by manuscript Proposition 4.9.
They are used to prove the assertions about fibres over the extraspecial
component group, restriction, the permutation on two elements,
triangularity and the basis theorem in PrincipalApplication.

Taylor's distinguished character has two restriction constituents. A
separate isolated family provides the characters used in manuscript
Lemma 2.11. Each family has its own rational series label. The geometric
argument in that lemma is not formalised. Its trace expansions and the
stated character identities are assumed here, and the finite proofs derive
spanning, independence and coverage from them. The Weyl group and its
trivial Frobenius action are not used in these deductions. The denominator
equality is a separate assumption. The trivial component action is used to
prove that the indices of the fixed subgroups in the weighted sum are one.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.GGGRSources

open ModularRep ModularRep.PaperProofs OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBSpinRationalUnipotentClassBinding TypeBAllRankGGGRFibres
open TypeBAllRankGGGREntries TypeBSpinOrdinaryRestriction
open TypeBCurrentPrincipalResults
open scoped BigOperators

attribute [local instance] Classical.propDecidable

local instance (priority := low) gggrSourceFiniteFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- The actual fixed subgroup used in the GH component index. -/
def componentFixedSubgroup {V : Type} [Group V] (sigma : MulAut V) : Subgroup V where
  carrier := {v | sigma v = v}
  one_mem' := map_one sigma
  mul_mem' hx hy := (map_mul sigma _ _).trans (congrArg₂ (· * ·) hx hy)
  inv_mem' hx := (map_inv sigma _).trans (congrArg Inv.inv hx)

theorem componentFixedSubgroup_eq_top {V : Type} [Group V] {sigma : MulAut V}
    (trivial : sigma = 1) : componentFixedSubgroup sigma = ⊤ := by
  subst sigma
  ext v
  simp [componentFixedSubgroup]

variable {n r f : ℕ} {F K : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  {N : NormSource n F} [Finite (SpecialClifford n F)] [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]

local instance gggrSourceUpperUnipotentFinite :
    Finite (UpperUnipotentClass (n := n) (F := F) (r := r)) := by
  let : Finite (ConjClasses (SpecialClifford n F)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  unfold UpperUnipotentClass
  infer_instance

section Local

variable
  {GeometricClass : Type}
  {geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass}
  {upperGeometricClass : UpperUnipotentClass (n := n) (F := F) (r := r) → GeometricClass}
  {geometric_square : ∀ c, upperGeometricClass (upperClassMap c) = geometricClass c}
  {ComponentGroup : GeometricClass → Type} [∀ C, Group (ComponentGroup C)]
  {gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K}
  {upperDual : Irr K (SpecialClifford n F) → Irr K (SpecialClifford n F)}
  {lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N)}
  {rationalSeries : TypeBConformalDualCarriers.PCSp F n → Irr K (Spin n F N) → Prop}
  {quasiIsolated : TypeBConformalDualCarriers.PCSp F n → Prop}
  {unipotentSupport : Irr K (Spin n F N) → GeometricClass → Prop}

/-- Weighted GGGR and restriction assumptions for one upper family.
The scalar product formula of Lusztig and Geck–Malle, in the form proved
by Taylor 2016, Proposition 15.4 and Lemma 14.15, gives the weighted sum
in odd characteristic. The denominator equality and trivial component
Frobenius action are separate assumptions. The latter, together with the
formula expressing the weights as indices of fixed subgroups, implies
that each weight is one.
Neither coverage of every rational class nor a selection of lower
characters is assumed here. -/
structure FamilySource (V : Type) [Group V]
    (parameters : OddFieldParameters F r f)
    (C : GeometricClass)
    (upperGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K)
    (family : Set (Irr K (SpecialClifford n F))) where
  restriction : RestrictionSource (N := N) family upperDual lowerDual
  upperNonnegative : ∀ Phi ∈ family, ∀ u,
    ∃ a : ℕ, upperScalarProduct (upperDual Phi).val (upperGamma u) = (a : K)
  frobeniusIndex : UpperRationalFibre upperGeometricClass C → ℕ
  componentFrobenius : UpperRationalFibre upperGeometricClass C → MulAut V
  componentFrobenius_trivial : ∀ u, componentFrobenius u = 1
  frobeniusIndex_eq : ∀ u, frobeniusIndex u =
    (componentFixedSubgroup (componentFrobenius u)).index
  componentOrder_pos : 0 < Nat.card V
  genericDenominator : Irr K (SpecialClifford n F) → ℕ
  dualDenominator_eq : ∀ Phi ∈ family,
    genericDenominator (upperDual Phi) = Nat.card V
  weightedSum : ∀ Phi ∈ family,
    ∑ u, (frobeniusIndex u : K) *
      upperScalarProduct (upperDual Phi).val (upperGamma u) =
        (Nat.card V : K) / (genericDenominator (upperDual Phi) : K)
  gggrInduction : ∀ c : RationalFibre geometricClass C,
    upperGamma (rationalClassMap geometricClass upperGeometricClass geometric_square C c) =
      induceSpinFunction (gamma c.val)
  gggrConjugation : ∀ (g : SpecialClifford n F) (c : RationalFibre geometricClass C),
    gamma (ambientClassEquiv geometricClass upperGeometricClass geometric_square C g c).val =
      fun x => gamma c.val (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹ x)

variable {parameters : OddFieldParameters F r f} {higher : 4 ≤ n}
  {V : Type} [Group V]
  {C : GeometricClass}
  {upperGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K}
  {family : Set (Irr K (SpecialClifford n F))}

omit [CharZero K] [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] in
theorem FamilySource.frobeniusIndex_one
    (source : FamilySource (geometricClass := geometricClass)
      (geometric_square := geometric_square) (gamma := gamma)
      (upperDual := upperDual) (lowerDual := lowerDual) V parameters C upperGamma family)
    (u : UpperRationalFibre upperGeometricClass C) : source.frobeniusIndex u = 1 := by
  rw [source.frobeniusIndex_eq, componentFixedSubgroup_eq_top
    (source.componentFrobenius_trivial u)]
  exact Subgroup.index_top

omit [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] in
theorem FamilySource.upperSumOne
    (source : FamilySource (geometricClass := geometricClass)
      (geometric_square := geometric_square) (gamma := gamma)
      (upperDual := upperDual) (lowerDual := lowerDual) V parameters C upperGamma family)
    (Phi : Irr K (SpecialClifford n F)) (hPhi : Phi ∈ family) :
    ∑ u, upperScalarProduct (upperDual Phi).val (upperGamma u) = 1 := by
  have nonzero : (Nat.card V : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt source.componentOrder_pos)
  simpa only [source.frobeniusIndex_one, Nat.cast_one, one_mul,
    source.dualDenominator_eq Phi hPhi, div_self nonzero] using source.weightedSum Phi hPhi


/-- Inverse values of actual ordinary characters are constant on actual
conjugacy classes. This is proved from their representation realization. -/
theorem ordinary_inverse_class {L H : Type} [Field L] [CharZero L] [Group H]
    (Phi : Irr L H) {x u : H} (same : ConjClasses.mk x = ConjClasses.mk u) :
    Phi.val x⁻¹ = Phi.val u⁻¹ := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp same)
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using
    (CyclicOuterLemma37Concrete.ordinaryCharacter_conj Phi g x⁻¹).symm

/-- A representative of the actual upper rational conjugacy class. -/
def upperRepresentative (u : UpperRationalFibre upperGeometricClass C) :
    SpecialClifford n F := Classical.choose u.val.property

omit [Finite F] [CharP F r] [Finite (SpecialClifford n F)] in
theorem upperRepresentative_class (u : UpperRationalFibre upperGeometricClass C) :
    ConjClasses.mk (upperRepresentative u) = u.val.val :=
  (Classical.choose_spec u.val.property).1

/-- Assumptions for the finite part of manuscript Lemma 2.11, applied to
the isolated family chosen in the proof of Proposition 4.9. The lemma
assumes connected centre, a simply connected derived subgroup of type B_n
with n ≥ 3, and odd q. Its isolated semisimple element is fixed by F and
lies in an F-stable maximal torus contained in an F-stable Borel subgroup
of the dual group. The component group and the family group are elementary
abelian of the same order, and F acts trivially on the component group.

The geometric proof establishing the required trace expansions is not
formalised. It uses Geck 1999, Theorem 4.5, in the setting justified in
the manuscript, and Shoji 1995 II, Theorem 3.2. The modified GGGR
expansions and pairings use Taylor 2016, (11.15), Theorem 11.13 and
Lemma 11.16, and Geck 1994, Lemma 3.5 and Corollary 3.6. The vanishing
and duality identities use Lusztig 1992, Theorem 11.2(iv), Proposition
8.5 and Corollary 8.6, as extended by Taylor 2016, Corollary 13.6,
together with Geck–Malle 2000, Theorem 3.7. The finite selection
argument follows Geck–Hézard 2008, Proposition 4.3.

The stated Weyl group and its trivial Frobenius action are not used in
the finite deductions below. Their identification with the geometric
Weyl group is not formalised, and the denominator equality is assumed
separately in FamilySource. The torus, Borel subgroup and character
sheaves are not constructed. Trace expansions use inverse class
representatives, as does the K-valued scalar product.

This interface concerns the type B character families. The selected
type C families in Lemma 2.12 are treated separately in
ManuscriptIBAW.TypeC.GGGRSelection, which proves the finite character
selection from its explicit trace and scalar product assumptions. -/
structure IsolatedValueSource
    (C : GeometricClass)
    (upperGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K)
    (family : Set (Irr K (SpecialClifford n F))) where
  WeylGroup : Type
  weylGroup : Group WeylGroup
  weylFrobenius : letI := weylGroup; MulAut WeylGroup
  weylFrobenius_trivial : weylFrobenius = 1
  traceValues : UpperRationalFibre upperGeometricClass C →
    UpperRationalFibre upperGeometricClass C → K
  traceTest : UpperRationalFibre upperGeometricClass C →
    (UpperRationalFibre upperGeometricClass C → K) →ₗ[K] K
  traceDiagonal : UpperRationalFibre upperGeometricClass C → K
  traceDiagonal_ne_zero : ∀ j, traceDiagonal j ≠ 0
  tracePairing : ∀ i j, traceTest i (traceValues j) =
    if i = j then traceDiagonal i else 0
  traceCoefficients : UpperRationalFibre upperGeometricClass C → family →₀ K
  actualFTraceExpansion : ∀ j, traceValues j = Finsupp.linearCombination K
    (fun Phi : family => fun u : UpperRationalFibre upperGeometricClass C =>
      Phi.val.val (upperRepresentative u)⁻¹)
    (traceCoefficients j)
  dualGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K
  modifiedValues : UpperRationalFibre upperGeometricClass C →
    UpperRationalFibre upperGeometricClass C → K
  modifiedTest : UpperRationalFibre upperGeometricClass C →
    (UpperRationalFibre upperGeometricClass C → K) →ₗ[K] K
  modifiedDiagonal : UpperRationalFibre upperGeometricClass C → K
  modifiedDiagonal_ne_zero : ∀ j, modifiedDiagonal j ≠ 0
  modifiedPairing : ∀ i j, modifiedTest i (modifiedValues j) =
    if i = j then modifiedDiagonal i else 0
  modifiedCoefficients : UpperRationalFibre upperGeometricClass C →
    UpperRationalFibre upperGeometricClass C →₀ K
  modifiedExpansion : ∀ j, modifiedValues j = Finsupp.linearCombination K
    (fun u => fun v : UpperRationalFibre upperGeometricClass C =>
      dualGamma u (upperRepresentative v)) (modifiedCoefficients j)
  dualGamma_class : ∀ (j u : UpperRationalFibre upperGeometricClass C)
    (x : SpecialClifford n F), ConjClasses.mk x = u.val.val →
    dualGamma j x = dualGamma j (upperRepresentative u)
  dualSupport : UpperRationalFibre upperGeometricClass C → Set (SpecialClifford n F)
  dualGamma_support : ∀ j x, x ∉ dualSupport j → dualGamma j x = 0
  pointwiseVanishing : ∀ Phi ∈ family, ∀ j x, x ∈ dualSupport j →
    (∀ u : UpperRationalFibre upperGeometricClass C, ConjClasses.mk x ≠ u.val.val) →
    Phi.val x⁻¹ = 0
  dualityFactor : family → K
  dualityFactor_ne_zero : ∀ Phi, dualityFactor Phi ≠ 0
  alvisCurtisPairing : ∀ (Phi : family) j,
    upperScalarProduct Phi.val.val (dualGamma j) =
      dualityFactor Phi * upperScalarProduct (upperDual Phi.val).val (upperGamma j)

variable (valueSource : IsolatedValueSource (upperDual := upperDual) C upperGamma family)

omit [Finite F] [CharP F r] [CharZero K]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] in
include valueSource in
theorem IsolatedValueSource.value_span :
    Submodule.span K (Set.range (fun Phi : family =>
      fun u : UpperRationalFibre upperGeometricClass C =>
        Phi.val.val (upperRepresentative u)⁻¹)) = ⊤ := by
  apply FiniteCharacterSelection.span_eq_top_of_trace_expansions _
    valueSource.traceValues valueSource.traceCoefficients
  · exact FiniteCharacterSelection.span_eq_top_of_diagonal_pairings
      valueSource.traceValues valueSource.traceTest valueSource.traceDiagonal
      valueSource.traceDiagonal_ne_zero (by
        intro i j
        by_cases h : i = j <;> simpa [h] using valueSource.tracePairing i j)
  · exact valueSource.actualFTraceExpansion

omit [Finite F] [CharP F r] [CharZero K]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] in
theorem IsolatedValueSource.dualRestriction_independent :
    LinearIndependent K (fun u => fun v : UpperRationalFibre upperGeometricClass C =>
      valueSource.dualGamma u (upperRepresentative v)) := by
  apply FiniteCharacterSelection.linearIndependent_of_spanning_independent_family _
    valueSource.modifiedValues
  · exact FiniteCharacterSelection.linearIndependent_of_diagonal_pairings
      valueSource.modifiedValues valueSource.modifiedTest valueSource.modifiedDiagonal
      valueSource.modifiedDiagonal_ne_zero (by
        intro i j
        by_cases h : i = j <;> simpa [h] using valueSource.modifiedPairing i j)
  · intro j
    rw [← Finsupp.range_linearCombination]
    exact ⟨valueSource.modifiedCoefficients j, (valueSource.modifiedExpansion j).symm⟩

/-- The coefficient of the rational class is its literal finite class size divided
by the group order. It is unrelated to the indices of the fixed subgroups in the
weighted Taylor formula. -/
def rationalClassWeight (u : UpperRationalFibre upperGeometricClass C) : K :=
  ((FiniteClassPairing.fibre ConjClasses.mk
    (fun v : UpperRationalFibre upperGeometricClass C => v.val.val) u).card : K) /
      (Fintype.card (SpecialClifford n F) : K)

omit [Finite F] [CharP F r]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] in
theorem rationalClassWeight_ne_zero (u : UpperRationalFibre upperGeometricClass C) :
    rationalClassWeight (K := K) u ≠ 0 :=
  FiniteClassPairing.weight_ne_zero _ _ upperRepresentative upperRepresentative_class u

omit [Finite F] [CharP F r]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] in
theorem IsolatedValueSource.localized_pairing (Phi : family)
    (j : UpperRationalFibre upperGeometricClass C) :
    upperScalarProduct Phi.val.val (valueSource.dualGamma j) =
      FiniteCharacterSelection.weightedPairing rationalClassWeight
        (fun u : UpperRationalFibre upperGeometricClass C =>
          Phi.val.val (upperRepresentative u)⁻¹)
        (fun u => valueSource.dualGamma j (upperRepresentative u)) := by
  have localized := FiniteClassPairing.sum_localize ConjClasses.mk
    (fun u : UpperRationalFibre upperGeometricClass C => u.val.val)
    (fun a b h => Subtype.ext (Subtype.ext h))
    (fun x => Phi.val.val x⁻¹ * valueSource.dualGamma j x)
    (fun u => Phi.val.val (upperRepresentative u)⁻¹ *
      valueSource.dualGamma j (upperRepresentative u))
    (fun u x h => by rw [ordinary_inverse_class Phi.val
        (h.trans (upperRepresentative_class u).symm),
      valueSource.dualGamma_class j u x h])
    (fun x hx => by
      by_cases supported : x ∈ valueSource.dualSupport j
      · rw [valueSource.pointwiseVanishing Phi.val Phi.property j x supported hx, zero_mul]
      · rw [valueSource.dualGamma_support j x supported, mul_zero])
  unfold upperScalarProduct
  rw [localized, Finset.mul_sum]
  unfold FiniteCharacterSelection.weightedPairing rationalClassWeight
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.card_eq_nat_card]
  simp only [div_eq_mul_inv]
  ring

include valueSource in
/-- The contradiction from a zero column follows from the source
identities on these actual characters and functions. -/
theorem IsolatedValueSource.coverage :
    ∀ u, ∃ Phi ∈ family,
      upperScalarProduct (upperDual Phi).val (upperGamma u) ≠ 0 := by
  have covered := FiniteCharacterSelection.coverage_of_span
    (fun Phi : family => fun u => Phi.val.val (upperRepresentative u)⁻¹)
    (fun j => fun u => valueSource.dualGamma j (upperRepresentative u))
    rationalClassWeight
    (fun Phi : family => fun u => upperScalarProduct (upperDual Phi.val).val (upperGamma u))
    valueSource.dualityFactor valueSource.value_span rationalClassWeight_ne_zero
    (fun j => valueSource.dualRestriction_independent.ne_zero j)
    (fun Phi j => (valueSource.localized_pairing Phi j).symm.trans
      (valueSource.alvisCurtisPairing Phi j))
  intro u
  obtain ⟨Phi, nonzero⟩ := covered u
  exact ⟨Phi.val, Phi.property, nonzero⟩

/-- The specified component group and quotient, and the uniform constituent
support and series before duality, are fixed throughout. The upper family
uses the source assumptions specified above. Geck–Malle 2020 Theorem 1.7.15
supplies multiplicity freeness of restriction. Geck–Malle 2000 Theorem 3.7
supplies constancy of support within each upper family. Compatibility
with duality and Taylor 2016 Lemmas 14.12 and 14.15 supply preservation
of support under restriction. -/
structure NonabelianSource (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
    (C : GeometricClass) where
  UpperComponent : Type
  upperComponentGroup : CommGroup UpperComponent
  presentation : letI := upperComponentGroup;
    ComponentPresentation (ComponentGroup C) UpperComponent
  parameter : letI := upperComponentGroup;
    CompatibleComponentParametrisation geometricClass upperGeometricClass geometric_square
      parameters rank C (ComponentGroup C) UpperComponent presentation
  upperGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K
  family : Set (Irr K (SpecialClifford n F))
  distinguished : Irr K (SpecialClifford n F)
  distinguished_mem : distinguished ∈ family
  distinguished_two : Fintype.card (Constituent (N := N) distinguished) = 2
  current : letI := upperComponentGroup;
    FamilySource (geometricClass := geometricClass)
    (geometric_square := geometric_square) (gamma := gamma)
    (upperDual := upperDual) (lowerDual := lowerDual) UpperComponent
    parameters C upperGamma {distinguished}
  isolatedFamily : Set (Irr K (SpecialClifford n F))
  isolatedCurrent : letI := upperComponentGroup;
    FamilySource (geometricClass := geometricClass)
    (geometric_square := geometric_square) (gamma := gamma)
    (upperDual := upperDual) (lowerDual := lowerDual) UpperComponent
    parameters C upperGamma isolatedFamily
  isolatedValues : IsolatedValueSource (upperDual := upperDual) C upperGamma isolatedFamily
  label : TypeBConformalDualCarriers.PCSp F n
  label_quasiIsolated : quasiIsolated label
  restriction_series : ∀ Phi ∈ family, ∀ rho : Irr K (Spin n F N),
    occurs N Phi rho → rationalSeries label rho
  restriction_support : ∀ Phi ∈ family, ∀ rho : Irr K (Spin n F N),
    occurs N Phi rho → unipotentSupport rho C
  isolatedLabel : TypeBConformalDualCarriers.PCSp F n
  isolatedLabel_quasiIsolated : quasiIsolated isolatedLabel
  isolated_restriction_series : ∀ Phi ∈ isolatedFamily, ∀ rho : Irr K (Spin n F N),
    occurs N Phi rho → rationalSeries isolatedLabel rho
  isolated_restriction_support : ∀ Phi ∈ isolatedFamily, ∀ rho : Irr K (Spin n F N),
    occurs N Phi rho → unipotentSupport rho C

omit [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] in
/-- For every conjugacy class in the special Clifford group within the
chosen geometric class, its GGGR has nonzero scalar product with the
dual of some character in the isolated family. This is the finite coverage
deduction in manuscript Lemma 2.11, proved from IsolatedValueSource.
GGGRSelection.workingSource uses it in the nonabelian case of
Proposition 4.9. -/
theorem NonabelianSource.isolatedCoverage
    (source : NonabelianSource (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
      parameters higher C) :
    ∀ u, ∃ Phi ∈ source.isolatedFamily,
      upperScalarProduct (upperDual Phi).val (source.upperGamma u) ≠ 0 :=
  source.isolatedValues.coverage

/-- The union `{source.distinguished} ∪ source.isolatedFamily` is used only by
the restriction and finite matrix arguments. It contains the original distinguished
character and the selected isolated family, and is not asserted to lie in one
rational series. -/
theorem NonabelianSource.unionSource
    (source : NonabelianSource (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
      parameters higher C) :
    TaylorFamilySource geometricClass upperGeometricClass geometric_square C
      parameters higher gamma source.upperGamma ({source.distinguished} ∪ source.isolatedFamily)
      upperDual lowerDual := by
  let := source.upperComponentGroup
  refine {
    restriction := ?_
    upperNonnegative := ?_
    upperSumOne := ?_
    coverage := ?_
    distinguished := ⟨source.distinguished, Or.inl rfl,
      source.distinguished_two⟩
    gggrInduction := source.current.gggrInduction
    gggrConjugation := source.current.gggrConjugation }
  · exact {
      nonempty := fun Phi h => h.elim
        (source.current.restriction.nonempty Phi)
        (source.isolatedCurrent.restriction.nonempty Phi)
      cliffordTransitive := fun Phi h => h.elim
        (source.current.restriction.cliffordTransitive Phi)
        (source.isolatedCurrent.restriction.cliffordTransitive Phi)
      dualityRestriction := fun Phi h => h.elim
        (source.current.restriction.dualityRestriction Phi)
        (source.isolatedCurrent.restriction.dualityRestriction Phi)
      dualityConjugation := fun Phi h => h.elim
        (source.current.restriction.dualityConjugation Phi)
        (source.isolatedCurrent.restriction.dualityConjugation Phi) }
  · intro Phi h
    exact h.elim (source.current.upperNonnegative Phi)
      (source.isolatedCurrent.upperNonnegative Phi)
  · intro Phi h
    exact h.elim (source.current.upperSumOne Phi)
      (source.isolatedCurrent.upperSumOne Phi)
  · intro u
    obtain ⟨Phi, hPhi, hnonzero⟩ := source.isolatedCoverage u
    exact ⟨Phi, Or.inr hPhi, hnonzero⟩


/-- The alternative with trivial image of the centre. The class map is
injective by the geometric component parametrisation input. Coverage is
proved from the selected isolated family `family`, using its trace data
and dual functions. -/
structure AbelianSingletonData (C : GeometricClass)
    (centerImage : Subgroup (ComponentGroup C))
    (upperGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K)
    (family : Set (Irr K (SpecialClifford n F))) where
  centerImage_trivial : centerImage = ⊥
  classMap_injective : Function.Injective
    (rationalClassMap geometricClass upperGeometricClass geometric_square C)
  isolatedValues : IsolatedValueSource (upperDual := upperDual) C upperGamma family

/-- The nontrivial image of the centre in the abelian case has order two and is the whole
component group. These are component geometry and Taylor's distinguished
character inputs. The lower scalar product identities are derived. -/
structure AbelianDoubleData (C : GeometricClass)
    (centerImage : Subgroup (ComponentGroup C))
    (family : Set (Irr K (SpecialClifford n F))) where
  centerImage_full : centerImage = ⊤
  component_order_two : Nat.card (ComponentGroup C) = 2
  upperClass_unique : Subsingleton (UpperRationalFibre upperGeometricClass C)
  lowerClasses : Fin 2 ≃ RationalFibre geometricClass C
  distinguished : Irr K (SpecialClifford n F)
  family_singleton : family = {distinguished}
  distinguished_two : Fintype.card (Constituent (N := N) distinguished) = 2

/-- The abelian component case separates the two possible images of the centre.
When the image is trivial, `family` is the selected isolated family.
When the image is nontrivial, `family` consists of the original distinguished
Taylor character. -/
structure AbelianSource (parameters : OddFieldParameters F r f) (C : GeometricClass) where
  component_abelian : ∀ x y : ComponentGroup C, x * y = y * x
  centerImage : Subgroup (ComponentGroup C)
  UpperComponent : Type
  upperComponentGroup : CommGroup UpperComponent
  /-- The actual upper component quotient, still requiring its algebraic
  interpretation. Its order is the one used in the weighted formula. -/
  componentMap : letI := upperComponentGroup; ComponentGroup C →* UpperComponent
  componentMap_surjective : Function.Surjective componentMap
  componentMap_ker : letI := upperComponentGroup; componentMap.ker = centerImage
  upperGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K
  family : Set (Irr K (SpecialClifford n F))
  current : letI := upperComponentGroup;
    FamilySource (geometricClass := geometricClass)
      (geometric_square := geometric_square) (gamma := gamma)
      (upperDual := upperDual) (lowerDual := lowerDual) UpperComponent
      parameters C upperGamma family
  alternative : Sum
    (AbelianSingletonData (geometricClass := geometricClass)
      (geometric_square := geometric_square) (upperDual := upperDual)
      C centerImage upperGamma family)
    (AbelianDoubleData (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (N := N) C centerImage family)
  label : TypeBConformalDualCarriers.PCSp F n
  label_quasiIsolated : quasiIsolated label
  restriction_series : ∀ Phi ∈ family, ∀ rho : Irr K (Spin n F N),
    occurs N Phi rho → rationalSeries label rho
  restriction_support : ∀ Phi ∈ family, ∀ rho : Irr K (Spin n F N),
    occurs N Phi rho → unipotentSupport rho C

/-- The abelian and nonabelian component alternatives use their explicit
upper sources. Neither contains a selected lower identity matrix. -/
abbrev LocalSources (C : GeometricClass) :=
  Sum
    (AbelianSource (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual)
      (rationalSeries := rationalSeries) (quasiIsolated := quasiIsolated)
      (unipotentSupport := unipotentSupport) parameters C)
    (NonabelianSource (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
      parameters higher C)

end Local

variable {parameters : OddFieldParameters F r f}
  {O k : Type} [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] {rank : 3 ≤ n}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
  {b : LiteralPrimitiveBlock k (Spin n F N)}
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]

structure HigherSources (D : GGGRContext parameters rank Msys iota b) (higher : 4 ≤ n) where
  upperGeometricClass : UpperUnipotentClass (n := n) (F := F) (r := r) → D.GeometricClass
  geometric_square : ∀ c, upperGeometricClass (upperClassMap c) = D.geometricClass c
  upperDual : Irr K (SpecialClifford n F) → Irr K (SpecialClifford n F)
  waveFront : TypeBAllRankGGGR.BasisPhysical.WaveFrontClosureCertificate parameters higher
    D.geometricClass D.gamma D.lowerDual D.unipotentSupport D.closure
  count : TypeBAllRankGGGR.BasisPhysical.PrincipalRationalClassCount parameters higher
    iota b D.principal
  reciprocity : FrobeniusReciprocitySource (N := N) (K := K)
  sources : ∀ C, Nonempty (RationalFibre D.geometricClass C) →
    LocalSources (geometricClass := D.geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := D.ComponentGroup) (gamma := D.gamma) (upperDual := upperDual)
      (lowerDual := D.lowerDual) (rationalSeries := D.rationalSeries)
      (quasiIsolated := D.quasiIsolated) (unipotentSupport := D.unipotentSupport)
      (parameters := parameters) (higher := higher) C

/-- Rank three uses the same construction from the image of the centre. The
retained source with identity rows is built only after that construction. -/
structure RankThreeSources
    {N : NormSource 3 F} [Finite (SpecialClifford 3 F)] [Finite (Spin 3 F N)]
    [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford 3 F))]
    [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
    [Finite (Irr K (Spin 3 F N))]
    {iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N)}
    {b : LiteralPrimitiveBlock k (Spin 3 F N)}
    [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
    (D : GGGRContext parameters (show 3 ≤ 3 from le_rfl) Msys iota b) where
  upperGeometricClass : UpperUnipotentClass (n := 3) (F := F) (r := r) → D.GeometricClass
  geometric_square : ∀ c, upperGeometricClass (upperClassMap c) = D.geometricClass c
  upperDual : Irr K (SpecialClifford 3 F) → Irr K (SpecialClifford 3 F)
  reciprocity : FrobeniusReciprocitySource (N := N) (K := K)
  sources : ∀ C, Nonempty (RationalFibre D.geometricClass C) →
    AbelianSource (geometricClass := D.geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := D.ComponentGroup) (gamma := D.gamma) (upperDual := upperDual)
      (lowerDual := D.lowerDual) (rationalSeries := D.rationalSeries)
      (quasiIsolated := D.quasiIsolated) (unipotentSupport := D.unipotentSupport) parameters C
  waveFront : TypeBSpinPrincipalGGGRBasisBinding.WaveFrontClosureCertificate parameters
    D.geometricClass D.gamma D.lowerDual D.unipotentSupport D.closure
  count : TypeBSpinPrincipalGGGRBasisBinding.PrincipalRationalClassCount parameters
    iota b D.principal

/-- Both rank ranges use upper source data and proved local selection. -/
structure RankSources (D : GGGRContext parameters rank Msys iota b) where
  rankThree : ∀ h : n = 3, by subst n; exact RankThreeSources D
  higher : ∀ h : 4 ≤ n, HigherSources D h

end ManuscriptIBAW.TypeB.GGGRSources

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
