import ManuscriptIBAW.Sporadic.NumericalWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4

/-!
# The Janko group J4

The manuscript uses the trivial Schur multiplier and outer automorphism
group from the Atlas, An, O'Brien and Wilson's Theorem 5.2 for noncyclic
defect groups, and Späth's Proposition 6.2 for cyclic defect groups.
The latter case includes defect zero.

The three numerical assumptions below concern the actual defect groups
and the Brauer and weight fibres of the specified block decomposition.
The full condition additionally requires root agreement for the constructed
extension and block witnesses. The interpretation of the selected finite
group as J4 remains external.
-/

noncomputable section

namespace ManuscriptIBAW.Sporadic.J4

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs
open CyclicOuterLemma37LiteralLocalExtension EvenFieldFLZSourceConditions
open EvenFieldFLZ318FixedTheoremGate SporadicCompleteCollapseLemma52Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierJ4Numerical
open SporadicFi24P3Definition44NamedCarrierJ4FullCover
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open SporadicFi24P3Definition44NamedCarrierSelfCover

universe u

local instance j4BrauerFintype {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X] (iota : PrimeRegularRootEmbedding p k K X) :
    Fintype (IBr iota) := Fintype.ofFinite _

/-- Published numerical assertions and existence of a defect group for
each primitive block. No equivariant matching is assumed. -/
structure NumericalSources {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X)) : Prop where
  defect_exists : ∀ b : ActualBlock (k := k) (X := X),
    ∃ D : Subgroup X, actualHasDefect iota R b D
  spath_cyclic : ∀ (b : ActualBlock (k := k) (X := X)) (D : Subgroup X),
    actualHasDefect iota R b D → IsCyclic D → blockCardEq iota hinj R b
  an_obrien_wilson_noncyclic : ∀ (b : ActualBlock (k := k) (X := X)) (D : Subgroup X),
    actualHasDefect iota R b D → ¬ IsCyclic D → blockCardEq iota hinj R b

theorem NumericalSources.defectCounts {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    {iota : PrimeRegularRootEmbedding p k K X}
    {hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota}
    {R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X)}
    (source : NumericalSources iota hinj R) :
    CyclicNoncyclicNumericalSource iota hinj R where
  existsDefect := source.defect_exists
  cyclicCardEq := source.spath_cyclic
  noncyclicCardEq := source.an_obrien_wilson_noncyclic

/-- The numerical equality for every block follows by the defect group case
distinction used in the manuscript. -/
theorem NumericalSources.all_blocks {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    {iota : PrimeRegularRootEmbedding p k K X}
    {hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota}
    {R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X)}
    (source : NumericalSources iota hinj R) (b : ActualBlock (k := k) (X := X)) :
    blockCardEq iota hinj R b := by
  obtain ⟨D, defect⟩ := source.defect_exists b
  by_cases cyclic : IsCyclic D
  · exact source.spath_cyclic b D defect cyclic
  · exact source.an_obrien_wilson_noncyclic b D defect cyclic

/-- Structural and published assumptions for one relevant prime on the same
specified J4 group. The ordinary coefficient field has characteristic zero.
Neither algebraic closure nor a modular system is required. -/
inductive SourceInputs (base : NamedBase.{u}) (p : ℕ) : Type (u + 1) where
  | mk
    {k K U X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group U] [Group X] [Fintype X]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (reductions : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (cover : U →* X) (universal : IsUniversalCentralExtension cover)
    (multiplier_trivial : Nat.card cover.ker = 1)
    (simple : IsSimpleGroup X) (nonabelian : ¬ IsMulCommutative X)
    (outer_trivial : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (defectZero : DefectZeroReductionSource iota)
    (trivialWeights : TrivialWeightSource (p := p) (X := X))
    (numerical : NumericalSources iota hinj R)
    (localBlocks : CanonicalLocalBlockCompatibility iota R.1.operations)
    (coefficients : SpathCoefficientField p k iota.prime)
    (identification : (identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover universal multiplier_trivial simple nonabelian).S ≃* base.S) :
    SourceInputs base p

/-- The proof of the complete condition receives only the subordinate
assumptions. Its numerical source is constructed from the cited cases. -/
def SourceInputs.retained {base : NamedBase.{u}} {p : ℕ} (source : SourceInputs base p) :
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4.Inputs base p := by
  cases source with
  | mk iota hinj R reductions cover universal multiplier_trivial simple nonabelian
      outer_trivial defectZero trivialWeights numerical localBlocks coefficients identification =>
    exact .mk iota hinj R reductions cover universal multiplier_trivial simple nonabelian
      outer_trivial defectZero trivialWeights numerical.defectCounts localBlocks coefficients
      identification

def SourceInputs.model {base : NamedBase.{u}} {p : ℕ} (source : SourceInputs base p) :
    CaseModel base p :=
  SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4.model source.retained

/-- Root agreement for the explicit witnesses constructed from the numerical counts. -/
def SourceInputs.RootAgreement {base : NamedBase.{u}} {p : ℕ}
    (source : SourceInputs base p) : Prop := by
  cases source with
  | mk iota hinj R reductions cover universal multiplier_trivial simple nonabelian
      outer_trivial defectZero trivialWeights numerical localBlocks coefficients identification =>
    let selectedCover := identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover universal multiplier_trivial simple nonabelian
    let W := CanonicalNumericalWitness.witnessOfNumerical iota hinj R reductions selectedCover
      (center_eq_bot_of_nonabelian_simple simple nonabelian)
      (allAutomorphismsInner_of_outer_card_one outer_trivial) defectZero trivialWeights
      (numericalBlockwiseAWC iota hinj R numerical.defectCounts) localBlocks coefficients
    exact CanonicalWitnessRoots iota R selectedCover reductions defectZero trivialWeights W

/-- The numerical sources and compatibility of the constructed root correspondences. -/
structure Inputs (base : NamedBase.{u}) (p : ℕ) where
  source : SourceInputs base p
  roots : source.RootAgreement

def Inputs.model {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) : CaseModel base p :=
  I.source.model

/-- The full condition for the same matching, with compatible root correspondences. -/
theorem Inputs.complete {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) :
    CaseConclusion I.model := by
  rcases I with ⟨source, roots⟩
  cases source with
  | mk iota hinj R reductions cover universal multiplier_trivial simple nonabelian
      outer_trivial defectZero trivialWeights numerical localBlocks coefficients identification =>
    let selectedCover := identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover universal multiplier_trivial simple nonabelian
    let W := CanonicalNumericalWitness.witnessOfNumerical iota hinj R reductions selectedCover
      (center_eq_bot_of_nonabelian_simple simple nonabelian)
      (allAutomorphismsInner_of_outer_card_one outer_trivial) defectZero trivialWeights
      (numericalBlockwiseAWC iota hinj R numerical.defectCounts) localBlocks coefficients
    change Definition41Certificate iota R selectedCover
    exact of_canonical iota R selectedCover reductions defectZero trivialWeights
      (center_eq_bot_of_nonabelian_simple simple nonabelian) W roots

end ManuscriptIBAW.Sporadic.J4

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
