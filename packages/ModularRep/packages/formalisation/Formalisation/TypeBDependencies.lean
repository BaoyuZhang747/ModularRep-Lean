import Formalisation.DependencyGraph
import Formalisation.DependencyCases
import Formalisation.PairedLeviOrbit

/-!
# Dependency certificate for the type B section

This module records the dependency audit of every named result in the manuscript's type `B`
section.  Literature results, finite computations, and representation theoretic bridges that
are not formalised in Mathlib are explicit leaves.  The seventeen named manuscript results and
the rank-indexed induction step used in the high-rank proof are derived nodes.  Every edge
strictly lowers `rank`, so the graph is acyclic by construction.

The graph is deliberately granular.  In particular, the high-rank proposition does not have a
leaf asserting Assumption 5.3 at the current rank, that all blocks are BAW-good, or any form of
the type `B` headline.  Its dependencies instead expose the principal selector, the lower-rank
bases, the component-return and Clifford arguments, and the cited Jordan and Levi bridges.
The repaired proof-body order is `R,G,P,T,Q,B,L,H`.  Among those named
results, `B` uses `T,Q`, `L` uses `P,Q`, and `H` uses `P,T,Q,L`.  The
rank-three proposition does not use the localized-return lemma, and the
high-rank proposition does not use the all-block rank-three proposition.

The final theorems are conditional certificates.  The headline theorem assumes only the
external leaves in the ancestor closure of the type `B` theorem.  The census theorem additionally
assumes its four census-only inputs.  The separate ranked-induction theorem exposes the
strictly-lower-rank hypothesis used at each step.  These theorems do not assert the truth of the
cited results, GAP transcripts, or unformalised representation theory.
-/

namespace Formalisation.TypeBDependencies

open DependencyGraph

-- Kernel reduction of the explicit 90-node audit lists needs more than the project's
-- deliberately small default recursion limit.
set_option maxRecDepth 10000

/-- External inputs, the seventeen named results in the current type `B` section, and the
explicit high-rank induction step. -/
inductive Node where
  -- Covering groups, automorphisms, and the defining-prime branch.
  | coverTable
  | outerAutomorphismDescription
  | definingCharacteristicTheorem
  -- Odd nondefining primes and the Conlon argument.
  | integralBasicSet
  | specialCliffordBlockParameters
  | specialCliffordTensorAction
  | conlonPermutationLatticeDetection
  | ordinaryWeightBijection
  | ordinaryStabilizerSeparation
  | weightStabilizerFactorization
  | oddPrimeInductiveCriterion
  | cyclicDefectIBAW
  -- Product characters and the component-return argument.
  | brauerCharactersOfDirectProducts
  | componentPermutationCompatibility
  | productOrbitCharacterization
  -- Regular embeddings of Levi subgroups.
  | connectedLeviCentre
  | regularEmbeddingCoinvariantProductAction
  | ambientRegularEmbeddingExponentTwo
  -- Characteristic-two Clifford theory.
  | modularCliffordCorrespondence
  | cliffordTwistByLinearBrauerCharacter
  | brauerLinearCharacterGroupOdd
  | cliffordInductionCompatibility
  -- Passage across a normal core.
  | normalCorePrincipalRestriction
  | radicalWeightQuotientEquivalence
  | modularTripleInflation
  -- Jordan reduction and factor packages.
  | strictQuasiIsolatedClassification
  | principalWeightAndCriterionPackage
  | typeAFactorPackage
  | solvableFactorPackage
  | typeC2FactorPackage
  | leviFactorDecomposition
  | productAndWreathAssembly
  | butterflyJordanPackage
  /-- E2/U source adapter: Feng--Li--Zhang, Section 5 and the first paragraph
  of the proof of Theorem 5.7, select the minimal proper `F`-stable Levi
  containing `C°(s)C(s)^F`; matching that source object is unformalised. -/
  | properRationalLeviReduction
  | pairedLeviAndOuterControl
  | multiplicityFreeCliffordExtension
  | equivariantJordanBijection
  | bdrExtensionTransfer
  | lusztigIdempotentOuterControl
  -- Unipotent classes and generalised Gelfand--Graev characters.
  | componentFrobeniusIsInner
  | rationalClassTwistedParametrization
  | gggrEquivariance
  | chanebAbelianPairing
  | extraspecialComponentFibres
  | geckHezardPairing
  | regularEmbeddingRestriction
  | dualityAndGGGRCompatibility
  | specialTwoConstituentCharacter
  | principalBlockLabelCriterion
  | waveFrontTriangularity
  | rationalUnipotentCount
  | projectiveBrauerDuality
  -- Preliminary results outside the type B section.
  | cyclicBrauerExtension
  | blockAggregation
  | fixedPointDescent
  | typeCOddTwoFactor
  | bawGoodImpliesInductiveBAW
  -- The five independent computations for the exceptional triple cover.
  | q3PrincipalWeightComputation
  | q3PrincipalBrauerComputation
  | q3BlockCensusComputation
  | q3BlockTwoComputation
  | q3RadicalSectorComputation
  -- Cited completion inputs for the exceptional triple cover.
  | q3PrincipalWeightTotalAndCovering
  | principalCentralCoverLift
  | heightZeroCriterion
  | quaternionBlockClassification
  | d8WeightPackage
  | innerStabilizerIBAWCompletion
  -- Inputs used only by the final all-type-B census.
  | evenCharacteristicTypeBTypeC
  | typeCHeadline
  | lowRankAIBAW
  | alternatingIBAW
  -- The seventeen named results in the type B section and its explicit induction step.
  | propDefiningPrime
  | lemConlonBlock
  | propOddNondefining
  | lemComponentReturn
  | lemRegularLeviOrbits
  | lemCharacteristicTwoClifford
  | lemNormalCore
  | lemRationalField
  | propGGGRRank
  | corPrincipalSelector
  | lemRankThreePrincipal
  | propExceptionalQ3
  | propTwoRankThree
  | lemLocalizedReturn
  | highRankInductionStep
  | propTwoHighRank
  | thmTypeB
  | corTypeBCensus
  deriving DecidableEq, Repr

/-- Provenance classification.  The computational leaves correspond one-for-one to the five
GAP transcripts in the type `B` appendix. -/
def kind : Node → NodeKind
  | .q3PrincipalWeightComputation
  | .q3PrincipalBrauerComputation
  | .q3BlockCensusComputation
  | .q3BlockTwoComputation
  | .q3RadicalSectorComputation => .computation
  | .brauerCharactersOfDirectProducts
  | .componentPermutationCompatibility
  | .productOrbitCharacterization
  | .modularCliffordCorrespondence
  | .cliffordTwistByLinearBrauerCharacter
  | .brauerLinearCharacterGroupOdd
  | .cliffordInductionCompatibility
  | .radicalWeightQuotientEquivalence
  | .projectiveBrauerDuality
  | .blockAggregation
  | .fixedPointDescent
  | .typeCOddTwoFactor
  | .properRationalLeviReduction
  | .bawGoodImpliesInductiveBAW
  | .evenCharacteristicTypeBTypeC
  | .typeCHeadline => .semanticBridge
  | .propDefiningPrime
  | .lemConlonBlock
  | .propOddNondefining
  | .lemComponentReturn
  | .lemRegularLeviOrbits
  | .lemCharacteristicTwoClifford
  | .lemNormalCore
  | .lemRationalField
  | .propGGGRRank
  | .corPrincipalSelector
  | .lemRankThreePrincipal
  | .propExceptionalQ3
  | .propTwoRankThree
  | .lemLocalizedReturn
  | .highRankInductionStep
  | .propTwoHighRank
  | .thmTypeB
  | .corTypeBCensus => .derived
  | _ => .cited

/-- The proper rational Levi reduction is recorded at its exact E2/U boundary:
the cited selection theorem and its concrete algebraic group identification
remain an external semantic bridge. -/
@[simp] theorem properRationalLeviReduction_kind :
    kind .properRationalLeviReduction = .semanticBridge := rfl

/-- The inputs used directly in one step of the strong induction proving the high-rank
proposition.  In particular, the internal principal selector and the previously proved
lower-rank conclusions are not hidden inside an unindexed headline node. -/
def highRankStepInputs : List Node :=
  [.coverTable, .outerAutomorphismDescription, .corPrincipalSelector,
   .lemLocalizedReturn, .lemComponentReturn, .lemRegularLeviOrbits,
   .lemCharacteristicTwoClifford,
   .lemNormalCore, .lemRankThreePrincipal, .propExceptionalQ3,
   .properRationalLeviReduction, .pairedLeviAndOuterControl,
   .strictQuasiIsolatedClassification, .principalBlockLabelCriterion,
   .typeAFactorPackage,
   .solvableFactorPackage, .typeC2FactorPackage, .typeCOddTwoFactor,
   .leviFactorDecomposition, .blockAggregation, .fixedPointDescent,
   .productAndWreathAssembly, .multiplicityFreeCliffordExtension,
   .cyclicBrauerExtension, .equivariantJordanBijection, .bdrExtensionTransfer,
   .lusztigIdempotentOuterControl, .bawGoodImpliesInductiveBAW]

/-- Immediate dependencies from the theorem-by-theorem audit. -/
def dependencies : Node → List Node
  | .propDefiningPrime =>
      [.coverTable, .definingCharacteristicTheorem]
  | .lemConlonBlock =>
      [.outerAutomorphismDescription, .integralBasicSet,
       .specialCliffordBlockParameters, .specialCliffordTensorAction,
       .conlonPermutationLatticeDetection]
  | .propOddNondefining =>
      [.coverTable, .outerAutomorphismDescription, .lemConlonBlock,
       .ordinaryWeightBijection, .ordinaryStabilizerSeparation,
       .weightStabilizerFactorization, .oddPrimeInductiveCriterion,
       .cyclicDefectIBAW]
  | .lemComponentReturn =>
      [.brauerCharactersOfDirectProducts, .componentPermutationCompatibility,
       .productOrbitCharacterization]
  | .lemRegularLeviOrbits =>
      [.leviFactorDecomposition, .connectedLeviCentre,
       .regularEmbeddingCoinvariantProductAction,
       .productOrbitCharacterization, .ambientRegularEmbeddingExponentTwo]
  | .lemCharacteristicTwoClifford =>
      [.modularCliffordCorrespondence, .cliffordTwistByLinearBrauerCharacter,
       .brauerLinearCharacterGroupOdd, .cliffordInductionCompatibility]
  | .lemNormalCore =>
      [.normalCorePrincipalRestriction, .radicalWeightQuotientEquivalence,
       .modularTripleInflation]
  | .lemRationalField =>
      [.componentFrobeniusIsInner, .rationalClassTwistedParametrization,
       .gggrEquivariance]
  | .propGGGRRank =>
      [.chanebAbelianPairing, .extraspecialComponentFibres, .geckHezardPairing,
       .regularEmbeddingRestriction, .dualityAndGGGRCompatibility,
       .specialTwoConstituentCharacter, .principalBlockLabelCriterion,
       .waveFrontTriangularity, .rationalUnipotentCount]
  | .corPrincipalSelector =>
      [.lemRationalField, .propGGGRRank, .projectiveBrauerDuality,
       .cyclicBrauerExtension, .principalWeightAndCriterionPackage]
  | .lemRankThreePrincipal =>
      [.coverTable, .corPrincipalSelector, .bawGoodImpliesInductiveBAW]
  | .propExceptionalQ3 =>
      [.coverTable, .q3PrincipalWeightComputation, .q3PrincipalBrauerComputation,
       .q3BlockCensusComputation, .q3BlockTwoComputation,
       .q3RadicalSectorComputation, .q3PrincipalWeightTotalAndCovering,
       .principalCentralCoverLift, .heightZeroCriterion,
       .quaternionBlockClassification, .d8WeightPackage, .cyclicDefectIBAW,
       .innerStabilizerIBAWCompletion]
  | .propTwoRankThree =>
      [.coverTable, .propExceptionalQ3, .lemRankThreePrincipal,
        .lemComponentReturn, .lemRegularLeviOrbits,
        .lemCharacteristicTwoClifford,
        .properRationalLeviReduction, .pairedLeviAndOuterControl,
        .strictQuasiIsolatedClassification, .principalBlockLabelCriterion,
        .typeAFactorPackage, .typeC2FactorPackage, .typeCOddTwoFactor,
        .productAndWreathAssembly,
        .multiplicityFreeCliffordExtension, .cyclicBrauerExtension,
        .equivariantJordanBijection, .bdrExtensionTransfer,
        .lusztigIdempotentOuterControl, .butterflyJordanPackage,
        .bawGoodImpliesInductiveBAW]
  | .lemLocalizedReturn =>
      [.lemNormalCore, .corPrincipalSelector, .propExceptionalQ3,
       .blockAggregation, .fixedPointDescent, .strictQuasiIsolatedClassification,
        .principalWeightAndCriterionPackage, .typeAFactorPackage,
        .solvableFactorPackage, .typeC2FactorPackage, .typeCOddTwoFactor,
        .leviFactorDecomposition, .productAndWreathAssembly,
        .butterflyJordanPackage, .cyclicBrauerExtension]
  | .highRankInductionStep => highRankStepInputs
  | .propTwoHighRank =>
      .highRankInductionStep :: highRankStepInputs
  | .thmTypeB =>
      [.coverTable, .propDefiningPrime, .propOddNondefining,
       .propTwoRankThree, .propTwoHighRank, .blockAggregation]
  | .corTypeBCensus =>
      [.thmTypeB, .evenCharacteristicTypeBTypeC, .typeCHeadline,
       .lowRankAIBAW, .alternatingIBAW]
  | _ => []

/-- Ranks used only to certify acyclicity.  External inputs have rank zero. -/
def rank : Node → ℕ
  | .propDefiningPrime
  | .lemConlonBlock
  | .lemComponentReturn
  | .lemRegularLeviOrbits
  | .lemCharacteristicTwoClifford
  | .lemNormalCore
  | .lemRationalField => 1
  | .propOddNondefining
  | .propGGGRRank => 2
  | .corPrincipalSelector => 3
  | .lemRankThreePrincipal => 4
  | .propExceptionalQ3 => 5
  | .propTwoRankThree => 6
  | .lemLocalizedReturn => 7
  | .highRankInductionStep => 8
  | .propTwoHighRank => 9
  | .thmTypeB => 10
  | .corTypeBCensus => 11
  | _ => 0

/-- Regression guard for the order of the eight named results in the repaired
proof body: `R,G,P,T,Q,B,L,H`. -/
theorem proof_body_rank_order :
    rank .lemRationalField < rank .propGGGRRank ∧
    rank .propGGGRRank < rank .corPrincipalSelector ∧
    rank .corPrincipalSelector < rank .lemRankThreePrincipal ∧
    rank .lemRankThreePrincipal < rank .propExceptionalQ3 ∧
    rank .propExceptionalQ3 < rank .propTwoRankThree ∧
    rank .propTwoRankThree < rank .lemLocalizedReturn ∧
    rank .lemLocalizedReturn < rank .propTwoHighRank := by
  decide

/-- The explicit list of external leaves in the ancestor closure of `thmTypeB`. -/
def externalLeafList : List Node :=
  [Node.coverTable, .outerAutomorphismDescription, .definingCharacteristicTheorem,
   .integralBasicSet, .specialCliffordBlockParameters, .specialCliffordTensorAction,
   .conlonPermutationLatticeDetection, .ordinaryWeightBijection,
   .ordinaryStabilizerSeparation, .weightStabilizerFactorization,
   .oddPrimeInductiveCriterion, .cyclicDefectIBAW, .brauerCharactersOfDirectProducts,
   .componentPermutationCompatibility, .productOrbitCharacterization,
   .connectedLeviCentre, .regularEmbeddingCoinvariantProductAction,
   .ambientRegularEmbeddingExponentTwo,
   .modularCliffordCorrespondence, .cliffordTwistByLinearBrauerCharacter,
   .brauerLinearCharacterGroupOdd, .cliffordInductionCompatibility,
   .normalCorePrincipalRestriction, .radicalWeightQuotientEquivalence,
    .modularTripleInflation, .strictQuasiIsolatedClassification,
    .principalWeightAndCriterionPackage, .typeAFactorPackage, .solvableFactorPackage,
   .typeC2FactorPackage, .leviFactorDecomposition, .productAndWreathAssembly,
   .butterflyJordanPackage, .properRationalLeviReduction,
   .pairedLeviAndOuterControl, .multiplicityFreeCliffordExtension,
   .equivariantJordanBijection, .bdrExtensionTransfer, .lusztigIdempotentOuterControl,
   .componentFrobeniusIsInner, .rationalClassTwistedParametrization, .gggrEquivariance,
   .chanebAbelianPairing, .extraspecialComponentFibres, .geckHezardPairing,
   .regularEmbeddingRestriction, .dualityAndGGGRCompatibility,
   .specialTwoConstituentCharacter, .principalBlockLabelCriterion,
   .waveFrontTriangularity, .rationalUnipotentCount, .projectiveBrauerDuality,
   .cyclicBrauerExtension, .blockAggregation, .fixedPointDescent, .typeCOddTwoFactor,
   .bawGoodImpliesInductiveBAW, .q3PrincipalWeightComputation,
   .q3PrincipalBrauerComputation, .q3BlockCensusComputation, .q3BlockTwoComputation,
   .q3RadicalSectorComputation, .q3PrincipalWeightTotalAndCovering,
   .principalCentralCoverLift, .heightZeroCriterion, .quaternionBlockClassification,
   .d8WeightPackage, .innerStabilizerIBAWCompletion]

/-- External leaves in the ancestor closure of `thmTypeB`.  The four inputs used only by the
subsequent census corollary are intentionally absent. -/
def externalLeaves : Finset Node := externalLeafList.toFinset

/-- The four external inputs that enter only the all-type-`B` census. -/
def censusOnlyExternalLeafList : List Node :=
  [Node.evenCharacteristicTypeBTypeC, .typeCHeadline, .lowRankAIBAW, .alternatingIBAW]

def censusOnlyExternalLeaves : Finset Node := censusOnlyExternalLeafList.toFinset

/-- All external leaves needed after continuing through the census corollary. -/
def allExternalLeaves : Finset Node :=
  externalLeaves ∪ censusOnlyExternalLeaves

/-- The seventeen named manuscript results and the explicit high-rank induction step. -/
def namedResultList : List Node :=
  [Node.propDefiningPrime, .lemConlonBlock, .propOddNondefining,
   .lemComponentReturn, .lemRegularLeviOrbits,
   .lemCharacteristicTwoClifford, .lemNormalCore,
   .lemRationalField, .propGGGRRank, .corPrincipalSelector,
   .lemRankThreePrincipal, .propExceptionalQ3, .propTwoRankThree,
   .lemLocalizedReturn, .highRankInductionStep, .propTwoHighRank,
   .thmTypeB, .corTypeBCensus]

def namedResults : Finset Node := namedResultList.toFinset

/-- Every node, explicitly enumerated without deriving a deeply nested sum instance. -/
def allNodeList : List Node :=
  externalLeafList ++ censusOnlyExternalLeafList ++ namedResultList

@[simp] theorem mem_externalLeaves_iff (n : Node) :
    n ∈ externalLeaves ↔
      kind n ≠ .derived ∧ n ∉ censusOnlyExternalLeaves := by
  cases n <;> decide

@[simp] theorem mem_allExternalLeaves_iff (n : Node) :
    n ∈ allExternalLeaves ↔ kind n ≠ .derived := by
  cases n <;> decide

@[simp] theorem mem_namedResults_iff (n : Node) :
    n ∈ namedResults ↔ kind n = .derived := by
  cases n <;> decide

theorem card_namedResults : namedResults.card = 18 := by decide

theorem card_externalLeaves : externalLeaves.card = 68 := by decide

theorem card_censusOnlyExternalLeaves : censusOnlyExternalLeaves.card = 4 := by decide

theorem card_allExternalLeaves : allExternalLeaves.card = 72 := by decide

set_option linter.flexible false in
/-- The machine-checked dependency graph for the type `B` section. -/
def graph : Graph Node where
  kind := kind
  dependencies := dependencies
  rank := rank
  dependencies_lower := by
    intro n d h
    cases n <;> simp [dependencies, highRankStepInputs] at h
    case propDefiningPrime =>
      rcases h with (rfl | rfl) <;> decide
    case lemConlonBlock =>
      rcases h with (rfl | rfl | rfl | rfl | rfl) <;> decide
    case propOddNondefining =>
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    case lemComponentReturn =>
      rcases h with (rfl | rfl | rfl) <;> decide
    case lemRegularLeviOrbits =>
      rcases h with (rfl | rfl | rfl | rfl | rfl) <;> decide
    case lemCharacteristicTwoClifford =>
      rcases h with (rfl | rfl | rfl | rfl) <;> decide
    case lemNormalCore =>
      rcases h with (rfl | rfl | rfl) <;> decide
    case lemRationalField =>
      rcases h with (rfl | rfl | rfl) <;> decide
    case propGGGRRank =>
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        decide
    case corPrincipalSelector =>
      rcases h with (rfl | rfl | rfl | rfl | rfl) <;> decide
    case lemRankThreePrincipal =>
      rcases h with (rfl | rfl | rfl) <;> decide
    case propExceptionalQ3 =>
      rcases h with
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl) <;> decide
    case propTwoRankThree =>
      rcases h with
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl) <;> decide
    case lemLocalizedReturn =>
      rcases h with
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl) <;> decide
    case highRankInductionStep =>
      rcases h with
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    case propTwoHighRank =>
      rcases h with
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    case thmTypeB =>
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    case corTypeBCensus =>
      rcases h with (rfl | rfl | rfl | rfl | rfl) <;> decide
  external_has_no_dependencies := by
    intro n h
    cases n <;> simp [kind, dependencies] at h ⊢

/-- The high-rank proposition cannot depend immediately on itself. -/
theorem highRank_not_self_dependent :
    Node.propTwoHighRank ∉ dependencies .propTwoHighRank :=
  graph.not_mem_own_dependencies .propTwoHighRank

/-- The localized-return lemma is a proper input to the high-rank proposition, not a cycle. -/
theorem localizedReturn_is_highRank_input :
    Node.lemLocalizedReturn ∈ dependencies .propTwoHighRank := by
  simp [dependencies, highRankStepInputs]

theorem highRank_is_not_localizedReturn_input :
    Node.propTwoHighRank ∉ dependencies .lemLocalizedReturn :=
  graph.no_two_cycle (n := .propTwoHighRank) (d := .lemLocalizedReturn)
    localizedReturn_is_highRank_input

/-- The localized-return lemma uses the independently proved principal selector. -/
theorem principalSelector_is_localizedReturn_input :
    Node.corPrincipalSelector ∈ dependencies .lemLocalizedReturn := by
  simp [dependencies]

/-- The repaired localized-return lemma no longer imports the all-block rank-three result. -/
theorem rankThree_is_not_localizedReturn_input :
    Node.propTwoRankThree ∉ dependencies .lemLocalizedReturn := by
  simp [dependencies]

/-- The local odd-label argument removes the former rank-three-to-high-rank edge. -/
theorem highRank_is_not_rankThree_input :
    Node.propTwoHighRank ∉ dependencies .propTwoRankThree := by
  simp [dependencies]

/-- The high-rank proposition does not import the all-block rank-three result. -/
theorem highRank_does_not_use_rankThree :
    Node.propTwoRankThree ∉ dependencies .propTwoHighRank := by
  simp [dependencies, highRankStepInputs]

/-- The rank-three proposition does not import the later localized-return lemma. -/
theorem rankThree_does_not_use_localizedReturn :
    Node.lemLocalizedReturn ∉ dependencies .propTwoRankThree := by
  simp [dependencies]

/-- The regular-Levi orbit lemma is an explicit input to the high-rank induction step. -/
theorem regularLeviOrbits_is_highRank_input :
    Node.lemRegularLeviOrbits ∈ dependencies .highRankInductionStep := by
  simp [dependencies, highRankStepInputs]

/-- The same regular-Levi orbit lemma is used directly in the rank-three proposition. -/
theorem regularLeviOrbits_is_rankThree_input :
    Node.lemRegularLeviOrbits ∈ dependencies .propTwoRankThree := by
  simp [dependencies]

/-- The rank-three principal-block lemma now uses the manuscript's internal selector rather
than a representative assertion extracted from the cited rank-three proof. -/
theorem principalSelector_is_rankThreePrincipal_input :
    Node.corPrincipalSelector ∈ dependencies .lemRankThreePrincipal := by
  simp [dependencies]

/-- The four rank-indexed assertions separated in the manuscript's high-rank induction.
The induction hypothesis in `step` is explicitly restricted to strictly smaller ranks. -/
structure HighRankInductionData
    (Principal OrbitCondition BAWGood IBAW : ℕ → Prop) where
  principal : ∀ r, 4 ≤ r → Principal r
  step : ∀ r, 4 ≤ r → Principal r →
    (∀ m, 4 ≤ m → m < r → OrbitCondition m) → OrbitCondition r
  localized : ∀ n, 4 ≤ n →
    (∀ r, 4 ≤ r → r ≤ n → Principal r) →
    (∀ r, 4 ≤ r → r ≤ n → OrbitCondition r) → BAWGood n
  finish : ∀ n, 4 ≤ n → BAWGood n → IBAW n

/-- The rank-indexed premises prove the conclusion in every rank at least four. -/
theorem HighRankInductionData.all
    {Principal OrbitCondition BAWGood IBAW : ℕ → Prop}
    (D : HighRankInductionData Principal OrbitCondition BAWGood IBAW) :
    ∀ n, 4 ≤ n → IBAW n := by
  have hOrbit : ∀ n, 4 ≤ n → OrbitCondition n := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        exact D.step n hn (D.principal n hn) (fun m hm hmn => ih m hmn hm)
  intro n hn
  apply D.finish n hn
  exact D.localized n hn
    (fun r hr _ => D.principal r hr)
    (fun r hr _ => hOrbit r hr)

/-- Semantic identification of the graph's high-rank step with the four indexed assertions and
of their conclusion with the manuscript proposition. -/
structure HighRankInductionRealisation
    (I : Interpretation Node) where
  principal : ℕ → Prop
  orbitCondition : ℕ → Prop
  bawGood : ℕ → Prop
  ibaw : ℕ → Prop
  data : I.claim .highRankInductionStep →
    HighRankInductionData principal orbitCondition bawGood ibaw
  close : (∀ n, 4 ≤ n → ibaw n) → I.claim .propTwoHighRank

/-- Strong induction closes the high-rank proposition from the explicitly ranked step.  No
current-rank conclusion is among the hypotheses of that step. -/
theorem propTwoHighRank_of_ranked_induction
    (I : Interpretation Node)
    (H : HighRankInductionRealisation I)
    (hStep : I.claim .highRankInductionStep) :
    I.claim .propTwoHighRank :=
  H.close (H.data hStep).all

set_option linter.flexible false in
/-- No node other than the census corollary has a census-only input as an immediate
dependency. -/
theorem dependency_avoids_census_only {n d : Node}
    (hn : n ≠ .corTypeBCensus) (hd : d ∈ dependencies n) :
    d ∉ censusOnlyExternalLeaves := by
  intro hdcensus
  simp [censusOnlyExternalLeaves, censusOnlyExternalLeafList] at hdcensus
  rcases hdcensus with (rfl | rfl | rfl | rfl) <;>
    cases n <;> simp [dependencies, highRankStepInputs] at hn hd

/-- The census corollary is never an immediate dependency of another node. -/
theorem census_is_not_a_dependency (n : Node) :
    Node.corTypeBCensus ∉ dependencies n := by
  cases n <;> simp [dependencies, highRankStepInputs]

/-- Dependency induction restricted to the ancestor scope of the type-`B` headline. -/
theorem derive_without_census_inputs
    (I : Interpretation Node)
    (hLeaves : ∀ n, n ∈ externalLeaves → I.claim n)
    (rules : DerivedRules graph I) :
    ∀ n, n ≠ .corTypeBCensus → n ∉ censusOnlyExternalLeaves → I.claim n := by
  intro n hncensus hnleaf
  induction n using (measure graph.rank).wf.induction with
  | h n ih =>
      by_cases hn : graph.kind n = .derived
      · apply rules.prove n hn
        intro d hd
        apply ih d (graph.dependencies_lower hd)
        · intro hdcensus
          subst d
          exact census_is_not_a_dependency n hd
        · exact dependency_avoids_census_only hncensus hd
      · exact hLeaves n ((mem_externalLeaves_iff n).2 ⟨hn, hnleaf⟩)

/-- The ranked induction step itself follows from exactly the headline leaves and its declared
lower-rank inputs. -/
theorem highRankInductionStep_of_external_leaves
    (I : Interpretation Node)
    (hLeaves : ∀ n, n ∈ externalLeaves → I.claim n)
    (rules : DerivedRules graph I) :
    I.claim .highRankInductionStep :=
  derive_without_census_inputs I hLeaves rules .highRankInductionStep (by decide) (by decide)

/-- Kernel-checked construction of the high-rank node in which the lower-rank use is mediated by
`Nat.strong_induction_on`. -/
theorem propTwoHighRank_of_external_leaves
    (I : Interpretation Node)
    (hLeaves : ∀ n, n ∈ externalLeaves → I.claim n)
    (rules : DerivedRules graph I)
    (H : HighRankInductionRealisation I) :
    I.claim .propTwoHighRank :=
  propTwoHighRank_of_ranked_induction I H
    (highRankInductionStep_of_external_leaves I hLeaves rules)

/-- If every headline external leaf is true and every named-result proof rule is supplied, then
the type `B` headline follows.  No census-only leaf is assumed. -/
theorem headline_of_exact_external_leaves
    (I : Interpretation Node)
    (hLeaves : ∀ n, n ∈ externalLeaves → I.claim n)
    (rules : DerivedRules graph I) :
    I.claim .thmTypeB :=
  derive_without_census_inputs I hLeaves rules .thmTypeB (by decide) (by decide)

/-- The same certificate continued through the final census corollary. -/
theorem census_of_exact_external_leaves
    (I : Interpretation Node)
    (hLeaves : ∀ n, n ∈ allExternalLeaves → I.claim n)
    (rules : DerivedRules graph I) :
    I.claim .corTypeBCensus := by
  let facts : ExternalFacts graph I :=
    { prove := fun n hn => hLeaves n ((mem_allExternalLeaves_iff n).2 hn) }
  exact graph.derive_all I facts rules .corTypeBCensus

/-- The parameter split at the end of the odd-characteristic type `B` proof is exhaustive. -/
theorem parameter_case_split_certificate
    (Goal : ℕ → ℕ → ℕ → Prop)
    (branches : DependencyCases.TypeBBranchResults Goal)
    (n ell p : ℕ) (hn : 3 ≤ n) (hellPrime : Nat.Prime ell) :
    Goal n ell p :=
  DependencyCases.typeB_of_branch_results Goal branches n ell p hn hellPrime

end Formalisation.TypeBDependencies


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
