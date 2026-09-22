import Formalisation.DependencyGraph
import Formalisation.DependencyCases
import Formalisation.PreliminaryDependencies
import Formalisation.SylowObstruction
import Formalisation.EvenFieldTransport

/-!
# Dependency graph for the type C section

This module is an audit artefact for the results in the manuscript's
symplectic section.  It lists every named result in that section together
with the cited inputs, computations, and still external semantic bridges on
which the proof depends.

The graph deliberately does not use a leaf saying that Proposition 3.3 or
Proposition 3.14 is true.  In particular, the geometric reflection data for
the new exclusion of the omitted even multiplicity radical factors and the
four assertions extracted from Li's proofs before unitriangularity is used
are separate visible leaves.  `ReflectionOvergroupData.contradiction` below
applies the generic theorem in `SylowObstruction` to the precise overgroup
data that the geometric argument must supply.

The isolated `sp6NumericalAudit` node represents the supplementary GAP
calculation.  It is not on a path to `symplectic`: the manuscript uses the
published theorem of Schaeffer Fry for that branch, while the program only
supplies numerical details.

The three transport steps, the final fixed-set closure, and the subsequent
unipotent correspondence in the even-field argument are classified as derived
manuscript arguments. `EvenFieldTransport` checks their elementary group
identities and the restriction-of-irreducibility step. The identification of
those abstract kernels with rational Levi subgroups, relative normalisers,
ordinary characters, and generic-weight orbits remains explicit semantic
input. Dedicated realisations intercept `.evenFieldFixed` and
`.evenUnipotentCorrespondence`, so the public dependency induction cannot use
the unrestricted residual proof rule for either node. This file does not
verify any cited character-theoretic statement or any such semantic
identification.

Proposition 3.8 is split into the verification of Feng--Malle--Zhang
Condition 6.1, block stability, the equivariant finite set bijection, and the
final BAW and iBAW conclusion.  The graph exposes decomposition-map
naturality, block-action semantics, restriction of the Feng--Malle--Zhang
action, and the BAW-good-to-iBAW implication as distinct inputs.  These new
nodes are not yet protected by concrete realisations, so this graph refinement
does not claim a kernel proof of Proposition 3.8.

Proposition 3.9 is likewise split into the conformal factorisation and
Assumption 5.3 branches, the cases in the strictly quasi-isolated block
hypothesis, Jordan reduction, passage from BAW-good blocks to the inductive
condition, and final block aggregation.  The graph keeps the supplementary
`Sp6(2)` numerical audit off every load-bearing path.  The abstract
factorisation and stabiliser kernels are checked in the overlying
`ModularRep` project, while their concrete conformal, Brauer-character, and
block-theoretic interpretations remain semantic inputs here.
-/

namespace Formalisation.TypeCDependencies

open DependencyGraph

/-- Nodes in the dependency audit for the type `C` section. -/
inductive Node where
  -- Realisation bridges from `PreliminaryDependencies`.
  | prelimBlockAggregationRealisation
  | prelimFixedPointDescentRealisation
  | prelimConlonMarkRealisation
  | prelimBasicSetBridgeRealisation
  | prelimCyclicExtensionRealisation
  -- General cited leaves used in the type C section.
  | flzJordanReduction
  | spathDefiningCharacteristic
  | typeCCarrierTable
  | fyzCentreSylowCriterion
  | fyzCorrectedRadicalData
  | fengMallePrincipalParametrisation
  | fengMallePrincipalEquivariance
  | fengMalleCoverPassage
  | typeAIBAWWitnesses
  | bonnafeOddQuasiIsolation
  | schaefferFryRankTwoEven
  | broughSchaefferFryRankTwo
  | rankTwoOrderAndCyclicTorus
  | koshitaniSpathCyclicDefect
  | cabanesEnguehardUnipotentBlocks
  | cabanesSpathFieldInvariance
  | cabanesSpathRationalLeviParametrisation
  | fmzGenericLabelsAndNormalisers
  -- Feng--Malle--Zhang, Proposition 3.20: the type C verification of
  -- Assumption 3.19 used before their Theorem 7.5.
  | fmzAssumption319Verification
  | spathUnipotentMaximalExtendibility
  | cliffordGallagherTheory
  | cabanesSpathRelativeWeylParametrisation
  | fmzUnipotentRelativeWeylCorrespondence
  -- Feng--Malle--Zhang 2026, Theorem 6.2 only.  Its hypotheses and the
  -- restriction of its ambient equivariance are represented separately.
  | fmzGenericWeightsToAlperinWeights
  | geckBlockBasicSet
  -- Malle--Testerman, Proposition 24.21 and Theorem 24.24: diagonal quotient
  -- and generation by the standard automorphism types.  The canonical
  -- semidirect-product realisation requires the separate semantic leaf below.
  | malleTestermanEvenAutomorphismTypes
  -- Feng--Li--Zhang 2022, discussion following equation (3.17).
  | bawGoodImpliesIBAW
  | bonnafeEvenQuasiIsolation
  | schaefferFryLowRankEvenField
  | malleSuzuki
  -- Malle--Testerman, Remark 24.19 and Table 24.3: completeness and entries
  -- of the exceptional multiplier list used in the low-rank case split.
  | malleTestermanTypeCCoverExceptions
  | schaefferFrySp6AtThree
  | liConformalAutomorphismStructure
  | broueMichelSeriesBlocks
  | flzSeriesBasicSets
  | liBlockLabelDirectSummands
  | liLinearCharacterReduction
  | liWeightLabelBijection
  | liOuterGroupStructure
  | broughSpathCriterion
  -- Feng--Li--Zhang 2022, Theorem 3.18, which recalls the full
  -- Brough--Späth criterion rather than a cyclic-outer shortcut.
  | flzBroughSpath318
  -- Navarro 1998, Theorems 3.18 and 8.12, respectively.
  | navarroDefectZeroReduction318
  | navarroCyclicBrauerExtension812
  -- Semantic bridges not supplied by a theorem with exactly this statement.
  | principalEvenMultiplicityReflectionData
  | evenNormalizerQuotientIdentification
  | evenRationalLeviTransportRealisation
  | evenRelativeNormaliserFieldActionRealisation
  | evenCliffordGallagherTransportRealisation
  -- Concrete group, block, action, character-realisation, and covering-group
  -- data needed to specialise the full Brough--Späth criterion.
  | cyclicOuterGroupDataRealisation
  | cyclicOuterCharacterActionRealisation
  | selfUniversalEllPrimeCoverRealisation
  -- Atomic and semantic inputs used in Proposition 3.8.  In particular,
  -- decomposition-map naturality is not part of Geck's basic-set theorem.
  | evenCondition61Data
  | evenUnipotentBlockActionRealisation
  | evenDecompositionMapNaturality
  | evenFMZActionRestrictionRealisation
  -- Triviality of the field/inner intersection and identification of the
  -- canonical semidirect map with all automorphisms.
  | evenFieldInnerIntersectionRealisation
  -- Concrete multiplier, Brauer action, extension, and Jordan-cover data
  -- used in Proposition 3.9.
  | evenConformalMultiplierRealisation
  | evenBrauerActionRealisation
  | evenBrauerExtensionRealisation
  | evenJordanCoverRealisation
  -- The prime-outside-order branch needs both group-theoretic and block or
  -- modular-character-triple interpretations.
  | primeOutsideOrderGroupRealisation
  | primeOutsideOrderBlockDataRealisation
  | primeOutsideOrderTripleIdentityRealisation
  -- Classification and semantic bridges in the strictly quasi-isolated
  -- branch of Proposition 3.9.
  | typeCConnectedSubdiagramRealisation
  | typeCSteinbergFormsRealisation
  | evenQuasiIsolationSemanticsRealisation
  | identitySeriesUnipotentBlockRealisation
  | typeCLowRankExclusionsRealisation
  | sp6DoubleCoverOrderRealisation
  | blockDefectGroupPrimeSubgroupRealisation
  | ibawBijectionToInductiveBAWRealisation
  | liBlockOrbitLengthsExtraction
  | liWeightMapEquivarianceExtraction
  | liOrdinaryStabiliserExtraction
  | liWeightStabiliserExtensionExtraction
  | caseSplitArithmeticInputs
  -- Supplementary computation, intentionally not load bearing.
  | sp6NumericalAudit
  -- Derived preliminary tools.
  | blockAggregation
  | fixedPointDescent
  | conlonMark
  | basicSetBridge
  | cyclicExtension
  -- Derived intermediate and named type C results.
  | jordanReduction
  | principalEvenMultiplicityExclusion
  | principalTwoBlockBridge
  | oddTwo
  | rankTwo
  | evenRationalLeviTransport
  | evenRelativeNormaliserFieldAction
  | evenCliffordGallagherTransport
  | evenFieldFixed
  | evenUnipotentCorrespondence
  | cyclicOuterStructuralConditions
  | cyclicOuterStabilizerIdentities
  | cyclicOuterGlobalExtension
  | cyclicOuterLocalExtension
  | cyclicOuterFLZHypotheses
  | cyclicOuterBAW
  | evenAutomorphismStructure
  | evenConformalFactorisation
  | evenConformalInnerAction
  | evenBrauerCharactersFixed
  | evenBrauerStabiliserFactorisation
  | evenBrauerCharacterExtension
  | evenAssumption53
  | evenFMZCondition61
  | evenUnipotentBlockStable
  | evenUnipotentBijection
  | evenUnipotent
  | primeOutsideOrderRadicalTriviality
  | primeOutsideOrderIBAW
  | evenTypeABlockIBAW
  | strictQuasiIsolatedImpliesQuasiIsolated
  | evenQuasiIsolatedLabelIdentity
  | evenStrictBlockUnipotent
  | evenSplitLowRankBlockIBAW
  | sp6CyclicSubgroups
  | sp6CyclicDefect
  | evenSp6BlockIBAW
  | evenSuzukiBlockIBAW
  | evenLowRankExhaustion
  | evenStrictBlockHypothesis
  | evenJordanCoverHypotheses
  | evenAllBlocksBAWGood
  | evenAllBlocksInductiveBAW
  | evenSimpleIBAW
  | evenBridge
  | exactStabiliser
  | oddConformalBridge
  | oddGFactorisation
  | oddWeightLabelMap
  | oddConlon
  | sp6FiveOrSeven
  | symplectic
  deriving DecidableEq, Repr

/-- Provenance classification of the type C dependency nodes. -/
def kind : Node → NodeKind
  | .prelimBlockAggregationRealisation
  | .prelimFixedPointDescentRealisation
  | .prelimConlonMarkRealisation
  | .prelimBasicSetBridgeRealisation
  | .prelimCyclicExtensionRealisation
  | .principalEvenMultiplicityReflectionData
  | .evenNormalizerQuotientIdentification
  | .evenRationalLeviTransportRealisation
  | .evenRelativeNormaliserFieldActionRealisation
  | .evenCliffordGallagherTransportRealisation
  | .cyclicOuterGroupDataRealisation
  | .cyclicOuterCharacterActionRealisation
  | .selfUniversalEllPrimeCoverRealisation
  | .evenCondition61Data
  | .evenUnipotentBlockActionRealisation
  | .evenDecompositionMapNaturality
  | .evenFMZActionRestrictionRealisation
  | .evenFieldInnerIntersectionRealisation
  | .evenConformalMultiplierRealisation
  | .evenBrauerActionRealisation
  | .evenBrauerExtensionRealisation
  | .evenJordanCoverRealisation
  | .primeOutsideOrderGroupRealisation
  | .primeOutsideOrderBlockDataRealisation
  | .primeOutsideOrderTripleIdentityRealisation
  | .typeCConnectedSubdiagramRealisation
  | .typeCSteinbergFormsRealisation
  | .evenQuasiIsolationSemanticsRealisation
  | .identitySeriesUnipotentBlockRealisation
  | .typeCLowRankExclusionsRealisation
  | .sp6DoubleCoverOrderRealisation
  | .blockDefectGroupPrimeSubgroupRealisation
  | .ibawBijectionToInductiveBAWRealisation
  | .liBlockOrbitLengthsExtraction
  | .liWeightMapEquivarianceExtraction
  | .liOrdinaryStabiliserExtraction
  | .liWeightStabiliserExtensionExtraction
  | .caseSplitArithmeticInputs => .semanticBridge
  | .sp6NumericalAudit => .computation
  | .blockAggregation
  | .fixedPointDescent
  | .conlonMark
  | .basicSetBridge
  | .cyclicExtension
  | .jordanReduction
  | .principalEvenMultiplicityExclusion
  | .principalTwoBlockBridge
  | .oddTwo
  | .rankTwo
  | .evenRationalLeviTransport
  | .evenRelativeNormaliserFieldAction
  | .evenCliffordGallagherTransport
  | .evenFieldFixed
  | .evenUnipotentCorrespondence
  | .cyclicOuterStructuralConditions
  | .cyclicOuterStabilizerIdentities
  | .cyclicOuterGlobalExtension
  | .cyclicOuterLocalExtension
  | .cyclicOuterFLZHypotheses
  | .cyclicOuterBAW
  | .evenAutomorphismStructure
  | .evenConformalFactorisation
  | .evenConformalInnerAction
  | .evenBrauerCharactersFixed
  | .evenBrauerStabiliserFactorisation
  | .evenBrauerCharacterExtension
  | .evenAssumption53
  | .evenFMZCondition61
  | .evenUnipotentBlockStable
  | .evenUnipotentBijection
  | .evenUnipotent
  | .primeOutsideOrderRadicalTriviality
  | .primeOutsideOrderIBAW
  | .evenTypeABlockIBAW
  | .strictQuasiIsolatedImpliesQuasiIsolated
  | .evenQuasiIsolatedLabelIdentity
  | .evenStrictBlockUnipotent
  | .evenSplitLowRankBlockIBAW
  | .sp6CyclicSubgroups
  | .sp6CyclicDefect
  | .evenSp6BlockIBAW
  | .evenSuzukiBlockIBAW
  | .evenLowRankExhaustion
  | .evenStrictBlockHypothesis
  | .evenJordanCoverHypotheses
  | .evenAllBlocksBAWGood
  | .evenAllBlocksInductiveBAW
  | .evenSimpleIBAW
  | .evenBridge
  | .exactStabiliser
  | .oddConformalBridge
  | .oddGFactorisation
  | .oddWeightLabelMap
  | .oddConlon
  | .sp6FiveOrSeven
  | .symplectic => .derived
  | _ => .cited

/-- Immediate dependencies.  The Li extractions and the geometric data for
the principal-block reflection remain individual leaves rather than being
hidden in a proposition with the desired conclusion.  The final Sylow
contradiction is formalised in `SylowObstruction`. -/
def dependencies : Node → List Node
  | .blockAggregation => [.prelimBlockAggregationRealisation]
  | .fixedPointDescent => [.prelimFixedPointDescentRealisation]
  | .conlonMark => [.prelimConlonMarkRealisation]
  | .basicSetBridge => [.prelimBasicSetBridgeRealisation]
  | .cyclicExtension => [.prelimCyclicExtensionRealisation]
  | .jordanReduction => [.flzJordanReduction]
  | .principalEvenMultiplicityExclusion =>
      [.fyzCentreSylowCriterion, .fyzCorrectedRadicalData,
       .principalEvenMultiplicityReflectionData]
  | .principalTwoBlockBridge =>
      [.fyzCorrectedRadicalData, .fengMallePrincipalParametrisation,
       .fengMallePrincipalEquivariance,
       .principalEvenMultiplicityExclusion]
  | .oddTwo =>
      [.principalTwoBlockBridge, .jordanReduction, .typeAIBAWWitnesses,
       .bonnafeOddQuasiIsolation, .fengMalleCoverPassage,
       .typeCCarrierTable, .blockAggregation]
  | .rankTwo =>
      [.spathDefiningCharacteristic, .schaefferFryRankTwoEven, .oddTwo,
       .broughSchaefferFryRankTwo, .rankTwoOrderAndCyclicTorus,
       .koshitaniSpathCyclicDefect, .typeCCarrierTable, .blockAggregation]
  | .evenRationalLeviTransport =>
      [.cabanesSpathRationalLeviParametrisation,
       .cabanesSpathFieldInvariance,
       .evenRationalLeviTransportRealisation]
  | .evenRelativeNormaliserFieldAction =>
      [.evenRationalLeviTransport, .evenNormalizerQuotientIdentification,
       .evenRelativeNormaliserFieldActionRealisation]
  | .evenCliffordGallagherTransport =>
      [.evenRationalLeviTransport, .evenRelativeNormaliserFieldAction,
       .spathUnipotentMaximalExtendibility, .cliffordGallagherTheory,
       .evenCliffordGallagherTransportRealisation]
  | .evenFieldFixed =>
      [.cabanesEnguehardUnipotentBlocks, .fmzGenericLabelsAndNormalisers,
       .evenRationalLeviTransport, .evenRelativeNormaliserFieldAction,
       .evenCliffordGallagherTransport]
  | .evenUnipotentCorrespondence =>
      [.evenFieldFixed, .cabanesEnguehardUnipotentBlocks,
       .cabanesSpathRelativeWeylParametrisation,
       .fmzAssumption319Verification,
       .fmzUnipotentRelativeWeylCorrespondence]
  | .cyclicOuterStructuralConditions =>
      [.cyclicOuterGroupDataRealisation,
       .selfUniversalEllPrimeCoverRealisation]
  | .cyclicOuterStabilizerIdentities =>
      [.cyclicOuterGroupDataRealisation,
       .cyclicOuterCharacterActionRealisation]
  | .cyclicOuterGlobalExtension =>
      [.cyclicOuterStabilizerIdentities,
       .navarroCyclicBrauerExtension812,
       .cyclicOuterCharacterActionRealisation]
  | .cyclicOuterLocalExtension =>
      [.cyclicOuterStabilizerIdentities,
       .navarroDefectZeroReduction318,
       .navarroCyclicBrauerExtension812,
       .cyclicOuterCharacterActionRealisation]
  | .cyclicOuterFLZHypotheses =>
      [.cyclicOuterStructuralConditions,
       .cyclicOuterStabilizerIdentities,
       .cyclicOuterGlobalExtension, .cyclicOuterLocalExtension,
       .cyclicOuterCharacterActionRealisation,
       .selfUniversalEllPrimeCoverRealisation]
  | .cyclicOuterBAW => [.flzBroughSpath318, .cyclicOuterFLZHypotheses]
  | .evenAutomorphismStructure =>
      [.malleTestermanEvenAutomorphismTypes,
       .evenFieldInnerIntersectionRealisation]
  | .evenConformalFactorisation =>
      [.evenConformalMultiplierRealisation]
  | .evenConformalInnerAction =>
      [.evenConformalFactorisation,
       .evenConformalMultiplierRealisation]
  | .evenBrauerCharactersFixed =>
      [.evenConformalInnerAction,
       .evenBrauerActionRealisation]
  | .evenBrauerStabiliserFactorisation =>
      [.evenBrauerCharactersFixed, .evenAutomorphismStructure,
       .evenBrauerActionRealisation]
  | .evenBrauerCharacterExtension =>
      [.evenAutomorphismStructure, .cyclicExtension,
       .evenBrauerExtensionRealisation]
  | .evenAssumption53 =>
      [.evenBrauerStabiliserFactorisation,
       .evenBrauerCharacterExtension]
  | .evenFMZCondition61 => [.evenCondition61Data]
  | .evenUnipotentBlockStable =>
      [.evenFieldFixed, .geckBlockBasicSet,
       .evenUnipotentBlockActionRealisation]
  | .evenUnipotentBijection =>
      [.evenUnipotentBlockStable, .evenUnipotentCorrespondence,
       .geckBlockBasicSet, .basicSetBridge,
       .fmzGenericWeightsToAlperinWeights, .evenFMZCondition61,
       .evenDecompositionMapNaturality,
       .evenFMZActionRestrictionRealisation,
       .evenUnipotentBlockActionRealisation,
       .evenAutomorphismStructure]
  | .evenUnipotent =>
      [.evenUnipotentBlockStable, .evenUnipotentBijection,
       .cyclicOuterBAW, .evenAutomorphismStructure,
       .typeCCarrierTable, .bawGoodImpliesIBAW]
  | .primeOutsideOrderRadicalTriviality =>
      [.primeOutsideOrderGroupRealisation]
  | .primeOutsideOrderIBAW =>
      [.primeOutsideOrderRadicalTriviality,
       .primeOutsideOrderBlockDataRealisation,
       .primeOutsideOrderTripleIdentityRealisation]
  | .evenTypeABlockIBAW =>
      [.typeAIBAWWitnesses, .bawGoodImpliesIBAW]
  | .strictQuasiIsolatedImpliesQuasiIsolated =>
      [.evenQuasiIsolationSemanticsRealisation]
  | .evenQuasiIsolatedLabelIdentity =>
      [.strictQuasiIsolatedImpliesQuasiIsolated,
       .bonnafeEvenQuasiIsolation]
  | .evenStrictBlockUnipotent =>
      [.evenQuasiIsolatedLabelIdentity,
       .identitySeriesUnipotentBlockRealisation]
  | .evenSplitLowRankBlockIBAW =>
      [.schaefferFryLowRankEvenField, .fixedPointDescent]
  | .sp6CyclicSubgroups =>
      [.sp6DoubleCoverOrderRealisation]
  | .sp6CyclicDefect =>
      [.sp6CyclicSubgroups,
       .blockDefectGroupPrimeSubgroupRealisation]
  | .evenSp6BlockIBAW =>
      [.sp6FiveOrSeven, .schaefferFrySp6AtThree,
       .fixedPointDescent]
  | .evenSuzukiBlockIBAW =>
      [.malleSuzuki, .malleTestermanTypeCCoverExceptions,
       .fixedPointDescent]
  | .evenLowRankExhaustion =>
      [.typeCSteinbergFormsRealisation,
       .typeCLowRankExclusionsRealisation,
       .malleTestermanTypeCCoverExceptions,
       .sp6DoubleCoverOrderRealisation]
  | .evenStrictBlockHypothesis =>
      [.primeOutsideOrderIBAW,
       .typeCConnectedSubdiagramRealisation,
       .evenTypeABlockIBAW, .evenStrictBlockUnipotent,
       .evenUnipotent, .evenSplitLowRankBlockIBAW,
       .evenSp6BlockIBAW, .evenSuzukiBlockIBAW,
       .evenLowRankExhaustion]
  | .evenJordanCoverHypotheses =>
      [.typeCCarrierTable, .evenJordanCoverRealisation]
  | .evenAllBlocksBAWGood =>
      [.jordanReduction, .evenAssumption53,
       .evenStrictBlockHypothesis, .evenJordanCoverHypotheses]
  | .evenAllBlocksInductiveBAW =>
      [.evenAllBlocksBAWGood, .bawGoodImpliesIBAW,
       .ibawBijectionToInductiveBAWRealisation]
  | .evenSimpleIBAW =>
      [.evenAllBlocksInductiveBAW, .blockAggregation,
       .evenJordanCoverHypotheses]
  | .evenBridge =>
      [.evenAllBlocksBAWGood, .evenSimpleIBAW]
  | .exactStabiliser => [.liBlockOrbitLengthsExtraction]
  | .oddConformalBridge =>
      [.exactStabiliser, .liConformalAutomorphismStructure,
       .flzSeriesBasicSets, .liBlockLabelDirectSummands,
       .liLinearCharacterReduction, .basicSetBridge]
  | .oddGFactorisation =>
      [.broueMichelSeriesBlocks, .flzSeriesBasicSets,
       .liOuterGroupStructure, .liOrdinaryStabiliserExtraction,
       .basicSetBridge, .cyclicExtension]
  | .oddWeightLabelMap =>
      [.liWeightLabelBijection, .liWeightMapEquivarianceExtraction]
  | .oddConlon =>
      [.oddConformalBridge, .oddGFactorisation, .oddWeightLabelMap,
       .liConformalAutomorphismStructure, .broughSpathCriterion,
       .liWeightStabiliserExtensionExtraction, .liOuterGroupStructure,
       .cyclicExtension, .blockAggregation]
  | .sp6FiveOrSeven =>
      [.sp6CyclicDefect, .koshitaniSpathCyclicDefect,
       .typeCCarrierTable,
       .blockAggregation]
  | .symplectic =>
      [.rankTwo, .spathDefiningCharacteristic, .oddTwo, .oddConlon,
       .sp6FiveOrSeven, .schaefferFrySp6AtThree,
       .schaefferFryLowRankEvenField, .evenBridge,
       .typeCCarrierTable, .caseSplitArithmeticInputs]
  | _ => []

/-- A rank certificate for the graph. -/
def rank : Node → ℕ
  | .blockAggregation
  | .fixedPointDescent
  | .conlonMark
  | .cyclicExtension
  | .jordanReduction
  | .principalEvenMultiplicityExclusion
  | .evenRationalLeviTransport
  | .exactStabiliser
  | .oddWeightLabelMap
  | .cyclicOuterStructuralConditions
  | .cyclicOuterStabilizerIdentities
  | .evenFMZCondition61
  | .evenAutomorphismStructure
  | .evenConformalFactorisation
  | .primeOutsideOrderRadicalTriviality
  | .evenTypeABlockIBAW
  | .strictQuasiIsolatedImpliesQuasiIsolated
  | .sp6CyclicSubgroups
  | .evenLowRankExhaustion
  | .evenJordanCoverHypotheses => 1
  | .basicSetBridge
  | .principalTwoBlockBridge
  | .evenRelativeNormaliserFieldAction
  | .cyclicOuterGlobalExtension
  | .cyclicOuterLocalExtension
  | .evenConformalInnerAction
  | .evenBrauerCharacterExtension
  | .primeOutsideOrderIBAW
  | .evenQuasiIsolatedLabelIdentity
  | .evenSplitLowRankBlockIBAW
  | .sp6CyclicDefect
  | .evenSuzukiBlockIBAW => 2
  | .oddTwo
  | .evenCliffordGallagherTransport
  | .oddConformalBridge
  | .oddGFactorisation
  | .cyclicOuterFLZHypotheses
  | .evenBrauerCharactersFixed
  | .evenStrictBlockUnipotent
  | .sp6FiveOrSeven => 3
  | .rankTwo
  | .evenFieldFixed
  | .oddConlon
  | .cyclicOuterBAW
  | .evenBrauerStabiliserFactorisation
  | .evenSp6BlockIBAW => 4
  | .evenUnipotentCorrespondence
  | .evenUnipotentBlockStable
  | .evenAssumption53 => 5
  | .evenUnipotentBijection => 6
  | .evenUnipotent => 7
  | .evenStrictBlockHypothesis => 8
  | .evenAllBlocksBAWGood => 9
  | .evenAllBlocksInductiveBAW => 10
  | .evenSimpleIBAW => 11
  | .evenBridge => 12
  | .symplectic => 13
  | _ => 0

private def rankCertificate (n : Node) : Bool :=
  (dependencies n).all fun d => decide (rank d < rank n)

private theorem rankCertificate_true (n : Node) :
    rankCertificate n = true := by
  cases n <;> rfl

/-- The complete type C audit graph. -/
def graph : Graph Node where
  kind := kind
  dependencies := dependencies
  rank := rank
  dependencies_lower := by
    intro n d hd
    have hcert := List.all_eq_true.mp (rankCertificate_true n)
    exact of_decide_eq_true (hcert d hd)
  external_has_no_dependencies := by
    intro n hn
    cases n <;> simp [kind, dependencies] at hn ⊢

/-- Explicit interpretation of the five preliminary realisation leaves.

The two dependency graphs use different node types and arbitrary
`Interpretation`s.  These maps are therefore necessary: Lean cannot infer
that, for example, the claim assigned to the preliminary block-orbit lemma
is the claim assigned to the type `C` block-aggregation input. -/
structure PreliminaryRealisation
    (I : Interpretation Node)
    (P : Interpretation PreliminaryDependencies.Node) where
  blockAggregation : P.claim .blockOrbitAggregation →
    I.claim .prelimBlockAggregationRealisation
  fixedPointDescent : P.claim .fixedPointDescentCorollary →
    I.claim .prelimFixedPointDescentRealisation
  conlonMark : P.claim .conlonMarkCorollary →
    I.claim .prelimConlonMarkRealisation
  basicSetBridge : P.claim .integralBasicSetBridge →
    I.claim .prelimBasicSetBridgeRealisation
  cyclicExtension : P.claim .cyclicCharacterExtension →
    I.claim .prelimCyclicExtensionRealisation

/-- The preliminary dependency certificate supplies the five type `C`
realisation leaves once their meanings have been related explicitly. -/
theorem realised_preliminary_leaves
    (I : Interpretation Node)
    (P : Interpretation PreliminaryDependencies.Node)
    (E : ExternalFacts PreliminaryDependencies.graph P)
    (R : DerivedRules PreliminaryDependencies.graph P)
    (L : PreliminaryRealisation I P) :
    I.claim .prelimBlockAggregationRealisation ∧
      I.claim .prelimFixedPointDescentRealisation ∧
      I.claim .prelimConlonMarkRealisation ∧
      I.claim .prelimBasicSetBridgeRealisation ∧
      I.claim .prelimCyclicExtensionRealisation := by
  have hall := PreliminaryDependencies.graph.derive_all P E R
  exact ⟨L.blockAggregation (hall .blockOrbitAggregation),
    L.fixedPointDescent (hall .fixedPointDescentCorollary),
    L.conlonMark (hall .conlonMarkCorollary),
    L.basicSetBridge (hall .integralBasicSetBridge),
    L.cyclicExtension (hall .cyclicCharacterExtension)⟩

/-- The exact group-theoretic output required from the geometric reflection
construction.  The proposed centre is represented by `centreSylow`, while
`overgroup` is the larger `2`-subgroup obtained by adjoining the reflection. -/
structure ReflectionOvergroupData (G : Type*) [Group G] where
  centreSylow : Sylow 2 G
  overgroup : Subgroup G
  overgroup_isTwoGroup : IsPGroup 2 overgroup
  centre_le_overgroup : (centreSylow : Subgroup G) ≤ overgroup
  reflection : G
  reflection_mem_overgroup : reflection ∈ overgroup
  reflection_not_mem_centre : reflection ∉ (centreSylow : Subgroup G)

/-- Actual invocation of the formal Sylow obstruction. -/
theorem ReflectionOvergroupData.contradiction
    {G : Type*} [Group G] (D : ReflectionOvergroupData G) : False :=
  SylowObstruction.false_of_element_in_p_overgroup
    D.centreSylow D.overgroup D.overgroup_isTwoGroup
    D.centre_le_overgroup D.reflection_mem_overgroup
    D.reflection_not_mem_centre

/-- If the external geometry constructs `ReflectionOvergroupData` from a
candidate omitted component, that candidate is excluded by the checked
Sylow argument. -/
theorem exclude_candidate_of_reflection_data
    {G : Type*} [Group G] {Candidate : Prop}
    (construct : Candidate → ReflectionOvergroupData G) : ¬ Candidate := by
  intro hCandidate
  exact (construct hCandidate).contradiction

/-- Connect an interpretation of the reflection-data leaf to the checked
obstruction without identifying that leaf with the desired exclusion. -/
theorem principal_exclusion_of_realised_reflection_leaf
    (I : Interpretation Node) {G : Type*} [Group G] {Candidate : Prop}
    (realise : I.claim .principalEvenMultiplicityReflectionData →
      Candidate → ReflectionOvergroupData G)
    (hreflection : I.claim .principalEvenMultiplicityReflectionData) :
    ¬ Candidate :=
  exclude_candidate_of_reflection_data (realise hreflection)

/-- A reflection obstruction together with its ambient group structure.  The
carrier is packaged because the concrete centraliser depends on the omitted
candidate in the manuscript's geometric construction. -/
structure PackedReflectionOvergroupData where
  carrier : Type
  group : Group carrier
  data : @ReflectionOvergroupData carrier group

theorem PackedReflectionOvergroupData.contradiction
    (D : PackedReflectionOvergroupData) : False :=
  @ReflectionOvergroupData.contradiction D.carrier D.group D.data

/-- Semantic identifications needed to turn the checked Sylow contradiction
into the manuscript node excluding the omitted even multiplicity candidate.
The construction of the concrete centraliser and reflection remains an
explicit input. -/
structure PrincipalExclusionRealisation (I : Interpretation Node) where
  candidate : Prop
  construct : I.claim .fyzCentreSylowCriterion →
    I.claim .fyzCorrectedRadicalData →
    I.claim .principalEvenMultiplicityReflectionData →
    candidate → PackedReflectionOvergroupData
  close : (¬ candidate) → I.claim .principalEvenMultiplicityExclusion

/-- Apply the formal Sylow obstruction to the realised manuscript geometry. -/
theorem principal_exclusion_of_realisation
    (I : Interpretation Node)
    (H : PrincipalExclusionRealisation I)
    (hcriterion : I.claim .fyzCentreSylowCriterion)
    (hcorrected : I.claim .fyzCorrectedRadicalData)
    (hreflection : I.claim .principalEvenMultiplicityReflectionData) :
    I.claim .principalEvenMultiplicityExclusion := by
  apply H.close
  intro hcandidate
  exact (H.construct hcriterion hcorrected hreflection hcandidate).contradiction

/-- Override the unrestricted proof rule for the principal exclusion by the
checked Sylow argument and its explicit semantic realisation. -/
theorem rulesWithRealisedPrincipalExclusion
    (I : Interpretation Node)
    (rules : DerivedRules graph I)
    (H : PrincipalExclusionRealisation I) : DerivedRules graph I where
  prove n hn hdeps := by
    by_cases h : n = .principalEvenMultiplicityExclusion
    · subst n
      exact principal_exclusion_of_realisation I H
        (hdeps .fyzCentreSylowCriterion (by decide))
        (hdeps .fyzCorrectedRadicalData (by decide))
        (hdeps .principalEvenMultiplicityReflectionData (by decide))
    · exact rules.prove n hn hdeps

/-- Semantic maps connecting the kernel-checked elementary transport
principles to the three concrete steps in the even-field proof.

The `close...` fields are intentionally explicit.  They contain the
algebraic-group and character-theoretic identification that cannot be
inferred from the abstract group identities alone. -/
structure EvenFieldTransportRealisation (I : Interpretation Node) where
  closeRationalLevi :
    I.claim .cabanesSpathRationalLeviParametrisation →
    I.claim .cabanesSpathFieldInvariance →
    I.claim .evenRationalLeviTransportRealisation →
    EvenFieldTransport.LangTransportPrinciple →
    I.claim .evenRationalLeviTransport
  closeRelativeNormaliser :
    I.claim .evenRationalLeviTransport →
    I.claim .evenNormalizerQuotientIdentification →
    I.claim .evenRelativeNormaliserFieldActionRealisation →
    EvenFieldTransport.RelativeNormalizerPrinciple →
    I.claim .evenRelativeNormaliserFieldAction
  closeCliffordGallagher :
    I.claim .evenRationalLeviTransport →
    I.claim .evenRelativeNormaliserFieldAction →
    I.claim .spathUnipotentMaximalExtendibility →
    I.claim .cliffordGallagherTheory →
    I.claim .evenCliffordGallagherTransportRealisation →
    EvenFieldTransport.IntermediateIrreducibilityPrinciple →
    I.claim .evenCliffordGallagherTransport

/-- Semantic map from the five explicit dependencies of Lemma 3.6 to the
claim assigned to `.evenFieldFixed`.

This is kept separate from `DerivedRules`: downstream interpretations can
construct it by applying the checked pointwise fixed-set closure, while this
formalisation package remains below those concrete character and orbit types
in the import graph. -/
structure EvenFieldFixedRealisation (I : Interpretation Node) where
  closeFieldFixed :
    I.claim .cabanesEnguehardUnipotentBlocks →
    I.claim .fmzGenericLabelsAndNormalisers →
    I.claim .evenRationalLeviTransport →
    I.claim .evenRelativeNormaliserFieldAction →
    I.claim .evenCliffordGallagherTransport →
    I.claim .evenFieldFixed

/-- Semantic map from the five explicit dependencies of Lemma 3.7 to the
claim assigned to `.evenUnipotentCorrespondence`.

The concrete realisation in `ModularRep` separately exposes the Lang
identification, the restricted Feng--Malle--Zhang coproduct, and the construction
of local generic-weight parameters into weight orbits. -/
structure EvenUnipotentCorrespondenceRealisation
    (I : Interpretation Node) where
  closeCorrespondence :
    I.claim .evenFieldFixed →
    I.claim .cabanesEnguehardUnipotentBlocks →
    I.claim .cabanesSpathRelativeWeylParametrisation →
    I.claim .fmzAssumption319Verification →
    I.claim .fmzUnipotentRelativeWeylCorrespondence →
    I.claim .evenUnipotentCorrespondence

/-- Override the unrestricted proof rules for the three even-field transport
nodes, `.evenFieldFixed`, and `.evenUnipotentCorrespondence` by the checked
kernels and explicit semantic realisations. -/
theorem rulesWithRealisedEvenFieldTransport
    (I : Interpretation Node)
    (rules : DerivedRules graph I)
    (H : EvenFieldTransportRealisation I)
    (F : EvenFieldFixedRealisation I)
    (U : EvenUnipotentCorrespondenceRealisation I) :
    DerivedRules graph I where
  prove n hn hdeps := by
    by_cases hRational : n = .evenRationalLeviTransport
    · subst n
      exact H.closeRationalLevi
        (hdeps .cabanesSpathRationalLeviParametrisation (by decide))
        (hdeps .cabanesSpathFieldInvariance (by decide))
        (hdeps .evenRationalLeviTransportRealisation (by decide))
        EvenFieldTransport.langTransportPrinciple
    by_cases hRelative : n = .evenRelativeNormaliserFieldAction
    · subst n
      exact H.closeRelativeNormaliser
        (hdeps .evenRationalLeviTransport (by decide))
        (hdeps .evenNormalizerQuotientIdentification (by decide))
        (hdeps .evenRelativeNormaliserFieldActionRealisation (by decide))
        EvenFieldTransport.relativeNormalizerPrinciple
    by_cases hClifford : n = .evenCliffordGallagherTransport
    · subst n
      exact H.closeCliffordGallagher
        (hdeps .evenRationalLeviTransport (by decide))
        (hdeps .evenRelativeNormaliserFieldAction (by decide))
        (hdeps .spathUnipotentMaximalExtendibility (by decide))
        (hdeps .cliffordGallagherTheory (by decide))
        (hdeps .evenCliffordGallagherTransportRealisation (by decide))
        EvenFieldTransport.intermediateIrreducibilityPrinciple
    by_cases hFixed : n = .evenFieldFixed
    · subst n
      exact F.closeFieldFixed
        (hdeps .cabanesEnguehardUnipotentBlocks (by decide))
        (hdeps .fmzGenericLabelsAndNormalisers (by decide))
        (hdeps .evenRationalLeviTransport (by decide))
        (hdeps .evenRelativeNormaliserFieldAction (by decide))
        (hdeps .evenCliffordGallagherTransport (by decide))
    by_cases hCorrespondence : n = .evenUnipotentCorrespondence
    · subst n
      exact U.closeCorrespondence
        (hdeps .evenFieldFixed (by decide))
        (hdeps .cabanesEnguehardUnipotentBlocks (by decide))
        (hdeps .cabanesSpathRelativeWeylParametrisation (by decide))
        (hdeps .fmzAssumption319Verification (by decide))
        (hdeps .fmzUnipotentRelativeWeylCorrespondence (by decide))
    exact rules.prove n hn hdeps

theorem dependency_rank_decreases {n d : Node}
    (h : d ∈ dependencies n) : rank d < rank n :=
  graph.dependencies_lower h

theorem dependency_graph_is_irreflexive (n : Node) :
    n ∉ dependencies n :=
  graph.not_mem_own_dependencies n

theorem dependency_graph_has_no_two_cycle {n d : Node}
    (h : d ∈ dependencies n) : n ∉ dependencies d :=
  graph.no_two_cycle h

theorem symplectic_rank : rank .symplectic = 13 := rfl

/-- The numerical audit is present in the ledger but is not an immediate
dependency of any node.  In particular it is not needed for the headline
derivation. -/
theorem sp6NumericalAudit_not_a_dependency (n : Node) :
    Node.sp6NumericalAudit ∉ dependencies n := by
  cases n <;> simp [dependencies]

/-- External facts needed on the route to the headline result.  The
supplementary numerical audit is deliberately excluded. -/
structure HeadlineExternalFacts (I : Interpretation Node) where
  prove : ∀ n, graph.kind n ≠ NodeKind.derived →
    n ≠ .sp6NumericalAudit → I.claim n

/-- External facts other than the five leaves realised by the preliminary
dependency certificate. -/
structure NonPreliminaryExternalFacts (I : Interpretation Node) where
  prove : ∀ n, graph.kind n ≠ NodeKind.derived →
    n ≠ .sp6NumericalAudit →
    n ≠ .prelimBlockAggregationRealisation →
    n ≠ .prelimFixedPointDescentRealisation →
    n ≠ .prelimConlonMarkRealisation →
    n ≠ .prelimBasicSetBridgeRealisation →
    n ≠ .prelimCyclicExtensionRealisation → I.claim n

/-- Combine the checked preliminary graph with the remaining external type
`C` inputs.  The interpretation maps in `PreliminaryRealisation` are the only
semantic identifications made between the two graphs. -/
theorem HeadlineExternalFacts.ofPreliminary
    (I : Interpretation Node)
    (P : Interpretation PreliminaryDependencies.Node)
    (E : ExternalFacts PreliminaryDependencies.graph P)
    (R : DerivedRules PreliminaryDependencies.graph P)
    (L : PreliminaryRealisation I P)
    (T : NonPreliminaryExternalFacts I) : HeadlineExternalFacts I where
  prove n hderived hnumerical := by
    have hpreliminary := realised_preliminary_leaves I P E R L
    by_cases h₁ : n = .prelimBlockAggregationRealisation
    · subst n
      exact hpreliminary.1
    by_cases h₂ : n = .prelimFixedPointDescentRealisation
    · subst n
      exact hpreliminary.2.1
    by_cases h₃ : n = .prelimConlonMarkRealisation
    · subst n
      exact hpreliminary.2.2.1
    by_cases h₄ : n = .prelimBasicSetBridgeRealisation
    · subst n
      exact hpreliminary.2.2.2.1
    by_cases h₅ : n = .prelimCyclicExtensionRealisation
    · subst n
      exact hpreliminary.2.2.2.2
    exact T.prove n hderived hnumerical h₁ h₂ h₃ h₄ h₅

/-- Internal dependency induction after all protected proof rules have been
replaced by their realised versions. -/
private theorem derive_without_numerical_audit_using_rules
    (I : Interpretation Node)
    (E : HeadlineExternalFacts I)
    (R : DerivedRules graph I) :
    ∀ n, n ≠ .sp6NumericalAudit → I.claim n := by
  intro n hn
  induction n using (measure graph.rank).wf.induction with
  | h n ih =>
      by_cases hderived : graph.kind n = NodeKind.derived
      · apply R.prove n hderived
        intro d hd
        have hdne : d ≠ Node.sp6NumericalAudit := by
          intro hdc
          subst d
          exact sp6NumericalAudit_not_a_dependency n hd
        exact ih d (graph.dependencies_lower hd) hdne
      · exact E.prove n hderived hn

/-- Dependency induction for every node other than the isolated numerical
audit.  The three even-field transport nodes, `.evenFieldFixed`, and
`.evenUnipotentCorrespondence` are always intercepted by their explicit
realisations before the unrestricted residual rules are consulted. -/
theorem derive_without_numerical_audit
    (I : Interpretation Node)
    (E : HeadlineExternalFacts I)
    (R : DerivedRules graph I)
    (T : EvenFieldTransportRealisation I)
    (F : EvenFieldFixedRealisation I)
    (U : EvenUnipotentCorrespondenceRealisation I) :
    ∀ n, n ≠ .sp6NumericalAudit → I.claim n :=
  derive_without_numerical_audit_using_rules I E
    (rulesWithRealisedEvenFieldTransport I R T F U)

/-- The arithmetic interface for the final eight-way case division.  It does
not encode that an odd `q` is a prime power or that `ell` divides the relevant
group order.  Those group-theoretic restrictions belong to the semantic
realisation of `Goal`, not to this finite case split. -/
def AdmissibleParameters (n q ell p f : ℕ) : Prop :=
  2 ≤ n ∧ 2 ≤ q ∧ ¬ (n = 2 ∧ q = 2) ∧ Nat.Prime ell ∧
    (Odd q ∨ (p = 2 ∧ q = 2 ^ f ∧ 0 < f)) ∧
    (n = 3 → q = 2 → ell ≠ p → ell = 3 ∨ ell = 5 ∨ ell = 7)

/-- Meaning assigned to the eight branch nodes in the final proof.  These
maps state how an audited node is instantiated in the parameterised theorem;
they do not assert any branch result without its node claim. -/
structure BranchRealisation
    (I : Interpretation Node)
    (Goal : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) where
  rankTwo : I.claim .rankTwo →
    ∀ n q ell p f, n = 2 → 2 < q → Goal n q ell p f
  definingPrime : I.claim .spathDefiningCharacteristic →
    ∀ n q ell p f, 3 ≤ n → ell = p → Goal n q ell p f
  oddFieldAtTwo : I.claim .oddTwo →
    ∀ n q ell p f, 3 ≤ n → Odd q → ell = 2 → Goal n q ell p f
  oddFieldOddPrime : I.claim .oddConlon →
    ∀ n q ell p f,
      3 ≤ n → Odd q → ell ≠ p → Odd ell → Goal n q ell p f
  sp6AtFiveOrSeven : I.claim .sp6FiveOrSeven →
    ∀ n q ell p f,
      n = 3 → q = 2 → (ell = 5 ∨ ell = 7) → Goal n q ell p f
  sp6AtThree : I.claim .schaefferFrySp6AtThree →
    ∀ n q ell p f, n = 3 → q = 2 → ell = 3 → Goal n q ell p f
  evenFieldRankThree : I.claim .schaefferFryLowRankEvenField →
    ∀ n q ell p f,
      n = 3 → p = 2 → q = 2 ^ f → 2 ≤ f → Odd ell → Goal n q ell p f
  evenFieldHigherRank : I.claim .evenBridge →
    ∀ n q ell p f,
      4 ≤ n → p = 2 → q = 2 ^ f → 0 < f → Odd ell → Goal n q ell p f

/-- The semantic map from the parameterised theorem to the abstract headline
node.  It does not assume either form of the headline. -/
structure HeadlineRealisation
    (I : Interpretation Node)
    (Goal : ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    extends BranchRealisation I Goal where
  principalExclusion : PrincipalExclusionRealisation I
  evenFieldTransport : EvenFieldTransportRealisation I
  evenFieldFixed : EvenFieldFixedRealisation I
  evenUnipotentCorrespondence :
    EvenUnipotentCorrespondenceRealisation I
  headline_of :
    (∀ n q ell p f, AdmissibleParameters n q ell p f → Goal n q ell p f) →
      I.claim .symplectic

/-- Machine-checked construction of the eight realised branch claims. -/
theorem branchwise_symplectic
    (I : Interpretation Node)
    (E : HeadlineExternalFacts I)
    (R : DerivedRules graph I)
    (Goal : ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (B : BranchRealisation I Goal)
    (P : PrincipalExclusionRealisation I)
    (T : EvenFieldTransportRealisation I)
    (F : EvenFieldFixedRealisation I)
    (U : EvenUnipotentCorrespondenceRealisation I)
    (n q ell p f : ℕ)
    (h : AdmissibleParameters n q ell p f) : Goal n q ell p f := by
  rcases h with ⟨hn, hq, hsimple, hellPrime, hfield, hsp6⟩
  have hall := derive_without_numerical_audit I E
    (rulesWithRealisedPrincipalExclusion I R P) T F U
  let branches : DependencyCases.TypeCBranchResults Goal :=
    { rankTwo := B.rankTwo (hall .rankTwo (by decide))
      definingPrime :=
        B.definingPrime (hall .spathDefiningCharacteristic (by decide))
      oddFieldAtTwo := B.oddFieldAtTwo (hall .oddTwo (by decide))
      oddFieldOddPrime := B.oddFieldOddPrime (hall .oddConlon (by decide))
      sp6AtFiveOrSeven :=
        B.sp6AtFiveOrSeven (hall .sp6FiveOrSeven (by decide))
      sp6AtThree :=
        B.sp6AtThree (hall .schaefferFrySp6AtThree (by decide))
      evenFieldRankThree :=
        B.evenFieldRankThree
          (hall .schaefferFryLowRankEvenField (by decide))
      evenFieldHigherRank :=
        B.evenFieldHigherRank (hall .evenBridge (by decide)) }
  exact DependencyCases.typeC_of_branch_results Goal branches
    n q ell p f hn hq hsimple hellPrime hfield hsp6

/-- The parameterised branch construction, followed by the explicit semantic map
in `HeadlineRealisation`, proves the claim assigned to the headline node. -/
theorem conditional_symplectic_node
    (I : Interpretation Node)
    (E : HeadlineExternalFacts I)
    (R : DerivedRules graph I)
    (Goal : ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (H : HeadlineRealisation I Goal) : I.claim .symplectic := by
  apply H.headline_of
  intro n q ell p f h
  exact branchwise_symplectic I E R Goal H.toBranchRealisation
    H.principalExclusion H.evenFieldTransport H.evenFieldFixed
      H.evenUnipotentCorrespondence n q ell p f h

/-- Pointwise form of the branch construction. -/
theorem conditional_symplectic
    (I : Interpretation Node)
    (E : HeadlineExternalFacts I)
    (R : DerivedRules graph I)
    (Goal : ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (H : HeadlineRealisation I Goal)
    (n q ell p f : ℕ)
    (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hsimple : ¬ (n = 2 ∧ q = 2))
    (hellPrime : Nat.Prime ell)
    (hfield : Odd q ∨ (p = 2 ∧ q = 2 ^ f ∧ 0 < f))
    (hsp6 : n = 3 → q = 2 → ell ≠ p →
      ell = 3 ∨ ell = 5 ∨ ell = 7) :
    Goal n q ell p f := by
  exact branchwise_symplectic I E R Goal H.toBranchRealisation
    H.principalExclusion H.evenFieldTransport H.evenFieldFixed
      H.evenUnipotentCorrespondence n q ell p f
      ⟨hn, hq, hsimple, hellPrime, hfield, hsp6⟩

/-- Pure graph derivation of the abstract `.symplectic` claim.  Unlike
`conditional_symplectic_node`, this theorem does not by itself identify that
claim with the parameterised group-theoretic statement. -/
theorem graph_derives_symplectic_node
    (I : Interpretation Node)
    (E : HeadlineExternalFacts I)
    (R : DerivedRules graph I)
    (T : EvenFieldTransportRealisation I)
    (F : EvenFieldFixedRealisation I)
    (U : EvenUnipotentCorrespondenceRealisation I) : I.claim .symplectic :=
  derive_without_numerical_audit I E R T F U .symplectic (by decide)

end Formalisation.TypeCDependencies


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
