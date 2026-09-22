import Formalisation.DependencyGraph
import Formalisation.DependencyCases
import Formalisation.SporadicPrimeArithmetic

/-!
# Dependency certificate for the sporadic section

This module records the dependency audit of every named result in the manuscript's sporadic
section.  Cited results, the four GAP transcripts used in that section, and semantic bridges
which are not formalised in Mathlib are explicit leaves.  Every dependency edge strictly
lowers `rank`, so the resulting graph is acyclic by construction.

The computation represented by `fi24WeightsTranscript` enumerates every class fusion allowed
by the character tables, requires the induced central character of each selected local
character to determine a unique global block, and checks that the resulting distributions do
not depend on the fusion.  Two group-theoretic inputs remain external: the cited exhaustion of
the radical `5`-subgroups and the identification of the named character tables with their
normalisers.  The central character criterion for block induction is also kept as a cited
input rather than hidden in the transcript.

The final theorems are conditional dependency certificates.  They do not prove any cited
character theory, validate CTblLib or AtlasRep data, replay a GAP transcript, or constitute a
Lean proof of the sporadic iBAW theorem.  The forty-five-pair census is different: its finite
arithmetic is checked below and is passed to the final construction through an explicit one-way
realisation map.  Identifying the factored orders with the orders of the four sporadic groups
remains part of the Atlas input to that map.
-/

namespace Formalisation.SporadicDependencies

open DependencyGraph

/-- External inputs, intermediate case conclusions, and all seven named results in the
sporadic section. -/
inductive Node where
  -- The verification used for the complementary twenty-two groups.
  | ctBlocksOverview
  -- General structural and inductive-condition inputs.
  | atlasCoverOuterAndPrimeData
  | spathCyclicDefectIBAW
  | spathSylowTwoIBAW
  | spathAWCGoodUpgrade
  | defectZeroNormalisation
  | blockWeightSectorCompatibility
  | trivialOuterExtensions
  | trivialOuterIntermediateBlocks
  | centralQuotientTrivialSector
  | cyclicExtensionCohomology
  | anDietrichStabiliserIdentification
  -- An--Dietrich data and its correction.
  | anDietrichAWCGoodFamilies
  | anDietrichOuterInversion
  | anDietrichCorrectedTableEight
  | anDietrichBabyWeightTotal
  | anDietrichMonsterWeightTotal
  -- The defect-four lemma.
  | defectFourClassification
  | huZhouCaseThreeInertial
  | huZhouInertialBlockIBAW
  | zhangZhouHyperfocalDichotomy
  | nilpotentBlockIsInertial
  | zhangZhouKleinFourIBAW
  -- Group-specific cited results.
  | j4NoncyclicBlockAWC
  | fi24TwoRadicalClassification
  | fi24TwoBlockData
  | fi24ThreeBlockData
  | fi24NoncyclicBlockAWC
  | sambaleDefectAtMostFourAWC
  | navarroRestrictionRank
  | navarroRegularClassCount
  | babyOrdinaryTableVerification
  | babyOddBlockClassification
  | babyOddBlockAWC
  | monsterOrdinaryTableVerification
  | monsterOddBlockClassification
  | monsterOddBlockAWC
  | monsterOrderFormula
  -- The four independent GAP transcripts used in the sporadic proof.
  | fi24BlocksTranscript
  | fi24WeightsTranscript
  | babyTranscript
  | monsterTranscript
  -- Semantic interpretation of the Fi'24 computations.
  | fi24P2LocalBlockInduction
  | fi24P5RadicalClassExhaustion
  | fi24P5NormaliserIdentification
  | blockInductionCentralCharacterCriterion
  -- The five named lemmas in the sporadic section.
  | lemCompleteCollapse
  | lemDefectFourBlocks
  | lemBlockCancellation
  | lemEquivariantReplacement
  | lemCentralSectors
  -- The explicit prime census in the boundary proposition.
  | boundaryPrimeCensus
  -- Intermediate group and prime branches in the boundary proposition.
  | caseJ4
  | fi24AtTwo
  | fi24AtThree
  | fi24AtFive
  | fi24AtSeven
  | fi24AtLargerPrimes
  | caseFi24
  | babyAtTwo
  | babyAtOddPrimes
  | caseBaby
  | monsterAtTwo
  | monsterAtOddPrimes
  | caseMonster
  -- The proposition and theorem named in the sporadic section.
  | propFourBoundary
  | thmSporadic
  deriving DecidableEq, Repr

/-- Provenance classification.  The four computation leaves correspond one-for-one to
`fi24blocks.out`, `fi24weights.out`, `baby.out`, and `monster.out`. -/
def kind : Node → NodeKind
  | .fi24BlocksTranscript
  | .fi24WeightsTranscript
  | .babyTranscript
  | .monsterTranscript => .computation
  | .defectZeroNormalisation
  | .blockWeightSectorCompatibility
  | .trivialOuterExtensions
  | .trivialOuterIntermediateBlocks
  | .centralQuotientTrivialSector
  | .cyclicExtensionCohomology
  | .anDietrichStabiliserIdentification
  | .fi24P2LocalBlockInduction => .semanticBridge
  | .lemCompleteCollapse
  | .lemDefectFourBlocks
  | .lemBlockCancellation
  | .lemEquivariantReplacement
  | .lemCentralSectors
  | .boundaryPrimeCensus
  | .caseJ4
  | .fi24AtTwo
  | .fi24AtThree
  | .fi24AtFive
  | .fi24AtSeven
  | .fi24AtLargerPrimes
  | .caseFi24
  | .babyAtTwo
  | .babyAtOddPrimes
  | .caseBaby
  | .monsterAtTwo
  | .monsterAtOddPrimes
  | .caseMonster
  | .propFourBoundary
  | .thmSporadic => .derived
  | _ => .cited

/-- Immediate dependencies obtained from the proof, citation, and program audit. -/
def dependencies : Node → List Node
  | .lemCompleteCollapse =>
      [.defectZeroNormalisation, .blockWeightSectorCompatibility,
       .trivialOuterExtensions, .trivialOuterIntermediateBlocks]
  | .lemDefectFourBlocks =>
      [.defectFourClassification, .spathSylowTwoIBAW,
       .huZhouCaseThreeInertial, .huZhouInertialBlockIBAW,
       .zhangZhouHyperfocalDichotomy, .nilpotentBlockIsInertial,
       .zhangZhouKleinFourIBAW]
  | .lemBlockCancellation => []
  | .lemEquivariantReplacement =>
      [.anDietrichAWCGoodFamilies, .anDietrichOuterInversion,
       .cyclicExtensionCohomology, .anDietrichStabiliserIdentification]
  | .lemCentralSectors =>
      [.blockWeightSectorCompatibility]
  | .boundaryPrimeCensus =>
      [.atlasCoverOuterAndPrimeData]
  | .caseJ4 =>
      [.atlasCoverOuterAndPrimeData, .j4NoncyclicBlockAWC,
       .spathCyclicDefectIBAW, .lemCompleteCollapse]
  | .fi24AtTwo =>
      [.atlasCoverOuterAndPrimeData, .centralQuotientTrivialSector,
       .anDietrichAWCGoodFamilies, .anDietrichCorrectedTableEight,
       .fi24BlocksTranscript, .fi24TwoRadicalClassification,
       .fi24TwoBlockData,
       .sambaleDefectAtMostFourAWC, .fi24P2LocalBlockInduction,
       .lemDefectFourBlocks, .lemBlockCancellation]
  | .fi24AtThree =>
      [.atlasCoverOuterAndPrimeData, .anDietrichAWCGoodFamilies,
       .anDietrichCorrectedTableEight, .fi24BlocksTranscript,
       .fi24ThreeBlockData, .fi24NoncyclicBlockAWC,
       .defectZeroNormalisation, .lemBlockCancellation]
  | .fi24AtFive =>
      [.atlasCoverOuterAndPrimeData, .centralQuotientTrivialSector,
       .fi24BlocksTranscript, .fi24WeightsTranscript,
       .fi24P5RadicalClassExhaustion, .fi24P5NormaliserIdentification,
       .blockInductionCentralCharacterCriterion,
       .spathCyclicDefectIBAW]
  | .fi24AtSeven =>
      [.atlasCoverOuterAndPrimeData, .centralQuotientTrivialSector,
       .anDietrichAWCGoodFamilies, .anDietrichCorrectedTableEight,
       .fi24BlocksTranscript, .spathCyclicDefectIBAW,
       .defectZeroNormalisation, .lemBlockCancellation]
  | .fi24AtLargerPrimes =>
      [.atlasCoverOuterAndPrimeData, .fi24BlocksTranscript,
       .spathCyclicDefectIBAW]
  | .caseFi24 =>
      [.atlasCoverOuterAndPrimeData, .fi24AtTwo, .fi24AtThree,
       .fi24AtFive, .fi24AtSeven, .fi24AtLargerPrimes,
       .lemEquivariantReplacement, .spathAWCGoodUpgrade,
       .lemCentralSectors]
  | .babyAtTwo =>
      [.atlasCoverOuterAndPrimeData, .babyOrdinaryTableVerification,
       .babyTranscript, .navarroRestrictionRank,
       .anDietrichBabyWeightTotal, .sambaleDefectAtMostFourAWC,
       .lemCompleteCollapse]
  | .babyAtOddPrimes =>
      [.atlasCoverOuterAndPrimeData, .babyTranscript,
       .babyOddBlockClassification, .babyOddBlockAWC,
       .spathCyclicDefectIBAW, .lemCompleteCollapse]
  | .caseBaby =>
      [.atlasCoverOuterAndPrimeData, .babyAtTwo, .babyAtOddPrimes]
  | .monsterAtTwo =>
      [.atlasCoverOuterAndPrimeData, .monsterOrdinaryTableVerification,
       .monsterTranscript, .navarroRegularClassCount,
       .anDietrichMonsterWeightTotal, .sambaleDefectAtMostFourAWC,
       .defectZeroNormalisation, .lemCompleteCollapse]
  | .monsterAtOddPrimes =>
      [.atlasCoverOuterAndPrimeData, .monsterOddBlockClassification,
       .monsterOddBlockAWC, .monsterOrderFormula,
       .spathCyclicDefectIBAW, .lemCompleteCollapse]
  | .caseMonster =>
      [.atlasCoverOuterAndPrimeData, .monsterAtTwo, .monsterAtOddPrimes]
  | .propFourBoundary =>
      [.boundaryPrimeCensus, .caseJ4, .caseFi24, .caseBaby, .caseMonster]
  | .thmSporadic =>
      [.ctBlocksOverview, .propFourBoundary]
  | _ => []

/-- Natural-number ranks certifying that every dependency precedes its consumer. -/
def rank : Node → ℕ
  | .lemCompleteCollapse
  | .lemDefectFourBlocks
  | .lemBlockCancellation
  | .lemEquivariantReplacement
  | .lemCentralSectors
  | .boundaryPrimeCensus => 1
  | .caseJ4
  | .fi24AtTwo
  | .fi24AtThree
  | .fi24AtFive
  | .fi24AtSeven
  | .fi24AtLargerPrimes
  | .babyAtTwo
  | .babyAtOddPrimes
  | .monsterAtTwo
  | .monsterAtOddPrimes => 2
  | .caseFi24
  | .caseBaby
  | .caseMonster => 3
  | .propFourBoundary => 4
  | .thmSporadic => 5
  | _ => 0

/-- The machine-checked dependency graph for the sporadic section. -/
def graph : Graph Node where
  kind := kind
  dependencies := dependencies
  rank := rank
  dependencies_lower := by
    intro n d hd
    cases n <;> cases d <;> simp [dependencies, rank] at hd ⊢
  external_has_no_dependencies := by
    intro n hn
    cases n <;> simp [kind, dependencies] at hn ⊢

/-- The seven theorem-like environments named in the sporadic section. -/
def namedResults : List Node :=
  [.lemCompleteCollapse, .lemDefectFourBlocks, .lemBlockCancellation,
   .lemEquivariantReplacement, .lemCentralSectors,
   .propFourBoundary, .thmSporadic]

/-- The four transcript leaves used by the sporadic proof. -/
def computationLeaves : List Node :=
  [.fi24BlocksTranscript, .fi24WeightsTranscript,
   .babyTranscript, .monsterTranscript]

theorem length_namedResults : namedResults.length = 7 := by decide

theorem namedResults_nodup : namedResults.Nodup := by decide

theorem length_computationLeaves : computationLeaves.length = 4 := by decide

theorem computationLeaves_nodup : computationLeaves.Nodup := by decide

/-- The ten primes displayed for `J₄`. -/
def j4Primes : List ℕ := [2, 3, 5, 7, 11, 23, 29, 31, 37, 43]

/-- The nine primes displayed for `Fi'₂₄`. -/
def fi24Primes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 23, 29]

/-- The eleven primes displayed for the Baby Monster. -/
def babyPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47]

/-- The fifteen primes displayed for the Monster. -/
def monsterPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

/-- The forty-five group-prime pairs displayed in the boundary proposition. -/
def boundaryPairs : List (DependencyCases.SporadicGroup × ℕ) :=
  j4Primes.map (fun ell => (DependencyCases.SporadicGroup.J4, ell)) ++
  fi24Primes.map (fun ell => (DependencyCases.SporadicGroup.Fi24Prime, ell)) ++
  babyPrimes.map (fun ell => (DependencyCases.SporadicGroup.Baby, ell)) ++
  monsterPrimes.map (fun ell => (DependencyCases.SporadicGroup.Monster, ell))

theorem boundary_prime_list_lengths :
    j4Primes.length = 10 ∧ fi24Primes.length = 9 ∧
    babyPrimes.length = 11 ∧ monsterPrimes.length = 15 := by
  decide

theorem boundary_prime_count : boundaryPairs.length = 45 := by
  decide

theorem j4Primes_nodup : j4Primes.Nodup := by decide

theorem fi24Primes_nodup : fi24Primes.Nodup := by decide

theorem babyPrimes_nodup : babyPrimes.Nodup := by decide

theorem monsterPrimes_nodup : monsterPrimes.Nodup := by decide

/-- No group-prime pair occurs twice in the displayed boundary list. -/
theorem boundaryPairs_nodup : boundaryPairs.Nodup := by decide

/-- Every integer in the displayed boundary list is prime. -/
theorem boundaryPairs_second_prime :
    ∀ x ∈ boundaryPairs, Nat.Prime x.2 := by
  decide

/-- The first coordinates in the displayed list are exactly the four boundary groups. -/
theorem boundaryPairs_group_support :
    (boundaryPairs.map Prod.fst).toFinset = DependencyCases.BoundaryFour := by
  decide

/-- The displayed prime lists agree with the prime supports of the standard
factorised order expressions.  Identifying those expressions with the orders
of the named groups remains the Atlas input `atlasCoverOuterAndPrimeData`. -/
theorem displayed_prime_supports_match_factored_orders :
    j4Primes.toFinset = SporadicPrimeArithmetic.j4PrimeSupport ∧
    fi24Primes.toFinset = SporadicPrimeArithmetic.fi24PrimeSupport ∧
    babyPrimes.toFinset = SporadicPrimeArithmetic.babyPrimeSupport ∧
    monsterPrimes.toFinset = SporadicPrimeArithmetic.monsterPrimeSupport := by
  decide

theorem displayed_primes_are_exact_for_factored_orders
    {p : ℕ} (hp : p.Prime) :
    (p ∣ SporadicPrimeArithmetic.j4Order ↔ p ∈ j4Primes) ∧
    (p ∣ SporadicPrimeArithmetic.fi24Order ↔ p ∈ fi24Primes) ∧
    (p ∣ SporadicPrimeArithmetic.babyOrder ↔ p ∈ babyPrimes) ∧
    (p ∣ SporadicPrimeArithmetic.monsterOrder ↔ p ∈ monsterPrimes) := by
  rw [SporadicPrimeArithmetic.prime_dvd_j4Order_iff hp,
    SporadicPrimeArithmetic.prime_dvd_fi24Order_iff hp,
    SporadicPrimeArithmetic.prime_dvd_babyOrder_iff hp,
    SporadicPrimeArithmetic.prime_dvd_monsterOrder_iff hp]
  simp [j4Primes, fi24Primes, babyPrimes, monsterPrimes,
    SporadicPrimeArithmetic.j4PrimeSupport,
    SporadicPrimeArithmetic.fi24PrimeSupport,
    SporadicPrimeArithmetic.babyPrimeSupport,
    SporadicPrimeArithmetic.monsterPrimeSupport]

/-- The kernel-checked finite information used in the boundary-prime census.
This certificate concerns the displayed lists and the standard factored-order
expressions only; it does not identify those expressions with group orders. -/
structure BoundaryArithmeticCertificate where
  primeListLengths :
    j4Primes.length = 10 ∧ fi24Primes.length = 9 ∧
      babyPrimes.length = 11 ∧ monsterPrimes.length = 15
  pairCount : boundaryPairs.length = 45
  pairNodup : boundaryPairs.Nodup
  pairPrimes : ∀ x ∈ boundaryPairs, Nat.Prime x.2
  groupSupport :
    (boundaryPairs.map Prod.fst).toFinset = DependencyCases.BoundaryFour
  exactFactoredOrders : ∀ {p : ℕ}, p.Prime →
    (p ∣ SporadicPrimeArithmetic.j4Order ↔ p ∈ j4Primes) ∧
      (p ∣ SporadicPrimeArithmetic.fi24Order ↔ p ∈ fi24Primes) ∧
      (p ∣ SporadicPrimeArithmetic.babyOrder ↔ p ∈ babyPrimes) ∧
      (p ∣ SporadicPrimeArithmetic.monsterOrder ↔ p ∈ monsterPrimes)

/-- The complete finite certificate proved above. -/
theorem boundaryArithmeticCertificate : BoundaryArithmeticCertificate where
  primeListLengths := boundary_prime_list_lengths
  pairCount := boundary_prime_count
  pairNodup := boundaryPairs_nodup
  pairPrimes := boundaryPairs_second_prime
  groupSupport := boundaryPairs_group_support
  exactFactoredOrders := displayed_primes_are_exact_for_factored_orders

theorem dependency_rank_decreases {n d : Node}
    (h : d ∈ dependencies n) : rank d < rank n :=
  graph.dependencies_lower h

theorem dependency_graph_is_irreflexive (n : Node) :
    n ∉ dependencies n :=
  graph.not_mem_own_dependencies n

theorem dependency_graph_has_no_two_cycle {n d : Node}
    (h : d ∈ dependencies n) : n ∉ dependencies d :=
  graph.no_two_cycle h

/-- The order `5` and order `25` transcript is accompanied by the exact external facts that
turn its exhaustive fusion calculation into a group-theoretic block statement. -/
theorem fi24_at_five_exposes_source_inputs :
    Node.fi24WeightsTranscript ∈ dependencies .fi24AtFive ∧
    Node.fi24P5RadicalClassExhaustion ∈ dependencies .fi24AtFive ∧
    Node.fi24P5NormaliserIdentification ∈ dependencies .fi24AtFive ∧
    Node.blockInductionCentralCharacterCriterion ∈ dependencies .fi24AtFive := by
  decide

/-- The syntactic forty-five-pair census is an explicit input to the four-group proposition
rather than an unstated case split. -/
theorem boundary_prime_census_is_four_boundary_input :
    Node.boundaryPrimeCensus ∈ dependencies .propFourBoundary := by
  decide

/-- All exact external leaves, together with proof rules respecting the displayed edges,
conditionally derive the four-group proposition. -/
theorem four_boundary_node_of_exact_external_leaves
    (I : Interpretation Node)
    (hLeaves : ∀ n, kind n ≠ .derived → I.claim n)
    (rules : DerivedRules graph I) :
    I.claim .propFourBoundary := by
  let facts : ExternalFacts graph I :=
    { prove := hLeaves }
  exact graph.derive_all I facts rules .propFourBoundary

/-- The same graph conditionally derives its node for the twenty-six-group headline. -/
theorem sporadic_node_of_exact_external_leaves
    (I : Interpretation Node)
    (hLeaves : ∀ n, kind n ≠ .derived → I.claim n)
    (rules : DerivedRules graph I) :
    I.claim .thmSporadic := by
  let facts : ExternalFacts graph I :=
    { prove := hLeaves }
  exact graph.derive_all I facts rules .thmSporadic

/-- Interpretation of the CTBlocks leaf and the four-group proposition as the two branches in
`DependencyCases.sporadic_of_twenty_two_and_four`. -/
structure SporadicRealisation
    (I : Interpretation Node)
    (Goal : DependencyCases.SporadicGroup → Prop) where
  boundaryCensus : I.claim .atlasCoverOuterAndPrimeData →
    BoundaryArithmeticCertificate → I.claim .boundaryPrimeCensus
  ctBlocks : I.claim .ctBlocksOverview →
    ∀ S, S ∈ DependencyCases.CTBlocksTwentyTwo → Goal S
  boundary : I.claim .propFourBoundary →
    ∀ S, S ∈ DependencyCases.BoundaryFour → Goal S

/-- Replace the unrestricted proof rule for the boundary census by the
checked finite certificate and its explicit Atlas realisation. -/
theorem rulesWithRealisedBoundaryCensus
    (I : Interpretation Node)
    (rules : DerivedRules graph I)
    (Goal : DependencyCases.SporadicGroup → Prop)
    (R : SporadicRealisation I Goal) : DerivedRules graph I where
  prove n hn hdeps := by
    by_cases h : n = .boundaryPrimeCensus
    · subst n
      exact R.boundaryCensus
        (hdeps .atlasCoverOuterAndPrimeData (by decide))
        boundaryArithmeticCertificate
    · exact rules.prove n hn hdeps

/-- Conditional derivation of the manuscript's four-group proposition with its intended
group-theoretic interpretation. -/
theorem conditional_four_boundary
    (I : Interpretation Node)
    (hLeaves : ∀ n, kind n ≠ .derived → I.claim n)
    (rules : DerivedRules graph I)
    (Goal : DependencyCases.SporadicGroup → Prop)
    (R : SporadicRealisation I Goal) :
    ∀ S, S ∈ DependencyCases.BoundaryFour → Goal S :=
  R.boundary (four_boundary_node_of_exact_external_leaves I hLeaves
    (rulesWithRealisedBoundaryCensus I rules Goal R))

/-- Conditional construction of the twenty-two CTBlocks cases and the four manuscript cases.
The final coverage step is the formally checked theorem in `DependencyCases`. -/
theorem conditional_sporadic
    (I : Interpretation Node)
    (hLeaves : ∀ n, kind n ≠ .derived → I.claim n)
    (rules : DerivedRules graph I)
    (Goal : DependencyCases.SporadicGroup → Prop)
    (R : SporadicRealisation I Goal)
    (S : DependencyCases.SporadicGroup) : Goal S := by
  let facts : ExternalFacts graph I :=
    { prove := hLeaves }
  let realisedRules := rulesWithRealisedBoundaryCensus I rules Goal R
  have hCTBlocks : I.claim .ctBlocksOverview :=
    graph.derive_all I facts realisedRules .ctBlocksOverview
  have hBoundary : I.claim .propFourBoundary :=
    graph.derive_all I facts realisedRules .propFourBoundary
  exact DependencyCases.sporadic_of_twenty_two_and_four Goal
    (R.ctBlocks hCTBlocks) (R.boundary hBoundary) S

end Formalisation.SporadicDependencies


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
