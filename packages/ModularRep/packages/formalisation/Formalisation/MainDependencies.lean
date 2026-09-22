import Formalisation.PreliminaryDependencies
import Formalisation.ReductionLogic
import Formalisation.TypeCDependencies
import Formalisation.TypeBDependencies
import Formalisation.SporadicDependencies

/-!
# Conditional construction of the manuscript's headline results

The section dependency modules use different node types and, in a few places,
duplicate a preliminary or type `C` result under a section-specific name.
This file does not identify such claims by fiat.  `PreliminaryLinks` states
the required semantic maps explicitly, and `ResidualExternalFacts` contains
only the remaining external leaves.

Theorem 1.1 uses the odd-characteristic, rank-at-least-three type `B` theorem
(`thmTypeB`).  Corollary 1.2 concerns all finite simple groups of type `B`, so
its proof must instead use the census corollary (`corTypeBCensus`).

The parameterised conclusions below are combined with the checked case-split
theorems in `DependencyCases`.  Literature results, computation transcripts,
semantic links between ledgers, and the proof rules for the named manuscript
results remain explicit assumptions.  In particular, this is a conditional
dependency certificate, not a formalisation of the cited character theory.
-/

namespace Formalisation.MainDependencies

open Formalisation.DependencyGraph

/-- The three families in Theorem 1.1, in manuscript order. -/
inductive MainFamily where
  | typeC
  | typeB
  | sporadic
  deriving DecidableEq, Repr

/-- Section-specific formulations of the three conclusions.  The type `B`
predicate may close over the fixed odd prime power occurring in that section. -/
structure SectionGoals where
  typeC : ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  typeB : ℕ → ℕ → ℕ → Prop
  sporadic : DependencyCases.SporadicGroup → Prop

/-- The arithmetic domain checked by the type `C` case construction.  Prime-power
and group-order divisibility hypotheses are left to the semantic realisation
of `Goal`; they are not represented by this finite split. -/
def TypeCConclusion (Goal : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ n q ell p f, 2 ≤ n → 2 ≤ q → ¬ (n = 2 ∧ q = 2) →
    Nat.Prime ell →
    (Odd q ∨ (p = 2 ∧ q = 2 ^ f ∧ 0 < f)) →
    (n = 3 → q = 2 → ell ≠ p → ell = 3 ∨ ell = 5 ∨ ell = 7) →
    Goal n q ell p f

/-- The rank and prime split used in the odd-characteristic type `B` theorem. -/
def TypeBConclusion (Goal : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ n ell p, 3 ≤ n → Nat.Prime ell → Goal n ell p

/-- The twenty-six-group conclusion checked by the sporadic case construction. -/
def SporadicConclusion (Goal : DependencyCases.SporadicGroup → Prop) : Prop :=
  ∀ S, Goal S

/-- The four type `B` branch nodes interpreted in the parameterised theorem.
This is the type `B` counterpart of `TypeCDependencies.BranchRealisation`. -/
structure TypeBBranchRealisation
    (I : Interpretation TypeBDependencies.Node)
    (Goal : ℕ → ℕ → ℕ → Prop) where
  definingPrime : I.claim .propDefiningPrime →
    ∀ n ell p, ell = p → Goal n ell p
  oddNondefining : I.claim .propOddNondefining →
    ∀ n ell p, ell ≠ p → Odd ell → Goal n ell p
  atTwoRankThree : I.claim .propTwoRankThree →
    ∀ n ell p, ell = 2 → n = 3 → Goal n ell p
  atTwoHigherRank : I.claim .propTwoHighRank →
    ∀ n ell p, ell = 2 → 4 ≤ n → Goal n ell p

/-- Explicit semantic maps from Section 2 and type `C` claims to the
differently typed section ledgers.  These fields are assumptions because the
interpretations of the ledgers are independent; they are not definitional
equalities.

The Conlon and cyclic-extension fields also account for section nodes whose
names package the precise specialisation of the corresponding preliminary
result used later. -/
structure PreliminaryLinks
    (IP : Interpretation PreliminaryDependencies.Node)
    (IC : Interpretation TypeCDependencies.Node)
    (IB : Interpretation TypeBDependencies.Node)
    (IS : Interpretation SporadicDependencies.Node) where
  typeC : TypeCDependencies.PreliminaryRealisation IC IP
  typeBBlockAggregation : IP.claim .blockOrbitAggregation →
    IB.claim .blockAggregation
  typeBFixedPointDescent : IP.claim .fixedPointDescentCorollary →
    IB.claim .fixedPointDescent
  typeBConlonDetection : IP.claim .conlonMarkCorollary →
    IB.claim .conlonPermutationLatticeDetection
  typeBCyclicExtension : IP.claim .cyclicCharacterExtension →
    IB.claim .cyclicBrauerExtension
  typeBLocalRestriction : IP.claim .localIBAWRestriction →
    IB.claim .bawGoodImpliesInductiveBAW
  typeBOddTwoFactor : IC.claim .oddTwo →
    IB.claim .typeCOddTwoFactor
  typeCHeadline : IC.claim .symplectic →
    IB.claim .typeCHeadline
  sporadicSectorCompatibility : IP.claim .centralSectorCompatibility →
    IS.claim .blockWeightSectorCompatibility
  sporadicCyclicCohomology : IP.claim .cyclicCharacterExtension →
    IS.claim .cyclicExtensionCohomology

def typeBLinkedInputs : List TypeBDependencies.Node :=
  [.blockAggregation, .fixedPointDescent,
   .conlonPermutationLatticeDetection, .cyclicBrauerExtension,
   .bawGoodImpliesInductiveBAW, .typeCOddTwoFactor, .typeCHeadline]

def sporadicPreliminaryInputs : List SporadicDependencies.Node :=
  [.blockWeightSectorCompatibility, .cyclicExtensionCohomology]

/-- All external leaves other than those supplied through `PreliminaryLinks`.
The isolated type `C` numerical audit is not required by the headline proof. -/
structure ResidualExternalFacts
    (IC : Interpretation TypeCDependencies.Node)
    (IB : Interpretation TypeBDependencies.Node)
    (IS : Interpretation SporadicDependencies.Node) where
  typeC : TypeCDependencies.NonPreliminaryExternalFacts IC
  typeB : ∀ n, TypeBDependencies.kind n ≠ NodeKind.derived →
    n ∉ typeBLinkedInputs → IB.claim n
  sporadic : ∀ n, SporadicDependencies.kind n ≠ NodeKind.derived →
    n ∉ sporadicPreliminaryInputs → IS.claim n

/-- Combine the type `C` external facts after deriving Section 2. -/
theorem linkedTypeCFacts
    (IP : Interpretation PreliminaryDependencies.Node)
    (EP : ExternalFacts PreliminaryDependencies.graph IP)
    (RP : DerivedRules PreliminaryDependencies.graph IP)
    (IC : Interpretation TypeCDependencies.Node)
    {IB : Interpretation TypeBDependencies.Node}
    {IS : Interpretation SporadicDependencies.Node}
    (L : PreliminaryLinks IP IC IB IS)
    (E : ResidualExternalFacts IC IB IS) :
    TypeCDependencies.HeadlineExternalFacts IC :=
  TypeCDependencies.HeadlineExternalFacts.ofPreliminary
    IC IP EP RP L.typeC E.typeC

/-- Combine the type `B` external leaves after deriving Section 2 and the
linked type `C` claims. -/
theorem linkedTypeBFacts
    (IP : Interpretation PreliminaryDependencies.Node)
    (EP : ExternalFacts PreliminaryDependencies.graph IP)
    (RP : DerivedRules PreliminaryDependencies.graph IP)
    (IC : Interpretation TypeCDependencies.Node)
    (RC : DerivedRules TypeCDependencies.graph IC)
    (TC : TypeCDependencies.EvenFieldTransportRealisation IC)
    (FC : TypeCDependencies.EvenFieldFixedRealisation IC)
    (UC : TypeCDependencies.EvenUnipotentCorrespondenceRealisation IC)
    (IB : Interpretation TypeBDependencies.Node)
    {IS : Interpretation SporadicDependencies.Node}
    (L : PreliminaryLinks IP IC IB IS)
    (E : ResidualExternalFacts IC IB IS) :
    ∀ n, n ∈ TypeBDependencies.externalLeaves → IB.claim n := by
  have hP : ∀ m, IP.claim m :=
    PreliminaryDependencies.graph.derive_all IP EP RP
  have hC : ∀ m, m ≠ .sp6NumericalAudit → IC.claim m :=
    TypeCDependencies.derive_without_numerical_audit IC
      (linkedTypeCFacts IP EP RP IC L E) RC TC FC UC
  intro n hn
  have hkind : TypeBDependencies.kind n ≠ NodeKind.derived :=
    ((TypeBDependencies.mem_externalLeaves_iff n).1 hn).1
  by_cases h₁ : n = .blockAggregation
  · subst n
    exact L.typeBBlockAggregation (hP .blockOrbitAggregation)
  by_cases h₂ : n = .fixedPointDescent
  · subst n
    exact L.typeBFixedPointDescent (hP .fixedPointDescentCorollary)
  by_cases h₃ : n = .conlonPermutationLatticeDetection
  · subst n
    exact L.typeBConlonDetection (hP .conlonMarkCorollary)
  by_cases h₄ : n = .cyclicBrauerExtension
  · subst n
    exact L.typeBCyclicExtension (hP .cyclicCharacterExtension)
  by_cases h₅ : n = .bawGoodImpliesInductiveBAW
  · subst n
    exact L.typeBLocalRestriction (hP .localIBAWRestriction)
  by_cases h₆ : n = .typeCOddTwoFactor
  · subst n
    exact L.typeBOddTwoFactor (hC .oddTwo (by decide))
  by_cases h₇ : n = .typeCHeadline
  · subst n
    have hnot :=
      ((TypeBDependencies.mem_externalLeaves_iff .typeCHeadline).1 hn).2
    exact (hnot (by decide)).elim
  · exact E.typeB n hkind (by
      simp [typeBLinkedInputs, h₁, h₂, h₃, h₄, h₅, h₆, h₇])

/-- The analogous linked family including the four census-only leaves. -/
theorem linkedTypeBAllFacts
    (IP : Interpretation PreliminaryDependencies.Node)
    (EP : ExternalFacts PreliminaryDependencies.graph IP)
    (RP : DerivedRules PreliminaryDependencies.graph IP)
    (IC : Interpretation TypeCDependencies.Node)
    (RC : DerivedRules TypeCDependencies.graph IC)
    (TC : TypeCDependencies.EvenFieldTransportRealisation IC)
    (FC : TypeCDependencies.EvenFieldFixedRealisation IC)
    (UC : TypeCDependencies.EvenUnipotentCorrespondenceRealisation IC)
    (hTypeCHeadline : IC.claim .symplectic)
    (IB : Interpretation TypeBDependencies.Node)
    {IS : Interpretation SporadicDependencies.Node}
    (L : PreliminaryLinks IP IC IB IS)
    (E : ResidualExternalFacts IC IB IS) :
    ∀ n, n ∈ TypeBDependencies.allExternalLeaves → IB.claim n := by
  have hP : ∀ m, IP.claim m :=
    PreliminaryDependencies.graph.derive_all IP EP RP
  have hC : ∀ m, m ≠ .sp6NumericalAudit → IC.claim m :=
    TypeCDependencies.derive_without_numerical_audit IC
      (linkedTypeCFacts IP EP RP IC L E) RC TC FC UC
  intro n hn
  have hkind : TypeBDependencies.kind n ≠ NodeKind.derived :=
    (TypeBDependencies.mem_allExternalLeaves_iff n).1 hn
  by_cases h₁ : n = .blockAggregation
  · subst n
    exact L.typeBBlockAggregation (hP .blockOrbitAggregation)
  by_cases h₂ : n = .fixedPointDescent
  · subst n
    exact L.typeBFixedPointDescent (hP .fixedPointDescentCorollary)
  by_cases h₃ : n = .conlonPermutationLatticeDetection
  · subst n
    exact L.typeBConlonDetection (hP .conlonMarkCorollary)
  by_cases h₄ : n = .cyclicBrauerExtension
  · subst n
    exact L.typeBCyclicExtension (hP .cyclicCharacterExtension)
  by_cases h₅ : n = .bawGoodImpliesInductiveBAW
  · subst n
    exact L.typeBLocalRestriction (hP .localIBAWRestriction)
  by_cases h₆ : n = .typeCOddTwoFactor
  · subst n
    exact L.typeBOddTwoFactor (hC .oddTwo (by decide))
  by_cases h₇ : n = .typeCHeadline
  · subst n
    exact L.typeCHeadline hTypeCHeadline
  · exact E.typeB n hkind (by
      simp [typeBLinkedInputs, h₁, h₂, h₃, h₄, h₅, h₆, h₇])

/-- Combine the sporadic external leaves after deriving Section 2. -/
theorem linkedSporadicFacts
    (IP : Interpretation PreliminaryDependencies.Node)
    (EP : ExternalFacts PreliminaryDependencies.graph IP)
    (RP : DerivedRules PreliminaryDependencies.graph IP)
    (IS : Interpretation SporadicDependencies.Node)
    {IC : Interpretation TypeCDependencies.Node}
    {IB : Interpretation TypeBDependencies.Node}
    (L : PreliminaryLinks IP IC IB IS)
    (E : ResidualExternalFacts IC IB IS) :
    ∀ n, SporadicDependencies.kind n ≠ NodeKind.derived → IS.claim n := by
  have hP : ∀ m, IP.claim m :=
    PreliminaryDependencies.graph.derive_all IP EP RP
  intro n hn
  by_cases h₁ : n = .blockWeightSectorCompatibility
  · subst n
    exact L.sporadicSectorCompatibility (hP .centralSectorCompatibility)
  by_cases h₂ : n = .cyclicExtensionCohomology
  · subst n
    exact L.sporadicCyclicCohomology (hP .cyclicCharacterExtension)
  · exact E.sporadic n hn (by
      simp [sporadicPreliminaryInputs, h₁, h₂])

/-- Interpret the checked section conclusions as the three family-level
statements in Theorem 1.1. -/
structure HeadlineRealisation
    (IC : Interpretation TypeCDependencies.Node)
    (IB : Interpretation TypeBDependencies.Node)
    (IS : Interpretation SporadicDependencies.Node)
    (G : SectionGoals)
    (FamilyGoal : MainFamily → Prop) where
  typeCBranches : TypeCDependencies.HeadlineRealisation IC G.typeC
  typeBBranches : TypeBBranchRealisation IB G.typeB
  typeBHighRank : TypeBDependencies.HighRankInductionRealisation IB
  sporadicBranches : SporadicDependencies.SporadicRealisation IS G.sporadic
  typeC : TypeCConclusion G.typeC → FamilyGoal .typeC
  typeB : TypeBConclusion G.typeB → FamilyGoal .typeB
  sporadic : SporadicConclusion G.sporadic → FamilyGoal .sporadic

/-- Conditional form of Theorem 1.1.  Unlike the node-only certificate, this
theorem runs the checked eight-branch, four-branch, and twenty-two-plus-four
case assemblies before passing to the family-level statements. -/
theorem conditional_main
    (IP : Interpretation PreliminaryDependencies.Node)
    (EP : ExternalFacts PreliminaryDependencies.graph IP)
    (RP : DerivedRules PreliminaryDependencies.graph IP)
    (IC : Interpretation TypeCDependencies.Node)
    (RC : DerivedRules TypeCDependencies.graph IC)
    (IB : Interpretation TypeBDependencies.Node)
    (RB : DerivedRules TypeBDependencies.graph IB)
    (IS : Interpretation SporadicDependencies.Node)
    (RS : DerivedRules SporadicDependencies.graph IS)
    (L : PreliminaryLinks IP IC IB IS)
    (E : ResidualExternalFacts IC IB IS)
    (G : SectionGoals)
    (FamilyGoal : MainFamily → Prop)
    (H : HeadlineRealisation IC IB IS G FamilyGoal) :
    ∀ family, FamilyGoal family := by
  let EC := linkedTypeCFacts IP EP RP IC L E
  let RC' := TypeCDependencies.rulesWithRealisedPrincipalExclusion
    IC RC H.typeCBranches.principalExclusion
  have EB := linkedTypeBFacts IP EP RP IC RC'
    H.typeCBranches.evenFieldTransport H.typeCBranches.evenFieldFixed
      H.typeCBranches.evenUnipotentCorrespondence IB L E
  have ES := linkedSporadicFacts IP EP RP IS L E
  have hC : TypeCConclusion G.typeC := by
    intro n q ell p f hn hq hsimple hellPrime hfield hsp6
    exact TypeCDependencies.conditional_symplectic IC EC RC G.typeC
      H.typeCBranches n q ell p f hn hq hsimple hellPrime hfield hsp6
  have hBnodes : ∀ n, n ≠ .corTypeBCensus →
      n ∉ TypeBDependencies.censusOnlyExternalLeaves → IB.claim n :=
    TypeBDependencies.derive_without_census_inputs IB EB RB
  have hBHigh : IB.claim .propTwoHighRank :=
    TypeBDependencies.propTwoHighRank_of_external_leaves
      IB EB RB H.typeBHighRank
  have hB : TypeBConclusion G.typeB := by
    let branches : DependencyCases.TypeBBranchResults G.typeB :=
      { definingPrime := H.typeBBranches.definingPrime
          (hBnodes .propDefiningPrime (by decide) (by decide))
        oddNondefining := H.typeBBranches.oddNondefining
          (hBnodes .propOddNondefining (by decide) (by decide))
        atTwoRankThree := H.typeBBranches.atTwoRankThree
          (hBnodes .propTwoRankThree (by decide) (by decide))
        atTwoHigherRank := H.typeBBranches.atTwoHigherRank hBHigh }
    intro n ell p hn hellPrime
    exact DependencyCases.typeB_of_branch_results G.typeB branches
      n ell p hn hellPrime
  have hS : SporadicConclusion G.sporadic := by
    intro S
    exact SporadicDependencies.conditional_sporadic IS ES RS G.sporadic
      H.sporadicBranches S
  intro family
  cases family with
  | typeC => exact H.typeC hC
  | typeB => exact H.typeB hB
  | sporadic => exact H.sporadic hS

/-- Realisation needed for the finite group consequence.  The type `B` field
deliberately consumes the all-type-`B` census node, not `thmTypeB`. -/
structure ReductionRealisation
    (IC : Interpretation TypeCDependencies.Node)
    (IB : Interpretation TypeBDependencies.Node)
    (IS : Interpretation SporadicDependencies.Node)
    (G : SectionGoals)
    (FamilyGoal : MainFamily → Prop) where
  typeCBranches : TypeCDependencies.HeadlineRealisation IC G.typeC
  typeBBranches : TypeBBranchRealisation IB G.typeB
  typeBHighRank : TypeBDependencies.HighRankInductionRealisation IB
  sporadicBranches : SporadicDependencies.SporadicRealisation IS G.sporadic
  typeC : TypeCConclusion G.typeC → FamilyGoal .typeC
  typeBHeadline : TypeBConclusion G.typeB → IB.claim .thmTypeB
  typeB : IB.claim .corTypeBCensus → FamilyGoal .typeB
  sporadic : SporadicConclusion G.sporadic → FamilyGoal .sporadic

/-- Conditional form of Corollary 1.2.  The final implication represents
Späth's reduction theorem for the manuscript's involved-as-a-section
hypothesis.  The all-type-`B` premise is derived through `corTypeBCensus`. -/
theorem conditional_reduction
    (IP : Interpretation PreliminaryDependencies.Node)
    (EP : ExternalFacts PreliminaryDependencies.graph IP)
    (RP : DerivedRules PreliminaryDependencies.graph IP)
    (IC : Interpretation TypeCDependencies.Node)
    (RC : DerivedRules TypeCDependencies.graph IC)
    (IB : Interpretation TypeBDependencies.Node)
    (RB : DerivedRules TypeBDependencies.graph IB)
    (IS : Interpretation SporadicDependencies.Node)
    (RS : DerivedRules SporadicDependencies.graph IS)
    (L : PreliminaryLinks IP IC IB IS)
    (E : ResidualExternalFacts IC IB IS)
    (G : SectionGoals)
    (FamilyGoal : MainFamily → Prop)
    (H : ReductionRealisation IC IB IS G FamilyGoal)
    (FiniteGroupConsequence : Prop)
    (spathReduction : (∀ family, FamilyGoal family) → FiniteGroupConsequence) :
    FiniteGroupConsequence := by
  let EC := linkedTypeCFacts IP EP RP IC L E
  let RC' := TypeCDependencies.rulesWithRealisedPrincipalExclusion
    IC RC H.typeCBranches.principalExclusion
  have hCNode : IC.claim .symplectic :=
    TypeCDependencies.conditional_symplectic_node IC EC RC G.typeC
      H.typeCBranches
  have EB := linkedTypeBFacts IP EP RP IC RC'
    H.typeCBranches.evenFieldTransport H.typeCBranches.evenFieldFixed
      H.typeCBranches.evenUnipotentCorrespondence IB L E
  have EBall := linkedTypeBAllFacts IP EP RP IC RC'
    H.typeCBranches.evenFieldTransport H.typeCBranches.evenFieldFixed
      H.typeCBranches.evenUnipotentCorrespondence hCNode IB L E
  have ES := linkedSporadicFacts IP EP RP IS L E
  have hC : TypeCConclusion G.typeC := by
    intro n q ell p f hn hq hsimple hellPrime hfield hsp6
    exact TypeCDependencies.conditional_symplectic IC EC RC G.typeC
      H.typeCBranches n q ell p f hn hq hsimple hellPrime hfield hsp6
  have hBnodes : ∀ n, n ≠ .corTypeBCensus →
      n ∉ TypeBDependencies.censusOnlyExternalLeaves → IB.claim n :=
    TypeBDependencies.derive_without_census_inputs IB EB RB
  have hBHigh : IB.claim .propTwoHighRank :=
    TypeBDependencies.propTwoHighRank_of_external_leaves
      IB EB RB H.typeBHighRank
  have hBParameterised : TypeBConclusion G.typeB := by
    let branches : DependencyCases.TypeBBranchResults G.typeB :=
      { definingPrime := H.typeBBranches.definingPrime
          (hBnodes .propDefiningPrime (by decide) (by decide))
        oddNondefining := H.typeBBranches.oddNondefining
          (hBnodes .propOddNondefining (by decide) (by decide))
        atTwoRankThree := H.typeBBranches.atTwoRankThree
          (hBnodes .propTwoRankThree (by decide) (by decide))
        atTwoHigherRank := H.typeBBranches.atTwoHigherRank hBHigh }
    intro n ell p hn hellPrime
    exact DependencyCases.typeB_of_branch_results G.typeB branches
      n ell p hn hellPrime
  have hBOdd : IB.claim .thmTypeB := H.typeBHeadline hBParameterised
  let RB' : DerivedRules TypeBDependencies.graph IB :=
    { prove := fun n hn hdeps => by
        by_cases h : n = .thmTypeB
        · subst n
          exact hBOdd
        · exact RB.prove n hn hdeps }
  have hB : IB.claim .corTypeBCensus :=
    TypeBDependencies.census_of_exact_external_leaves IB EBall RB'
  have hS : SporadicConclusion G.sporadic := by
    intro S
    exact SporadicDependencies.conditional_sporadic IS ES RS G.sporadic
      H.sporadicBranches S
  apply spathReduction
  intro family
  cases family with
  | typeC => exact H.typeC hC
  | typeB => exact H.typeB hB
  | sporadic => exact H.sporadic hS

/-- A version of `conditional_reduction` in which the final use of Späth's
reduction theorem is split into its actual two cases.  Involved simple
sections on the modular prime support are assigned to one of the three
families proved in the manuscript.  The other involved simple sections are
handled by the defect-zero theorem.  Thus the quantifier step in Corollary
1.2 is checked rather than packaged into a single opaque implication. -/
theorem conditional_reduction_by_sections
    (IP : Interpretation PreliminaryDependencies.Node)
    (EP : ExternalFacts PreliminaryDependencies.graph IP)
    (RP : DerivedRules PreliminaryDependencies.graph IP)
    (IC : Interpretation TypeCDependencies.Node)
    (RC : DerivedRules TypeCDependencies.graph IC)
    (IB : Interpretation TypeBDependencies.Node)
    (RB : DerivedRules TypeBDependencies.graph IB)
    (IS : Interpretation SporadicDependencies.Node)
    (RS : DerivedRules SporadicDependencies.graph IS)
    (L : PreliminaryLinks IP IC IB IS)
    (E : ResidualExternalFacts IC IB IS)
    (G : SectionGoals)
    (FamilyGoal : MainFamily → Prop)
    (H : ReductionRealisation IC IB IS G FamilyGoal)
    {SimpleGroup : Type*}
    (Involved : SimpleGroup → Prop)
    (PrimeDividesOrder : SimpleGroup → Prop)
    (BelongsToFamily : SimpleGroup → MainFamily → Prop)
    (InductiveBAW : SimpleGroup → Prop)
    (BlockwiseAWC : Prop)
    (covered : ∀ S, Involved S → PrimeDividesOrder S →
      ∃ family, BelongsToFamily S family)
    (familySpecialisation : ∀ S family,
      BelongsToFamily S family → FamilyGoal family → InductiveBAW S)
    (defectZeroCase : ∀ S,
      Involved S → ¬ PrimeDividesOrder S → InductiveBAW S)
    (spathReduction : (∀ S, Involved S → InductiveBAW S) →
      BlockwiseAWC) :
    BlockwiseAWC := by
  apply conditional_reduction IP EP RP IC RC IB RB IS RS L E G
    FamilyGoal H BlockwiseAWC
  intro familyTheorems
  exact finiteGroupReduction_of_covered_sections
    Involved PrimeDividesOrder BelongsToFamily InductiveBAW FamilyGoal
    BlockwiseAWC covered familyTheorems familySpecialisation defectZeroCase
    spathReduction

end Formalisation.MainDependencies


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
