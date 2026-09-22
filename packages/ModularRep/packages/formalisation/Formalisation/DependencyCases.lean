import Formalisation.SymplecticCaseSplit
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Exhaustive case dependencies for the headline theorems

This file formalises the case divisions at the ends of the type `C`, type
`B`, and sporadic sections.  The predicate supplied as `Goal` represents the
relevant iBAW conclusion.  The branch hypotheses record exactly which cited
or manuscript result supplies that conclusion in each case.

The file checks exhaustiveness and the final deductions.  It does not prove
the branch hypotheses, which are audited separately in the dependency
modules for the three sections.
-/

namespace Formalisation.DependencyCases

section TypeC

/-- Results assigned to the eight branches in the proof of the symplectic
theorem. -/
structure TypeCBranchResults
    (Goal : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) where
  rankTwo : ∀ n q ell p f, n = 2 → 2 < q → Goal n q ell p f
  definingPrime : ∀ n q ell p f, 3 ≤ n → ell = p → Goal n q ell p f
  oddFieldAtTwo : ∀ n q ell p f,
    3 ≤ n → Odd q → ell = 2 → Goal n q ell p f
  oddFieldOddPrime : ∀ n q ell p f,
    3 ≤ n → Odd q → ell ≠ p → Odd ell → Goal n q ell p f
  sp6AtFiveOrSeven : ∀ n q ell p f,
    n = 3 → q = 2 → (ell = 5 ∨ ell = 7) → Goal n q ell p f
  sp6AtThree : ∀ n q ell p f,
    n = 3 → q = 2 → ell = 3 → Goal n q ell p f
  evenFieldRankThree : ∀ n q ell p f,
    n = 3 → p = 2 → q = 2 ^ f → 2 ≤ f → Odd ell → Goal n q ell p f
  evenFieldHigherRank : ∀ n q ell p f,
    4 ≤ n → p = 2 → q = 2 ^ f → 0 < f → Odd ell → Goal n q ell p f

/-- Once the eight branch results are supplied, the exhaustive case split
proves the symplectic conclusion for every admissible parameter tuple. -/
theorem typeC_of_branch_results
    (Goal : ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (R : TypeCBranchResults Goal)
    (n q ell p f : ℕ)
    (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hsimple : ¬ (n = 2 ∧ q = 2))
    (hellPrime : Nat.Prime ell)
    (hfield : Odd q ∨ (p = 2 ∧ q = 2 ^ f ∧ 0 < f))
    (hsp6 : n = 3 → q = 2 → ell ≠ p →
      ell = 3 ∨ ell = 5 ∨ ell = 7) :
    Goal n q ell p f := by
  have hcase := symplectic_case_exhaustion n q ell p f hn hq hsimple
    hellPrime hfield hsp6
  cases hcase with
  | rankTwo hn' hq' => exact R.rankTwo n q ell p f hn' hq'
  | definingPrime hn' hell => exact R.definingPrime n q ell p f hn' hell
  | oddFieldAtTwo hn' hq' hell =>
      exact R.oddFieldAtTwo n q ell p f hn' hq' hell
  | oddFieldOddPrime hn' hq' hndef hell =>
      exact R.oddFieldOddPrime n q ell p f hn' hq' hndef hell
  | sp6AtFiveOrSeven hn' hq' hell =>
      exact R.sp6AtFiveOrSeven n q ell p f hn' hq' hell
  | sp6AtThree hn' hq' hell => exact R.sp6AtThree n q ell p f hn' hq' hell
  | evenFieldRankThree hn' hp hq' hf hell =>
      exact R.evenFieldRankThree n q ell p f hn' hp hq' hf hell
  | evenFieldHigherRank hn' hp hq' hf hell =>
      exact R.evenFieldHigherRank n q ell p f hn' hp hq' hf hell

end TypeC

section TypeB

/-- The four branches in the proof of the odd-characteristic type `B`
theorem. -/
inductive TypeBCase (n ell p : ℕ) : Prop
  | definingPrime (hell : ell = p)
  | oddNondefining (hndef : ell ≠ p) (hell : Odd ell)
  | atTwoRankThree (hell : ell = 2) (hn : n = 3)
  | atTwoHigherRank (hell : ell = 2) (hn : 4 ≤ n)

/-- A prime and rank in the range of the type `B` theorem lies in one of
the four branches used in its concluding proof. -/
theorem typeB_case_exhaustion
    (n ell p : ℕ) (hn : 3 ≤ n) (hellPrime : Nat.Prime ell) :
    TypeBCase n ell p := by
  by_cases hdef : ell = p
  · exact TypeBCase.definingPrime hdef
  rcases hellPrime.eq_two_or_odd' with hellTwo | hellOdd
  · by_cases hnThree : n = 3
    · exact TypeBCase.atTwoRankThree hellTwo hnThree
    · exact TypeBCase.atTwoHigherRank hellTwo (by omega)
  · exact TypeBCase.oddNondefining hdef hellOdd

/-- Results assigned to the four branches in the type `B` completion. -/
structure TypeBBranchResults (Goal : ℕ → ℕ → ℕ → Prop) where
  definingPrime : ∀ n ell p, ell = p → Goal n ell p
  oddNondefining : ∀ n ell p, ell ≠ p → Odd ell → Goal n ell p
  atTwoRankThree : ∀ n ell p, ell = 2 → n = 3 → Goal n ell p
  atTwoHigherRank : ∀ n ell p, ell = 2 → 4 ≤ n → Goal n ell p

/-- The four branch results imply the odd-characteristic type `B` theorem
for every rank at least three and every prime. -/
theorem typeB_of_branch_results
    (Goal : ℕ → ℕ → ℕ → Prop) (R : TypeBBranchResults Goal)
    (n ell p : ℕ) (hn : 3 ≤ n) (hellPrime : Nat.Prime ell) :
    Goal n ell p := by
  cases typeB_case_exhaustion n ell p hn hellPrime with
  | definingPrime h => exact R.definingPrime n ell p h
  | oddNondefining hndef hodd => exact R.oddNondefining n ell p hndef hodd
  | atTwoRankThree htwo hn' => exact R.atTwoRankThree n ell p htwo hn'
  | atTwoHigherRank htwo hn' => exact R.atTwoHigherRank n ell p htwo hn'

end TypeB

section Sporadic

/-- The twenty-six sporadic simple groups. -/
inductive SporadicGroup where
  | M11 | M12 | M22 | M23 | M24
  | J1 | J2 | J3 | J4
  | HS | McL | He | Ru | Suz | O_N
  | Co1 | Co2 | Co3
  | Fi22 | Fi23 | Fi24Prime
  | HN | Ly | Th | Baby | Monster
  deriving DecidableEq

/-- The four groups treated in the manuscript rather than by the cited
CTBlocks overview. -/
def BoundaryFour : Finset SporadicGroup :=
  {SporadicGroup.J4, SporadicGroup.Fi24Prime,
    SporadicGroup.Baby, SporadicGroup.Monster}

/-- The complementary twenty-two groups for which the manuscript invokes
the CTBlocks verification. -/
def CTBlocksTwentyTwo : Finset SporadicGroup :=
  {SporadicGroup.M11, SporadicGroup.M12, SporadicGroup.M22,
    SporadicGroup.M23, SporadicGroup.M24, SporadicGroup.J1,
    SporadicGroup.J2, SporadicGroup.J3, SporadicGroup.HS,
    SporadicGroup.McL, SporadicGroup.He, SporadicGroup.Ru,
    SporadicGroup.Suz, SporadicGroup.O_N, SporadicGroup.Co1,
    SporadicGroup.Co2, SporadicGroup.Co3, SporadicGroup.Fi22,
    SporadicGroup.Fi23, SporadicGroup.HN, SporadicGroup.Ly,
    SporadicGroup.Th}

def AllSporadic : Finset SporadicGroup := CTBlocksTwentyTwo ∪ BoundaryFour

theorem card_all_sporadic : AllSporadic.card = 26 := by decide

theorem card_boundary_four : BoundaryFour.card = 4 := by decide

theorem card_CTBlocks_twenty_two : CTBlocksTwentyTwo.card = 22 := by decide

theorem sporadic_coverage (S : SporadicGroup) :
    S ∈ CTBlocksTwentyTwo ∨ S ∈ BoundaryFour := by
  cases S <;> simp [CTBlocksTwentyTwo, BoundaryFour]

/-- The cited twenty-two-group verification and the manuscript's four-group
proposition together imply the sporadic theorem. -/
theorem sporadic_of_twenty_two_and_four
    (Goal : SporadicGroup → Prop)
    (hCTBlocks : ∀ S, S ∈ CTBlocksTwentyTwo → Goal S)
    (hBoundary : ∀ S, S ∈ BoundaryFour → Goal S)
    (S : SporadicGroup) : Goal S := by
  rcases sporadic_coverage S with h | h
  · exact hCTBlocks S h
  · exact hBoundary S h

end Sporadic

end Formalisation.DependencyCases


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
