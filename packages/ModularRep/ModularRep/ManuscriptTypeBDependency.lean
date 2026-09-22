import Mathlib.Tactic

/-!
# Repair and topological order of the local type B dependencies

An earlier manuscript version had three literal references forming a cycle:

* the localized-return lemma used the rank-three proposition;
* the high-rank proposition used the localized-return lemma;
* the rank-three proposition used the proof of the high-rank proposition.

The former rank-three edge in the localized-return lemma is replaced by the
principal-selector result, while the independent exceptional `q = 3` input
remains.  The third edge is replaced by the local odd-label and proper Levi
argument.  The manuscript now orders the eight affected results as rational
field, GGGR rank, principal selector, rank-three principal block, exceptional
`q = 3`, all rank-three blocks, localized return, and high rank.  This file
retains the former cycle as an audit record and certifies that the repaired
current relation is ranked and acyclic.  It asserts no
representation theoretic input.
-/

namespace ModularRep.ManuscriptVerification.TypeBLocalDependency

/-- The eight manuscript results moved into dependency order. -/
inductive Result where
  | rationalField
  | gggrRank
  | principalSelector
  | rankThreePrincipal
  | exceptionalQ3
  | twoRankThree
  | localizedReturn
  | twoHighRank
  deriving DecidableEq, Repr

/-- The relevant literal cross-references before the manuscript repair. -/
def literalDependencies : Result → List Result
  | .rationalField => []
  | .gggrRank => []
  | .principalSelector => [.rationalField, .gggrRank]
  | .rankThreePrincipal => [.principalSelector]
  | .exceptionalQ3 => []
  | .twoRankThree => [.twoHighRank]
  | .localizedReturn => [.twoRankThree]
  | .twoHighRank => [.localizedReturn]

theorem literal_three_cycle :
    Result.twoRankThree ∈ literalDependencies .localizedReturn ∧
      Result.localizedReturn ∈ literalDependencies .twoHighRank ∧
      Result.twoHighRank ∈ literalDependencies .twoRankThree := by
  decide

/-- No natural-number rank can decrease along every literal dependency edge. -/
theorem literalDependencies_not_rankable :
    ¬ ∃ rank : Result → ℕ,
      ∀ {n d}, d ∈ literalDependencies n → rank d < rank n := by
  rintro ⟨rank, lower⟩
  have h₁ : rank .twoRankThree < rank .localizedReturn :=
    lower (n := .localizedReturn) (d := .twoRankThree) (by decide)
  have h₂ : rank .localizedReturn < rank .twoHighRank :=
    lower (n := .twoHighRank) (d := .localizedReturn) (by decide)
  have h₃ : rank .twoHighRank < rank .twoRankThree :=
    lower (n := .twoRankThree) (d := .twoHighRank) (by decide)
  omega

/-- The repaired dependencies among the eight reordered manuscript results. -/
def correctedDependencies : Result → List Result
  | .rationalField => []
  | .gggrRank => []
  | .principalSelector => [.rationalField, .gggrRank]
  | .rankThreePrincipal => [.principalSelector]
  | .exceptionalQ3 => []
  | .twoRankThree => [.rankThreePrincipal, .exceptionalQ3]
  | .localizedReturn => [.principalSelector, .exceptionalQ3]
  | .twoHighRank =>
      [.principalSelector, .rankThreePrincipal, .exceptionalQ3,
       .localizedReturn]

/-- The source order `R,G,P,T,Q,B,L,H`, used as a decreasing dependency rank. -/
def correctedRank : Result → ℕ
  | .rationalField => 0
  | .gggrRank => 1
  | .principalSelector => 2
  | .rankThreePrincipal => 3
  | .exceptionalQ3 => 4
  | .twoRankThree => 5
  | .localizedReturn => 6
  | .twoHighRank => 7

theorem correctedDependencies_lower {n d : Result}
    (h : d ∈ correctedDependencies n) : correctedRank d < correctedRank n := by
  cases n <;> cases d <;> simp [correctedDependencies, correctedRank] at h ⊢

/-- A dependency relation equipped with a strictly decreasing natural-number
rank.  This deliberately contains no interpretation or proof callback. -/
structure RankedDependency (Node : Type*) where
  dependencies : Node → List Node
  rank : Node → ℕ
  dependencies_lower : ∀ {n d}, d ∈ dependencies n → rank d < rank n

namespace RankedDependency

theorem not_mem_own_dependencies {Node : Type*}
    (D : RankedDependency Node) (n : Node) :
    n ∉ D.dependencies n := by
  intro h
  exact (Nat.lt_irrefl _ (D.dependencies_lower h))

theorem no_two_cycle {Node : Type*}
    (D : RankedDependency Node) {n d : Node}
    (h : d ∈ D.dependencies n) :
    n ∉ D.dependencies d := by
  intro hback
  exact (Nat.not_lt_of_ge (Nat.le_of_lt (D.dependencies_lower h)))
    (D.dependencies_lower hback)

end RankedDependency

/-- The current local relation after the circular references have been removed. -/
abbrev currentDependencies : Result → List Result := correctedDependencies

/-- The current dependency relation as a checked ranked dependency
relation. -/
def correctedGraph : RankedDependency Result where
  dependencies := currentDependencies
  rank := correctedRank
  dependencies_lower := correctedDependencies_lower

theorem corrected_no_self_dependency (n : Result) :
    n ∉ currentDependencies n :=
  correctedGraph.not_mem_own_dependencies n

theorem corrected_no_two_cycle {n d : Result}
    (h : d ∈ currentDependencies n) :
    n ∉ currentDependencies d :=
  correctedGraph.no_two_cycle h

theorem localizedReturn_uses_principalSelector :
    Result.principalSelector ∈ currentDependencies .localizedReturn := by
  decide

theorem localizedReturn_does_not_use_rankThree :
    Result.twoRankThree ∉ currentDependencies .localizedReturn := by
  decide

theorem rankThree_does_not_use_highRank :
    Result.twoHighRank ∉ currentDependencies .twoRankThree := by
  decide

theorem highRank_does_not_use_rankThree :
    Result.twoRankThree ∉ currentDependencies .twoHighRank := by
  decide

theorem rankThree_does_not_use_localizedReturn :
    Result.localizedReturn ∉ currentDependencies .twoRankThree := by
  decide

end ModularRep.ManuscriptVerification.TypeBLocalDependency


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
