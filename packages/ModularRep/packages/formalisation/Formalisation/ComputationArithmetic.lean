import Formalisation.C2Cancellation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Arithmetic extracted from the computational transcripts

This file checks the finite arithmetic used after the GAP outputs have been
accepted: block totals, independently supplied character and weight sector
totals, cancellation for the faithful sectors of `3.Ω₇(3)`, and the orbit
signature comparison for the principal block.
It also records the five blockwise counts for `2.Sp₆(2)` at `ℓ = 3`.

The numerals below are transcript inputs.  Lean verifies every deduction from
them, but does not certify that GAP produced them or that the computed tables
represent the claimed groups, blocks, characters, or weights.
-/

namespace Formalisation.ComputationArithmetic

open Formalisation.C2Cancellation

section Sp6

/-- Blockwise weight counts printed by `sp6.g` for `2.Sp₆(2)` at `ℓ=3`. -/
def sp6BlockwiseCounts : List ℕ := [10, 2, 2, 1, 6]

theorem sp6_number_of_listed_blocks : sp6BlockwiseCounts.length = 5 := by decide

theorem sp6_total_listed_count : sp6BlockwiseCounts.sum = 21 := by decide

end Sp6

section ExceptionalTypeB

/-- The nine `2`-blocks in the transcript for `3.Ω₇(3)`. -/
inductive Q3Block where
  | B1 | B2 | B3 | B4 | B5 | B6 | B7 | B8 | B9
  deriving DecidableEq, Repr

instance : Fintype Q3Block := derive_fintype% Q3Block

/-- Brauer-character counts printed by `o7blocks.g`. -/
def q3BrauerCount : Q3Block → ℕ
  | .B1 => 12
  | .B2 => 2
  | .B3 => 1
  | .B4 => 1
  | .B5 => 1
  | .B6 => 6
  | .B7 => 6
  | .B8 => 2
  | .B9 => 2

/-- The outer involution on blocks printed by `o7blocks.g`. -/
def q3OuterBlockAction : Equiv.Perm Q3Block where
  toFun
    | .B1 => .B1
    | .B2 => .B2
    | .B3 => .B3
    | .B4 => .B4
    | .B5 => .B5
    | .B6 => .B7
    | .B7 => .B6
    | .B8 => .B9
    | .B9 => .B8
  invFun
    | .B1 => .B1
    | .B2 => .B2
    | .B3 => .B3
    | .B4 => .B4
    | .B5 => .B5
    | .B6 => .B7
    | .B7 => .B6
    | .B8 => .B9
    | .B9 => .B8
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

theorem q3_outer_block_action_involutive :
    Function.Involutive q3OuterBlockAction := by
  intro b
  cases b <;> rfl

theorem q3_brauer_counts_outer_invariant (b : Q3Block) :
    q3BrauerCount (q3OuterBlockAction b) = q3BrauerCount b := by
  cases b <;> rfl

theorem q3_total_brauer_count :
    ∑ b : Q3Block, q3BrauerCount b = 33 := by decide

/-- The three central character sectors visible in the transcript. -/
inductive Q3Sector where
  | trivial | faithfulOne | faithfulTwo
  deriving DecidableEq, Repr

def q3Sector : Q3Block → Q3Sector
  | .B1 | .B2 | .B3 | .B4 | .B5 => .trivial
  | .B6 | .B8 => .faithfulOne
  | .B7 | .B9 => .faithfulTwo

theorem q3_trivial_sector_total :
    q3BrauerCount .B1 + q3BrauerCount .B2 + q3BrauerCount .B3 +
      q3BrauerCount .B4 + q3BrauerCount .B5 = 17 := by decide

theorem q3_first_faithful_sector_total :
    q3BrauerCount .B6 + q3BrauerCount .B8 = 8 := by decide

theorem q3_second_faithful_sector_total :
    q3BrauerCount .B7 + q3BrauerCount .B9 = 8 := by decide

theorem q3_sector_totals_exhaust_total : 17 + 8 + 8 = 33 := by decide

/-- Contributions by radical-subgroup order printed by `o7radical.out`. -/
structure Q3RadicalContribution where
  subgroupOrder : ℕ
  trivial : ℕ
  faithfulOne : ℕ
  faithfulTwo : ℕ
  deriving DecidableEq, Repr

def q3RadicalContributions : List Q3RadicalContribution :=
  [⟨512, 1, 1, 1⟩, ⟨256, 6, 2, 2⟩, ⟨128, 4, 0, 0⟩,
   ⟨64, 0, 2, 2⟩, ⟨32, 1, 1, 1⟩, ⟨8, 1, 1, 1⟩,
   ⟨4, 1, 1, 1⟩, ⟨2, 1, 0, 0⟩, ⟨1, 2, 0, 0⟩]

theorem q3_nine_radical_order_contributions :
    q3RadicalContributions.length = 9 := by decide

theorem q3_radical_contribution_orders_distinct :
    (q3RadicalContributions.map Q3RadicalContribution.subgroupOrder).Nodup := by
  decide

/-- Weight-sector totals obtained by summing those transcript rows. -/
def q3WeightSectorTotals : Q3Sector → ℕ
  | .trivial => (q3RadicalContributions.map Q3RadicalContribution.trivial).sum
  | .faithfulOne =>
      (q3RadicalContributions.map Q3RadicalContribution.faithfulOne).sum
  | .faithfulTwo =>
      (q3RadicalContributions.map Q3RadicalContribution.faithfulTwo).sum

theorem q3_weight_sector_totals :
    q3WeightSectorTotals .trivial = 17 ∧
      q3WeightSectorTotals .faithfulOne = 8 ∧
      q3WeightSectorTotals .faithfulTwo = 8 := by decide

/-- Brauer-character totals obtained from the block data in `o7blocks.out`. -/
def q3BrauerSectorTotals : Q3Sector → ℕ
  | .trivial => 17
  | .faithfulOne => 8
  | .faithfulTwo => 8

/-- The independently printed weight totals agree with the Brauer totals in
each central character sector. -/
theorem q3_weight_and_brauer_sector_totals_agree (sector : Q3Sector) :
    q3WeightSectorTotals sector = q3BrauerSectorTotals sector := by
  cases sector <;> rfl

/-- Once the two-weight contribution of `B8` (respectively `B9`) is known,
the faithful-sector total forces the six-weight contribution of `B6`
(respectively `B7`). -/
theorem q3_faithful_sector_subtraction : 8 - 2 = 6 := by decide

/-- Inputs on the Brauer-character side from `o7brauer.out`: ten characters
upstairs, with eight irreducible restrictions and two restrictions that split
into pairs. -/
def q3PrincipalHBrauerCount : ℕ := 10
def q3PrincipalIrreducibleRestrictions : ℕ := 8
def q3PrincipalSplitRestrictions : ℕ := 2

def q3PrincipalBrauerOrbitData : C2OrbitData :=
  (q3PrincipalIrreducibleRestrictions, q3PrincipalSplitRestrictions)

/-- Inputs on the weight side: the total of ten classes for the outer group
is cited from Feng--Yu--Zhang, while `o7weights.out` finds the two classes
that split into pairs on restriction to the simple group. -/
def q3PrincipalHWeightCount : ℕ := 10
def q3PrincipalSplittingHWeightCount : ℕ := 2

def q3PrincipalWeightOrbitData : C2OrbitData :=
  (q3PrincipalHWeightCount - q3PrincipalSplittingHWeightCount,
    q3PrincipalSplittingHWeightCount)

theorem q3_principal_brauer_restriction_census :
    q3PrincipalIrreducibleRestrictions + q3PrincipalSplitRestrictions =
      q3PrincipalHBrauerCount := by decide

theorem q3_principal_orbit_data_agree :
    q3PrincipalBrauerOrbitData = q3PrincipalWeightOrbitData := rfl

theorem q3_principal_orbit_signature :
    signature q3PrincipalBrauerOrbitData = (12, 8) ∧
      signature q3PrincipalWeightOrbitData = (12, 8) := by decide

/-- Numerical data printed for the second block. -/
structure Q3BlockTwoData where
  defectOrder : ℕ
  ordinaryCount : ℕ
  brauerCount : ℕ
  heights : List ℕ
  deriving DecidableEq, Repr

def q3BlockTwoData : Q3BlockTwoData where
  defectOrder := 8
  ordinaryCount := 5
  brauerCount := 2
  heights := [0, 0, 1, 0, 0]

theorem q3_block_two_height_list_complete :
    q3BlockTwoData.heights.length = q3BlockTwoData.ordinaryCount := by decide

theorem q3_block_two_has_one_positive_height :
    q3BlockTwoData.heights.count 1 = 1 := by decide

/-- Search/fusion counts printed by `o7radical.g`. -/
structure Q3RadicalSearchData where
  tested : ℕ
  rawRadicalRepresentatives : ℕ
  fusedClasses : ℕ
  deriving DecidableEq, Repr

def q3RadicalSearchData : Q3RadicalSearchData where
  tested := 3021
  rawRadicalRepresentatives := 26
  fusedClasses := 12

theorem q3_radical_search_reduces_counts :
    q3RadicalSearchData.fusedClasses ≤
        q3RadicalSearchData.rawRadicalRepresentatives ∧
      q3RadicalSearchData.rawRadicalRepresentatives ≤
        q3RadicalSearchData.tested := by decide

end ExceptionalTypeB

section Sporadic

/-- Convert a signature `(total points, fixed points)` used in the sporadic
section to its orbit data when the nonfixed points form pairs. -/
def orbitDataOfSignature (total fixed : ℕ) : C2OrbitData :=
  (fixed, (total - fixed) / 2)

/-- The conversion from a signature is valid when the fixed count is at most
the total count and the number of nonfixed points is even. -/
theorem signature_orbitDataOfSignature
    {total fixed : ℕ} (hle : fixed ≤ total)
    (heven : ∃ pairs, total - fixed = 2 * pairs) :
    signature (orbitDataOfSignature total fixed) = (total, fixed) := by
  rcases heven with ⟨pairs, hpairs⟩
  simp only [signature, card, fixedOrbits, twoElementOrbits,
    orbitDataOfSignature]
  have htotal : total = fixed + 2 * pairs := by omega
  simp [htotal]

theorem fi24_two_total_trivial_signature :
    signature (orbitDataOfSignature 41 31) = (41, 31) := by decide

theorem fi24_two_defect_four_signature :
    signature (orbitDataOfSignature 3 1) = (3, 1) := by decide

theorem fi24_two_dihedral_signature :
    signature (orbitDataOfSignature 3 3) = (3, 3) := by decide

theorem fi24_two_defect_zero_signature :
    signature (orbitDataOfSignature 1 1) = (1, 1) := by decide

/-- Cancelling signatures `(3,1)`, `(3,3)`, `(1,1)`, and `(1,1)` from
the corrected trivial-sector signature `(41,31)` leaves `(33,25)` for the
principal block. -/
theorem fi24_two_principal_signature_subtraction :
    (41 - (3 + 3 + 1 + 1), 31 - (1 + 3 + 1 + 1)) = (33, 25) := by decide

/-- The orbit-data version of the same cancellation, so it is not merely a
coordinatewise calculation with signatures. -/
theorem fi24_two_orbit_data_cancellation :
    orbitDataOfSignature 41 31 =
      orbitDataOfSignature 33 25 +
        (orbitDataOfSignature 3 1 + orbitDataOfSignature 3 3 +
          orbitDataOfSignature 1 1 + orbitDataOfSignature 1 1) := by decide

theorem fi24_faithful_sector_subtraction : 25 - 2 = 23 := by decide

theorem baby_two_restriction_rank_total : 25 + 2 = 27 := by decide

theorem baby_two_principal_weight_subtraction : 27 - 2 = 25 := by decide

def babySevenRestrictionRanks : List ℕ := [24, 24, 21, 24]

theorem baby_seven_four_noncyclic_blocks :
    babySevenRestrictionRanks.length = 4 := by decide

def babySevenRegularClassCount : ℕ := 222

theorem baby_seven_regular_class_count : babySevenRegularClassCount = 222 := rfl

theorem baby_seven_historical_count_differs : babySevenRegularClassCount ≠ 220 := by
  decide

def monsterTwoDefects : List ℕ := [46, 0, 0, 4, 0]

def monsterTwoOrdinaryCounts : List ℕ := [183, 1, 1, 8, 1]

theorem monster_two_has_five_blocks :
    monsterTwoDefects.length = 5 ∧ monsterTwoOrdinaryCounts.length = 5 := by
  decide

theorem monster_two_three_defect_zero_blocks :
    monsterTwoDefects.count 0 = 3 := by decide

theorem monster_two_total_ordinary_count :
    monsterTwoOrdinaryCounts.sum = 194 := by decide

def monsterTwoRegularClassCount : ℕ := 61

theorem monster_two_regular_class_count : monsterTwoRegularClassCount = 61 := rfl

end Sporadic

end Formalisation.ComputationArithmetic


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
