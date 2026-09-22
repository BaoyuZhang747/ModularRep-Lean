import Formalisation.ComputationArithmetic
import Formalisation.C2Cancellation
import Mathlib.Tactic

/-!
# Paper proof: finite deductions in Proposition 5.7

This file checks the manuscript-specific finite arithmetic used in the four
sporadic branches of Proposition 5.7.  The representation theoretic results,
the correctness of the character tables, and the GAP calculations are not
reproved here.  Their outputs enter only as the explicitly transcribed data
listed in the accompanying contract.

The checked deductions are:

* the corrected `Fi'_24` Table 8 entries at `2` sum to signature `(41,31)`;
* the two known fixed weights in the three-weight dihedral block force its
  third weight to be fixed;
* the independently transcribed `Fi'_24` block and weight outputs at `5`
  agree, including the two faithful-sector block orbits;
* the Baby Monster and Monster subtraction arguments force the principal
  block equalities; and
* tagging the four prime lists by their groups gives exactly forty-five
  distinct pairs.
-/

namespace ModularRep.PaperProofs.SporadicProposition57ComputationRelative

open Formalisation.C2Cancellation

/-! ## The corrected `Fi'_24` table at `2` -/

/-- An entry `a/b` in the corrected An--Dietrich table: `a` points are fixed
by the outer involution and `b` points are not fixed. -/
structure TableSignatureEntry where
  fixed : Nat
  nonfixed : Nat
  deriving DecidableEq, Repr

def TableSignatureEntry.total (entry : TableSignatureEntry) : Nat :=
  entry.fixed + entry.nonfixed

/-- The thirty-four entries in the trivial central character column of the
corrected An--Dietrich Table 8 at `2`, in table order. -/
def correctedFi24Table8AtTwo : List TableSignatureEntry :=
  [⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩,
   ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨1, 0⟩,
   ⟨0, 2⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩,
   ⟨0, 2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩,
   ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]

theorem correctedFi24Table8AtTwo_length :
    correctedFi24Table8AtTwo.length = 34 := by
  decide

theorem correctedFi24Table8AtTwo_nonfixed_even :
    ∀ entry ∈ correctedFi24Table8AtTwo, Even entry.nonfixed := by
  decide

/-- This is the table summation behind the sector signature `(41,31)` in the
manuscript, rather than an assumption of that already-summed signature. -/
theorem correctedFi24Table8AtTwo_signature_sum :
    (correctedFi24Table8AtTwo.map TableSignatureEntry.total).sum = 41 ∧
      (correctedFi24Table8AtTwo.map TableSignatureEntry.fixed).sum = 31 := by
  decide

/-- Removing the three weights of signature `(3,1)` from the four weights of
signature `(4,2)` leaves one further fixed weight. -/
theorem fi24_remaining_klein_four_weight_fixed
    (remainingTotal remainingFixed : Nat)
    (hTotal : 3 + remainingTotal = 4)
    (hFixed : 1 + remainingFixed = 2) :
    remainingTotal = 1 ∧ remainingFixed = 1 := by
  omega

/-- A three-point set with an involution and at least two fixed points is
fixed pointwise.  This is the parity step used for the `D_8` block. -/
theorem three_weights_two_fixed_force_all_fixed
    (data : C2OrbitData) (hcard : card data = 3)
    (hknown : 2 ≤ fixedOrbits data) :
    signature data = (3, 3) := by
  rcases data with ⟨fixed, pairs⟩
  change fixed + 2 * pairs = 3 at hcard
  change 2 ≤ fixed at hknown
  have hfixed : fixed = 3 := by omega
  have hpairs : pairs = 0 := by omega
  simp [signature, card, fixedOrbits, twoElementOrbits, hfixed, hpairs]

/-- The corrected total signature, the defect-four signature, the dihedral
signature, and the two defect-zero signatures leave the principal signature
printed by `fi24blocks.g`. -/
theorem fi24_principal_signature_forced :
    (41 - (3 + 3 + 1 + 1), 31 - (1 + 3 + 1 + 1)) = (33, 25) := by
  decide

/-! ## Independent `Fi'_24` transcripts at `5` -/

abbrev SignatureRow := Nat × Nat × Nat
abbrev CountRow := Nat × Nat

/-- `(block identifier, Brauer count, fixed count)` from `fi24blocks.g`. -/
def fi24FiveBrauerTrivialRows : List SignatureRow :=
  [(1, 16, 16), (2, 14, 6), (3, 16, 16)]

/-- `(block identifier, weight count, fixed count)` from `fi24weights.g`. -/
def fi24FiveWeightTrivialRows : List SignatureRow :=
  [(1, 16, 16), (2, 14, 6), (3, 16, 16)]

theorem fi24_five_trivial_signatures_agree :
    fi24FiveBrauerTrivialRows = fi24FiveWeightTrivialRows := by
  decide

theorem fi24_five_trivial_weight_total :
    (fi24FiveWeightTrivialRows.map (fun row => row.2.1)).sum = 46 := by
  decide

/-- Positive-defect block counts in the cover from `fi24blocks.g`. -/
def fi24FiveBrauerCoverRows : List CountRow :=
  [(1, 16), (2, 14), (3, 16), (45, 16), (46, 16), (47, 14), (48, 14)]

/-- Weight counts for the same blocks from `fi24weights.g`. -/
def fi24FiveWeightCoverRows : List CountRow :=
  [(1, 16), (2, 14), (3, 16), (45, 16), (46, 16), (47, 14), (48, 14)]

theorem fi24_five_cover_counts_agree :
    fi24FiveBrauerCoverRows = fi24FiveWeightCoverRows := by
  decide

theorem fi24_five_cover_weight_total :
    (fi24FiveWeightCoverRows.map Prod.snd).sum = 106 := by
  decide

/-- Blocks `45,47` lie in one faithful sector and `46,48` in the sector
obtained from it by the outer involution.  Each sector therefore has thirty
weights supported on the radical subgroup of order twenty-five. -/
theorem fi24_five_faithful_sector_totals :
    16 + 14 = 30 ∧ 16 + 14 = 30 := by
  decide

inductive Fi24FaithfulFiveBlock
  | b45 | b46 | b47 | b48
  deriving DecidableEq, Repr

/-- The outer action on the four faithful-sector blocks printed by
`fi24blocks.g`. -/
def fi24FaithfulFiveOuter :
    Fi24FaithfulFiveBlock → Fi24FaithfulFiveBlock
  | .b45 => .b46
  | .b46 => .b45
  | .b47 => .b48
  | .b48 => .b47

theorem fi24FaithfulFiveOuter_involutive :
    Function.Involutive fi24FaithfulFiveOuter := by
  intro block
  cases block <;> rfl

theorem fi24FaithfulFiveOuter_fixed_point_free
    (block : Fi24FaithfulFiveBlock) :
    fi24FaithfulFiveOuter block ≠ block := by
  cases block <;> decide

/-! ## Baby Monster and Monster subtraction -/

/-- The two Baby Monster restriction ranks and the cited total weight count
force equality in the principal block. -/
theorem baby_two_principal_count_forced
    (principalBrauer nonprincipalBrauer principalWeights nonprincipalWeights : Nat)
    (hBrauerTotal : principalBrauer + nonprincipalBrauer = 27)
    (hWeightTotal : principalWeights + nonprincipalWeights = 27)
    (hNonprincipalBrauer : nonprincipalBrauer = 2)
    (hNonprincipalWeights : nonprincipalWeights = 2) :
    principalBrauer = 25 ∧ principalWeights = 25 ∧
      principalBrauer = principalWeights := by
  omega

/-- For the Monster, the three defect-zero blocks contribute one on each
side and the defect-four block satisfies the numerical conjecture.  Equality
of the two totals therefore forces equality in the principal block without
requiring the defect-four contribution to be known numerically. -/
theorem monster_two_principal_count_forced
    (principalBrauer principalWeights defectFourBrauer defectFourWeights : Nat)
    (hBrauerTotal : principalBrauer + defectFourBrauer + 3 = 61)
    (hWeightTotal : principalWeights + defectFourWeights + 3 = 61)
    (hDefectFour : defectFourBrauer = defectFourWeights) :
    principalBrauer = principalWeights := by
  omega

/-! ## Coverage of the forty-five displayed pairs -/

inductive BoundaryGroup
  | j4 | fi24 | baby | monster
  deriving DecidableEq, Repr

abbrev BoundaryPair := BoundaryGroup × Nat

def j4Primes : List Nat := [2, 3, 5, 7, 11, 23, 29, 31, 37, 43]
def fi24Primes : List Nat := [2, 3, 5, 7, 11, 13, 17, 23, 29]
def babyPrimes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47]
def monsterPrimes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

def boundaryPairs : List BoundaryPair :=
  j4Primes.map (BoundaryGroup.j4, ·) ++
    fi24Primes.map (BoundaryGroup.fi24, ·) ++
    babyPrimes.map (BoundaryGroup.baby, ·) ++
    monsterPrimes.map (BoundaryGroup.monster, ·)

theorem boundary_prime_lists_nodup :
    j4Primes.Nodup ∧ fi24Primes.Nodup ∧ babyPrimes.Nodup ∧
      monsterPrimes.Nodup := by
  decide

theorem boundary_group_pair_counts :
    j4Primes.length = 10 ∧ fi24Primes.length = 9 ∧
      babyPrimes.length = 11 ∧ monsterPrimes.length = 15 := by
  decide

theorem boundary_pairs_exactly_forty_five :
    boundaryPairs.length = 45 ∧ boundaryPairs.Nodup := by
  decide

theorem mem_boundaryPairs_iff (pair : BoundaryPair) :
    pair ∈ boundaryPairs ↔
      (pair.1 = .j4 ∧ pair.2 ∈ j4Primes) ∨
      (pair.1 = .fi24 ∧ pair.2 ∈ fi24Primes) ∨
      (pair.1 = .baby ∧ pair.2 ∈ babyPrimes) ∨
      (pair.1 = .monster ∧ pair.2 ∈ monsterPrimes) := by
  rcases pair with ⟨group, prime⟩
  cases group <;> simp [boundaryPairs, j4Primes, fi24Primes, babyPrimes,
    monsterPrimes]

end ModularRep.PaperProofs.SporadicProposition57ComputationRelative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
