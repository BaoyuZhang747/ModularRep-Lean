import Formalisation.DependencyCases
import ModularRep.PaperProofs.SporadicProposition57ComputationRelative

/-!
# Paper proof: finite construction in Theorem 5.1

This file checks the final finite case construction for the sporadic theorem
without using the manuscript dependency graph.  The twenty-two-group
CTBlocks result and Proposition 5.7 are represented by two separate theorem
arguments.  A third argument is the exact Atlas prime-support statement for
the four boundary groups.  Lean then proves that these inputs cover every
sporadic group at every prime dividing its order.

The representation theoretic assertions supplied by CTBlocks and
Proposition 5.7, the Atlas order data identifying the prime divisors of the
four boundary groups, and the identification of the twenty-six constructors
with the actual sporadic simple groups remain external inputs.  The kernel
checks the conversion between the two finite name types, the forty-five-pair
inventory, and the final quantifier construction.
-/

namespace ModularRep.PaperProofs.SporadicTheorem51AssemblyRelative

open Formalisation.DependencyCases
open ModularRep.PaperProofs.SporadicProposition57ComputationRelative

/-- Embed the four group names used by the Proposition 5.7 computation into
the enumeration of all twenty-six sporadic groups. -/
def boundaryToSporadic : BoundaryGroup → SporadicGroup
  | .j4 => .J4
  | .fi24 => .Fi24Prime
  | .baby => .Baby
  | .monster => .Monster

theorem boundaryToSporadic_injective :
    Function.Injective boundaryToSporadic := by
  intro G H h
  cases G <;> cases H <;> simp_all [boundaryToSporadic]

/-- The four groups in `BoundaryFour` are exactly the image of the four
group names used in the explicit list of forty-five pairs. -/
theorem mem_boundaryFour_iff_exists_boundaryGroup (S : SporadicGroup) :
    S ∈ BoundaryFour ↔
      ∃ G : BoundaryGroup, boundaryToSporadic G = S := by
  constructor
  · intro h
    simp only [BoundaryFour, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h
    · exact ⟨.j4, h.symm⟩
    · exact ⟨.fi24, h.symm⟩
    · exact ⟨.baby, h.symm⟩
    · exact ⟨.monster, h.symm⟩
  · rintro ⟨G, rfl⟩
    cases G <;> simp [boundaryToSporadic, BoundaryFour]

/-- Every group name used by the Proposition 5.7 list belongs to
`BoundaryFour` after embedding it in the twenty-six-group enumeration. -/
theorem boundaryPair_group_mem_boundaryFour (pair : BoundaryPair) :
    boundaryToSporadic pair.1 ∈ BoundaryFour := by
  rcases pair with ⟨G, ell⟩
  cases G <;> simp [boundaryToSporadic, BoundaryFour]

/-- The two cited families contain twenty-two and four constructors, and
their union contains all twenty-six constructors of `SporadicGroup`. -/
theorem sporadic_group_inventory :
    CTBlocksTwentyTwo.card = 22 ∧ BoundaryFour.card = 4 ∧
      AllSporadic.card = 26 :=
  ⟨card_CTBlocks_twenty_two, card_boundary_four, card_all_sporadic⟩

/-- The imported computation exposes exactly forty-five distinct boundary
pairs. -/
theorem proposition57_pair_inventory :
    boundaryPairs.length = 45 ∧ boundaryPairs.Nodup :=
  boundary_pairs_exactly_forty_five

/-- Source-shaped form of the final deduction in Theorem 5.1.

`RelevantPrime S ell` represents that `ell` is a prime divisor of the order
of `S`.  The Atlas input is an exact support statement, not an iBAW
conclusion: on the four boundary groups it identifies the relevant primes
with precisely the pairs printed in Proposition 5.7. -/
theorem theorem_5_1_relative
    (RelevantPrime Goal : SporadicGroup → Nat → Prop)
    (ctblocksTwentyTwo :
      ∀ S, S ∈ CTBlocksTwentyTwo →
        ∀ ell, RelevantPrime S ell → Goal S ell)
    (proposition57 :
      ∀ pair, pair ∈ boundaryPairs →
        Goal (boundaryToSporadic pair.1) pair.2)
    (atlasBoundaryPrimeSupport :
      ∀ S, S ∈ BoundaryFour → ∀ ell,
        RelevantPrime S ell ↔
          ∃ G : BoundaryGroup,
            boundaryToSporadic G = S ∧ (G, ell) ∈ boundaryPairs) :
    ∀ S ell, RelevantPrime S ell → Goal S ell := by
  intro S ell hRelevant
  rcases sporadic_coverage S with hCTBlocks | hBoundary
  · exact ctblocksTwentyTwo S hCTBlocks ell hRelevant
  · rcases (atlasBoundaryPrimeSupport S hBoundary ell).mp hRelevant with
      ⟨G, hGS, hPair⟩
    rw [← hGS]
    exact proposition57 (G, ell) hPair

end ModularRep.PaperProofs.SporadicTheorem51AssemblyRelative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
