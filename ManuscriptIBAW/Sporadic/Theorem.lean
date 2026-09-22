import ManuscriptIBAW.Sporadic.Common
import ManuscriptIBAW.Sporadic.J4
import ManuscriptIBAW.Sporadic.Fi24Two
import ManuscriptIBAW.Sporadic.Fi24Three
import ManuscriptIBAW.Sporadic.Fi24Five
import ManuscriptIBAW.Sporadic.Fi24Seven
import ManuscriptIBAW.Sporadic.Fi24Cyclic
import ManuscriptIBAW.Sporadic.BabyApplication
import ManuscriptIBAW.Sporadic.MonsterApplication
import ModularRep.PaperProofs.SporadicProposition57ComputationRelative

/-!
# Theorem 5.1 for the 26 sporadic groups

The applications at each prime construct the four families in Proposition
5.4. For the other 22 sporadic groups, we assume the inductive condition
recorded as established in the CTBlocks 0.9.5 overview, together with its
interpretation in the specified models. This interpretation includes
compatible roots for extension and intermediate block witnesses and is not
supplied by the overview. The assumption is restricted to those groups and
primes dividing their orders. Its blockwise conclusion is distinct from the
An–Dietrich theorem for whole character sets.

Each model has its own root correspondence, block operations, universal
prime-to-p cover and isomorphism to the named simple group. The source data
and actual prime divisibility determine the model before the proof of the
complete inductive condition.

The interpretations of the named groups, tables and published results remain
explicit assumptions. The proof verifies finite coverage of all 26 names and
the 45 pairs in the four families.
-/

noncomputable section

namespace ManuscriptIBAW.Sporadic.Theorem

open Formalisation.DependencyCases
open ModularRep.PaperProofs.SporadicProposition57ComputationRelative
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

universe u v w

def boundaryName : BoundaryGroup → SporadicGroup
  | .j4 => .J4
  | .fi24 => .Fi24Prime
  | .baby => .Baby
  | .monster => .Monster

def boundaryPrimes : BoundaryGroup → List ℕ
  | .j4 => j4Primes
  | .fi24 => fi24Primes
  | .baby => babyPrimes
  | .monster => monsterPrimes

theorem boundary_name_of_mem (s : SporadicGroup) (h : s ∈ BoundaryFour) :
    ∃ b, boundaryName b = s := by
  simp only [BoundaryFour, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h
  · exact ⟨.j4, h.symm⟩
  · exact ⟨.fi24, h.symm⟩
  · exact ⟨.baby, h.symm⟩
  · exact ⟨.monster, h.symm⟩

set_option linter.checkUnivs false in
/-- The applications from the stated assumptions for the four boundary groups. -/
structure BoundaryInputs (bases : SporadicGroup → NamedBase.{u}) where
  j4 : ∀ p, p ∈ j4Primes → J4.Inputs (bases .J4) p
  fi24Two : Fi24Two.Inputs.{u, v, w} (bases .Fi24Prime)
  fi24Three : Fi24Three.Inputs (bases .Fi24Prime)
  fi24Five : Fi24Five.Inputs (bases .Fi24Prime)
  fi24Seven : Fi24Seven.Inputs (bases .Fi24Prime)
  fi24Cyclic : ∀ p, p ∈ [11, 13, 17, 23, 29] → Fi24Cyclic.Inputs (bases .Fi24Prime) p
  babyTwo : BabyTwo.Inputs (bases .Baby)
  babyOdd : ∀ p, p ∈ babyPrimes → p ≠ 2 → BabyOdd.Inputs (bases .Baby) p
  monsterTwo : MonsterTwo.Inputs (bases .Monster)
  monsterOdd : ∀ p, p ∈ monsterPrimes → p ≠ 2 → MonsterOdd.Inputs (bases .Monster) p

namespace BoundaryInputs

variable {bases : SporadicGroup → NamedBase.{u}} (I : BoundaryInputs.{u, v, w} bases)

def model (b : BoundaryGroup) (p : ℕ) (hp : p ∈ boundaryPrimes b) :
    CaseModel (bases (boundaryName b)) p := by
  cases b with
  | j4 => exact (I.j4 p hp).model
  | baby =>
    by_cases h2 : p = 2
    · subst p; exact BabyTwo.model I.babyTwo
    · exact BabyOdd.model (I.babyOdd p hp h2)
  | monster =>
    by_cases h2 : p = 2
    · subst p; exact MonsterTwo.model I.monsterTwo
    · exact MonsterOdd.model (I.monsterOdd p hp h2)
  | fi24 =>
    by_cases h2 : p = 2
    · subst p; exact I.fi24Two.model
    by_cases h3 : p = 3
    · subst p; exact I.fi24Three.model
    by_cases h5 : p = 5
    · subst p; exact Fi24Five.Inputs.model I.fi24Five
    by_cases h7 : p = 7
    · subst p; exact Fi24Seven.Inputs.model I.fi24Seven
    · exact Fi24Cyclic.Inputs.model (I.fi24Cyclic p (by
        simpa [boundaryPrimes, fi24Primes, h2, h3, h5, h7] using hp))

theorem complete (b : BoundaryGroup) (p : ℕ) (hp : p ∈ boundaryPrimes b) :
    CaseConclusion (I.model b p hp) := by
  cases b with
  | j4 => exact (I.j4 p hp).complete
  | baby =>
    by_cases h2 : p = 2
    · subst p; simpa [model, boundaryName, BabyTwo.target] using BabyTwo.complete I.babyTwo
    · simpa [model, boundaryName, BabyOdd.target, h2] using BabyOdd.complete (I.babyOdd p hp h2)
  | monster =>
    by_cases h2 : p = 2
    · subst p; simpa [model, boundaryName, MonsterTwo.target] using MonsterTwo.complete I.monsterTwo
    · simpa [model, boundaryName, MonsterOdd.target, h2] using MonsterOdd.complete (I.monsterOdd p hp h2)
  | fi24 =>
    by_cases h2 : p = 2
    · subst p; simpa [model, boundaryName] using I.fi24Two.complete
    by_cases h3 : p = 3
    · subst p; simpa [model, boundaryName] using I.fi24Three.complete
    by_cases h5 : p = 5
    · subst p; simpa [model, boundaryName] using Fi24Five.Inputs.complete I.fi24Five
    by_cases h7 : p = 7
    · subst p; simpa [model, boundaryName] using Fi24Seven.Inputs.complete I.fi24Seven
    · simpa [model, boundaryName, h2, h3, h5, h7] using
        Fi24Cyclic.Inputs.complete (I.fi24Cyclic p (by
          simpa [boundaryPrimes, fi24Primes, h2, h3, h5, h7] using hp))

/-- Proposition 5.4 on all 45 distinct boundary pairs. -/
theorem proposition_5_4 :
    boundaryPairs.length = 45 ∧ boundaryPairs.Nodup ∧
      ∀ (b : BoundaryGroup) (p : ℕ) (hp : p ∈ boundaryPrimes b),
        CaseConclusion (I.model b p hp) :=
  ⟨boundary_pairs_exactly_forty_five.1,
    boundary_pairs_exactly_forty_five.2, I.complete⟩

end BoundaryInputs

/-- External inputs for the twenty-two sporadic groups whose inductive condition
is recorded as established in the CTBlocks overview. The input also includes
the interpretation of those results in the selected models, with compatible
roots for the extension and intermediate block witnesses. These formal
interpretations are not supplied by the overview. -/
structure PublishedTwentyTwoInputs (bases : SporadicGroup → NamedBase.{u}) where
  models : (c : RelevantCase bases) → c.1 ∈ CTBlocksTwentyTwo →
    CaseModel (bases c.1) c.2.val
  published : ∀ c h, CaseConclusion (models c h)

set_option linter.checkUnivs false in
structure Inputs (bases : SporadicGroup → NamedBase.{u}) where
  boundary : BoundaryInputs.{u, v, w} bases
  twentyTwo : PublishedTwentyTwoInputs bases
  primeSupport : ∀ b p,
    RelevantPrime (bases (boundaryName b)) p ↔ p ∈ boundaryPrimes b

namespace Inputs

variable {bases : SporadicGroup → NamedBase.{u}} (I : Inputs.{u, v, w} bases)

inductive Route (c : RelevantCase bases) where
  | published (h : c.1 ∈ CTBlocksTwentyTwo)
  | boundary (b : BoundaryGroup) (name_eq : boundaryName b = c.1)
      (prime_mem : c.2.val ∈ boundaryPrimes b)

def route (c : RelevantCase bases) : Route c := by
  by_cases h22 : c.1 ∈ CTBlocksTwentyTwo
  · exact .published h22
  · have h4 := (sporadic_coverage c.1).resolve_left h22
    let b := Classical.choose (boundary_name_of_mem c.1 h4)
    have hb : boundaryName b = c.1 := Classical.choose_spec (boundary_name_of_mem c.1 h4)
    exact .boundary b hb ((I.primeSupport b c.2.val).mp (by simpa only [hb] using c.2.property))

def modelOfRoute (c : RelevantCase bases) (r : Route c) :
    CaseModel (bases c.1) c.2.val :=
  match r with
  | .published h => I.twentyTwo.models c h
  | .boundary b e hp =>
    cast (congrArg (fun s => CaseModel (bases s) c.2.val) e)
      (I.boundary.model b c.2.val hp)

theorem completeOfRoute (c : RelevantCase bases) (r : Route c) :
    CaseConclusion (I.modelOfRoute c r) := by
  cases r with
  | published h => exact I.twentyTwo.published c h
  | boundary b e hp =>
    rcases c with ⟨s, p, hprime⟩
    dsimp at e
    subst s
    change CaseConclusion (I.boundary.model b p hp)
    exact I.boundary.complete b p hp

def models (c : RelevantCase bases) : CaseModel (bases c.1) c.2.val :=
  I.modelOfRoute c (I.route c)

theorem case_complete (c : RelevantCase bases) : CaseConclusion (I.models c) :=
  I.completeOfRoute c (I.route c)

/-- Theorem 5.1, with every cover and block family fixed first. -/
theorem complete : SporadicConclusion bases I.models := I.case_complete

end Inputs

export Formalisation.DependencyCases
  (card_all_sporadic card_CTBlocks_twenty_two card_boundary_four)
export ModularRep.PaperProofs.SporadicProposition57ComputationRelative
  (boundary_pairs_exactly_forty_five)

end ManuscriptIBAW.Sporadic.Theorem

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
