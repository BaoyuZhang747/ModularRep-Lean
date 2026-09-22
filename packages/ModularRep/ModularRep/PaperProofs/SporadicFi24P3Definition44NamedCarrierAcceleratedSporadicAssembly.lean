import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic
import ModularRep.PaperProofs.SporadicProposition57ComputationRelative

/-! Raw constructions for the named sporadic groups. The full inductive condition additionally requires compatible roots. The main manuscript application uses the stronger certificate and states that requirement explicitly. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly
open Formalisation.DependencyCases
open SporadicProposition57ComputationRelative
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
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

theorem boundary_pair_mem_iff (b : BoundaryGroup) (p : ℕ) :
    (b, p) ∈ boundaryPairs ↔ p ∈ boundaryPrimes b := by
  cases b <;> simp [mem_boundaryPairs_iff, boundaryPrimes]

theorem boundary_name_of_mem (s : SporadicGroup) (h : s ∈ BoundaryFour) :
    ∃ b : BoundaryGroup, boundaryName b = s := by
  simp only [BoundaryFour, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h
  · exact ⟨.j4, h.symm⟩
  · exact ⟨.fi24, h.symm⟩
  · exact ⟨.baby, h.symm⟩
  · exact ⟨.monster, h.symm⟩

-- Fi24Two retains independent row universes inside this input container.
set_option linter.checkUnivs false in
structure ExceptionalInputs (bases : SporadicGroup → NamedBase.{u}) where
  j4 : ∀ p, p ∈ j4Primes →
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4.Inputs (bases .J4) p
  babyTwo :
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo.Inputs (bases .Baby)
  babyOdd : ∀ p, p ∈ babyPrimes → p ≠ 2 →
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd.Inputs (bases .Baby) p
  monsterTwo :
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo.Inputs (bases .Monster)
  monsterOdd : ∀ p, p ∈ monsterPrimes → p ≠ 2 →
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd.Inputs (bases .Monster) p
  fi24Two :
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two.Inputs.{u, v, w} (bases .Fi24Prime)
  fi24Three :
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three.Inputs (bases .Fi24Prime)
  fi24Five :
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five.Inputs (bases .Fi24Prime)
  fi24Seven :
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven.Inputs (bases .Fi24Prime)
  fi24Cyclic : ∀ p, p ∈ ([11, 13, 17, 23, 29] : List ℕ) →
    SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic.Inputs (bases .Fi24Prime) p

def exceptionalResult {bases : SporadicGroup → NamedBase.{u}}
    (I : ExceptionalInputs.{u, v, w} bases)
    (b : BoundaryGroup) (p : ℕ) (hp : p ∈ boundaryPrimes b) :
    {M : CaseModel (bases (boundaryName b)) p // RawCaseConclusion M} := by
  cases b with
  | j4 =>
      exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsJ4.realise (I.j4 p hp)
  | baby =>
      by_cases h : p = 2
      · subst p
        exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo.realise I.babyTwo
      · exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd.realise (I.babyOdd p hp h)
  | monster =>
      by_cases h : p = 2
      · subst p
        exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterTwo.realise I.monsterTwo
      · exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd.realise (I.monsterOdd p hp h)
  | fi24 =>
      by_cases h2 : p = 2
      · subst p
        exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Two.realise I.fi24Two
      by_cases h3 : p = 3
      · subst p
        exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three.realise I.fi24Three
      by_cases h5 : p = 5
      · subst p
        exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five.realise I.fi24Five
      by_cases h7 : p = 7
      · subst p
        exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven.realise I.fi24Seven
      have hc : p ∈ ([11, 13, 17, 23, 29] : List ℕ) := by
        simpa [boundaryPrimes, fi24Primes, h2, h3, h5, h7] using hp
      exact SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic.realise (I.fi24Cyclic p hc)

def proposition57Model {bases : SporadicGroup → NamedBase.{u}}
    (I : ExceptionalInputs.{u, v, w} bases)
    (pair : {pair : BoundaryPair // pair ∈ boundaryPairs}) :
    CaseModel (bases (boundaryName pair.1.1)) pair.1.2 :=
  (exceptionalResult I pair.1.1 pair.1.2
    ((boundary_pair_mem_iff pair.1.1 pair.1.2).mp pair.2)).val

/-- Every one of the forty-five distinct exceptional pairs is derived from the
lower case inputs; no Proposition5.7 hypothesis is supplied. -/
theorem proposition57_from_external_inputs {bases : SporadicGroup → NamedBase.{u}}
    (I : ExceptionalInputs.{u, v, w} bases) :
    boundaryPairs.length = 45 ∧ boundaryPairs.Nodup ∧
      ∀ pair, RawCaseConclusion (proposition57Model I pair) := by
  refine ⟨boundary_pairs_exactly_forty_five.1,
    boundary_pairs_exactly_forty_five.2, ?_⟩
  intro pair
  exact (exceptionalResult I pair.1.1 pair.1.2
    ((boundary_pair_mem_iff pair.1.1 pair.1.2).mp pair.2)).property

/-- The independently published CTBlocks result, bound to actual models and
restricted literally to the twenty-two covered names and their relevant primes. -/
structure PublishedTwentyTwoInputs (bases : SporadicGroup → NamedBase.{u}) where
  models : (c : RelevantCase bases) → c.1 ∈ CTBlocksTwentyTwo →
    CaseModel (bases c.1) c.2.val
  published : ∀ c h, RawCaseConclusion (models c h)

def allResults {bases : SporadicGroup → NamedBase.{u}}
    (I : ExceptionalInputs.{u, v, w} bases)
    (L : PublishedTwentyTwoInputs bases)
    (primeSupport : ∀ b p,
      RelevantPrime (bases (boundaryName b)) p ↔ p ∈ boundaryPrimes b)
    (c : RelevantCase bases) :
    {M : CaseModel (bases c.1) c.2.val // RawCaseConclusion M} := by
  rcases c with ⟨s, ⟨p, hp⟩⟩
  by_cases h22 : s ∈ CTBlocksTwentyTwo
  · exact ⟨L.models ⟨s, ⟨p, hp⟩⟩ h22, L.published ⟨s, ⟨p, hp⟩⟩ h22⟩
  · have h4 := (sporadic_coverage s).resolve_left h22
    let hex := boundary_name_of_mem s h4
    let b := Classical.choose hex
    have hb : boundaryName b = s := Classical.choose_spec hex
    have hp' : RelevantPrime (bases (boundaryName b)) p := by
      simpa only [hb] using hp
    exact Eq.mp
      (congrArg (fun name => {M : CaseModel (bases name) p // RawCaseConclusion M}) hb)
      (exceptionalResult I b p ((primeSupport b p).mp hp'))

def modelsOfInputs {bases : SporadicGroup → NamedBase.{u}}
    (I : ExceptionalInputs.{u, v, w} bases)
    (L : PublishedTwentyTwoInputs bases)
    (primeSupport : ∀ b p,
      RelevantPrime (bases (boundaryName b)) p ↔ p ∈ boundaryPrimes b)
    (c : RelevantCase bases) : CaseModel (bases c.1) c.2.val :=
  (allResults I L primeSupport c).val

/-- The fixed literature-relative sporadic conclusion, with the exceptional
forty-five-pair proof constructed internally and the CTBlocks22 input explicit. -/
theorem sporadic_from_external_inputs {bases : SporadicGroup → NamedBase.{u}}
    (I : ExceptionalInputs.{u, v, w} bases)
    (L : PublishedTwentyTwoInputs bases)
    (primeSupport : ∀ b p,
      RelevantPrime (bases (boundaryName b)) p ↔ p ∈ boundaryPrimes b) :
    RawSporadicConclusion bases (modelsOfInputs I L primeSupport) := by
  intro c
  exact (allResults I L primeSupport c).property

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
