import ManuscriptIBAW.FamilyCertificate
import ManuscriptIBAW.TypeB.Defining
import ManuscriptIBAW.TypeB.OddInputs
import ManuscriptIBAW.TypeB.TwoApplication
import ManuscriptIBAW.TypeB.ExceptionalApplication
import ManuscriptIBAW.TypeB.Census
import ModularRep.PaperProofs.TypeBCurrentPrimeCases

/-!
# The Type B theorem in all prime cases

The prime cases are determined from the original finite field, rank and
prime divisor. Each case applies its proof on the specified covering group.
At the prime two, the natural quotient criteria for the nine blocks of
Omega7(3) are interpreted on the common covering family. The final
certificate contains its full family witness.

The final theorem constructs the higher rank result from the source
assumptions of its prime cases. The reduction of the remaining groups uses
the Type C proof and the stated theorem for PSL2.
-/

noncomputable section

set_option genInjectivity false
set_option genSizeOfSpec false

namespace ManuscriptIBAW.TypeB.AllPrimes

open ModularRep.PaperProofs
open TypeBCliffordCarriers TypeBCurrentCertificate

variable {n p f ell : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
variable [Finite (SpecialClifford n F)] [NeZero f]
variable (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
variable (N : NormSource n F)
variable (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)

local instance allPrimesSpinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

/-- The subordinate assumptions required in each applicable prime case.
No complete inductive condition is a field of this structure. -/
structure Inputs (ell : ℕ) (prime : Nat.Prime ell)
    (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)) where
  defining : ell = p → Defining.SourceInputs parameters rank N C
  odd : ∀ odd : Odd ell, ∀ nondefining : ¬ ell ∣ Nat.card F,
    OddInputs.Inputs parameters rank N C ell odd nondefining divides
  twoGeneric : ell = 2 → (n, Nat.card F) ≠ (3, 3) →
    TwoApplication.Inputs parameters rank N C
  twoExceptional : ell = 2 → (n, Nat.card F) = (3, 3) →
    Exceptional.Inputs (TypeBOrthogonalOmegaCarriers.Omega n F)

/-- The two covering cases at the prime two. -/
theorem prime_two
    (generic : (n, Nat.card F) ≠ (3, 3) → TwoApplication.Inputs parameters rank N C)
    (exceptional : (n, Nat.card F) = (3, 3) →
      Exceptional.Inputs (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    Nonempty (FamilyCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) 2) := by
  classical
  by_cases same : (n, Nat.card F) = (3, 3)
  · exact (exceptional same).complete
  · let D := generic same
    obtain ⟨witness⟩ := D.complete same
    exact ⟨⟨D.family, D.cover, (MulEquiv.refl _), witness⟩⟩

/-- Apply the proof for each prime case on the same matrix Omega group. -/
theorem complete (prime : Nat.Prime ell)
    (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F))
    (D : Inputs parameters rank N C ell prime divides) :
    Nonempty (FamilyCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) ell) := by
  classical
  cases TypeBCurrentPrimeCases.classify parameters n prime with
  | defining same =>
      subst ell
      exact Defining.complete parameters rank N C (D.defining rfl)
  | oddNondefining odd different nondefining coverCases exceptionalNondefining =>
      exact (D.odd odd nondefining).complete
  | twoGeneric same nondefining generic =>
      subst ell
      let source := D.twoGeneric rfl generic
      obtain ⟨witness⟩ := source.complete generic
      exact ⟨⟨source.family, source.cover, (MulEquiv.refl _), witness⟩⟩
  | twoExceptional same nondefining exceptional definingPrime exponent =>
      subst ell
      exact (D.twoExceptional rfl exceptional).complete

/-- The complete condition at every prime dividing the original group order. -/
theorem all_primes
    (sources : ∀ (ell : ℕ) (prime : Nat.Prime ell)
      (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)),
      Inputs parameters rank N C ell prime divides) :
    AllPrimeFamily (TypeBOrthogonalOmegaCarriers.Omega n F) := by
  intro ell prime divides
  exact complete parameters rank N C prime divides (sources ell prime divides)

end ManuscriptIBAW.TypeB.AllPrimes

namespace ManuscriptIBAW.TypeB

open ModularRep.PaperProofs
open TypeBCliffordCarriers TypeBCurrentCertificate

/-- Structural assumptions and prime case sources for the same finite field.
The positive exponent supplies the nonzero exponent needed in the field action. -/
structure OddHighInputs (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 3 ≤ n) where
  f : ℕ
  parameters : OddFieldParameters F p f
  [finiteSpecial : Finite (SpecialClifford n F)]
  norm : NormSource n F
  projection : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank norm
  branches :
    letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
    ∀ (ell : ℕ) (prime : Nat.Prime ell)
      (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)),
      AllPrimes.Inputs parameters rank norm projection ell prime divides

/-- The higher rank theorem follows from the prime case proofs. -/
theorem OddHighInputs.complete {n p : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F p] {rank : 3 ≤ n}
    (D : OddHighInputs n p F rank) :
    AllPrimeFamily (TypeBOrthogonalOmegaCarriers.Omega n F) := by
  letI : Finite (SpecialClifford n F) := D.finiteSpecial
  letI : NeZero D.f := ⟨Nat.ne_of_gt D.parameters.exponent_pos⟩
  exact AllPrimes.all_primes D.parameters rank D.norm D.projection D.branches

/-- The source assumptions for a specified Type B presentation.
Both the higher rank theorem and the remaining cases are proved below. -/
structure TheoremInputs {S : Type} [Group S] (P : TypeBCurrentCensus.Presentation S) where
  remaining : ∀ (ell : ℕ) (prime : Nat.Prime ell),
    ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega P.n P.F) →
      Census.SourceInputs P.n P.p ell P.F prime P.rank
  oddHigh : ∀ rank : 3 ≤ P.n, Odd P.p → OddHighInputs P.n P.p P.F rank

/-- Every finite simple Type B presentation has the complete inductive
condition at every relevant prime, under the stated external assumptions. -/
theorem finite_simple_typeB {S : Type} [Group S] [IsSimpleGroup S]
    (P : TypeBCurrentCensus.Presentation S) (_nonabelian : ¬ IsMulCommutative S)
    (sources : TheoremInputs P) : AllPrimeFamily S :=
  Census.of_presentation P sources.remaining
    (fun rank odd => (sources.oddHigh rank odd).complete)

end ManuscriptIBAW.TypeB

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
