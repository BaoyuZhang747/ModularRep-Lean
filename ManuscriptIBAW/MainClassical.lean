import ManuscriptIBAW.TypeC.Theorem
import ManuscriptIBAW.TypeB.AllPrimes
import ManuscriptIBAW.MainEvidence

/-!
# Classical groups in the main theorem

Theorem 1.1 includes all finite simple groups of types B and C. The Type B
cases include ranks one and two and even characteristic. In odd
characteristic and rank at least three, the theorem is proved from the
separate source assumptions at each prime.

The data satisfying the inductive condition preserve the covering group,
character fields and complete inductive condition when the simple group is
identified by an isomorphism.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.Main

open ModularRep ModularRep.PaperProofs
open TypeBCurrentCertificate
open OddTwoConformalProjectiveRealisation (PSp)

/-- The Type C source assumptions, at the original rank and field. -/
def TypeCInputs : Type 1 :=
  ∀ (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2)),
    TypeC.TheoremInputs n p F rank notSmall

/-- Subordinate assumptions for type B in odd characteristic in rank at
least three, before the theorem at the specified prime is applied. -/
def TypeBInputs : Type 1 :=
  ∀ (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 3 ≤ n), Odd p → TypeB.OddHighInputs n p F rank

/-- The remaining Type B sources are required only for actual nonabelian
simple groups and primes dividing their orders. -/
def CensusInputs : Type 1 :=
  ∀ (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 1 ≤ n) [IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)],
    (¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)) →
    ∀ prime : Nat.Prime ell,
      ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F) →
        TypeB.Census.SourceInputs n p ell F prime rank

structure ClassicalInputs where
  typeC : TypeCInputs
  typeB : TypeBInputs
  census : CensusInputs

/-- The data for the full inductive condition give the main theorem's conclusion
with the same characters and covering group. -/
theorem of_allPrimeFamily {S : Type} [Group S] (proved : AllPrimeFamily S) :
    AllPrimeMain S := by
  intro ell prime divides
  obtain ⟨certificate⟩ := proved ell prime divides
  exact ⟨MainCertificate.established certificate⟩

theorem typeC_complete (sources : TypeCInputs)
    (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2)) :
    AllPrimeMain (PSp n F) :=
  of_allPrimeFamily (TypeC.all_primes n p F rank notSmall
    (sources n p F rank notSmall))

/-- Combine the cases with the result in higher rank proved from the assumptions
for each case. This is the Type B clause of Theorem 1.1. -/
theorem typeB_complete (sources : ClassicalInputs)
    (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 1 ≤ n) [IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)]
    (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    AllPrimeMain (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  of_allPrimeFamily (TypeB.Census.all_cases n p F rank
    (fun ell prime divides => sources.census n p ell F rank nonabelian prime divides)
    (fun high odd => (sources.typeB n p F high odd).complete))

end ManuscriptIBAW.Main

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
