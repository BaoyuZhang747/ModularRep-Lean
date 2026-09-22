import ModularRep.PaperProofs.TypeBCurrentCompletion
import ModularRep.PaperProofs.TypeBCurrentCensus

/-!
# Concrete current Type B census theorem

The final join supplies the odd high-rank branch from the actual current
prime dispatcher. Its source box retains the original finite field, norm,
Clifford projection and each prime's subordinate inputs. The completed
all-prime certificate is a theorem output, never an input field.

Low rank and even characteristic use the exact current census sources.
The two complete certificate presentations, including the exceptional
nine-block one, remain distinct through the same base coordinate.
-/

noncomputable section
-- Consumers use projections; omit unused constructor-injectivity auxiliaries.
set_option genInjectivity false

namespace ModularRep.PaperProofs.TypeBCurrentTheorem

open ModularRep TypeBCliffordCarriers TypeBCurrentCertificate TypeBCurrentCensus

/-- Raw data for the actual odd high-rank dispatcher. Positive exponent
comes from its original finite-field parameters and supplies NeZero f
locally; no extra coefficient or completed branch conclusion is added. -/
structure OddHighInputs (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 3 ≤ n) where
  f : ℕ
  parameters : OddFieldParameters F p f
  [finiteSpecial : Finite (SpecialClifford n F)]
  norm : NormSource n F
  projection : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank norm
  branches :
    letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩;
    ∀ (ell : ℕ) (prime : Nat.Prime ell)
      (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)),
      TypeBCurrentCompletion.Inputs parameters rank norm projection ell prime divides

/-- The source box calls the proved defining/odd/two prime dispatcher. -/
theorem OddHighInputs.complete {n p : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F p] {rank : 3 ≤ n}
    (D : OddHighInputs n p F rank) : AllPrimeIBAW (TypeBOrthogonalOmegaCarriers.Omega n F) := by
  letI : Finite (SpecialClifford n F) := D.finiteSpecial
  letI : NeZero D.f := ⟨Nat.ne_of_gt D.parameters.exponent_pos⟩
  exact TypeBCurrentCompletion.allPrimes D.parameters rank D.norm D.projection D.branches

/-- Every field is numeric-case source data or a raw high-rank context.
There is no AllPrimeIBAW, IBAWCertificate or FamilyWitness input field. -/
structure Inputs {S : Type} [Group S] (P : Presentation S) where
  censusSources : ∀ (ell : ℕ) (prime : Nat.Prime ell),
    ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega P.n P.F) →
      SourceInputs P.n P.p ell P.F prime P.rank
  oddHigh : ∀ rank : 3 ≤ P.n, Odd P.p → OddHighInputs P.n P.p P.F rank

/-- Current Corollary 4.15 on any actual finite simple Type B presentation,
with the odd high-rank theorem supplied internally from its raw sources. -/
theorem finite_simple_typeB {S : Type} [Group S] [IsSimpleGroup S]
    (P : Presentation S) (nonabelian : ¬ IsMulCommutative S) (sources : Inputs P) :
    AllPrimeIBAW S :=
  census_of_presentation P nonabelian sources.censusSources
    (fun rank odd => (sources.oddHigh rank odd).complete)

end ModularRep.PaperProofs.TypeBCurrentTheorem


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
