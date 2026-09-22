import ManuscriptIBAW.TypeC.AllCases
import ManuscriptIBAW.FamilyCertificate

/-!
# The Type C theorem under the stated external assumptions

For each prime dividing the order of the actual simple group, the
numerical case determines the required source data. The theorem applies
the proved case distinction to these data. Its conclusion retains the
complete family on the specified universal prime-to-ell cover.

The external hypotheses remain explicit. This theorem does not construct
the published character theory or the algebraic group interpretations
used by those hypotheses.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep.PaperProofs
open OddTwoConformalProjectiveRealisation (PSp)
open TypeBCurrentCertificate

variable (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
variable (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2))

/-- The source data required at every prime dividing the simple group order. -/
def TheoremInputs : Type 1 :=
  ∀ (ell : ℕ) (prime : Nat.Prime ell), ell ∣ Nat.card (PSp n F) →
    AllCases.SourceInputs n p ell F prime rank notSmall

/-- The complete inductive condition for the actual projective symplectic
group at every relevant prime, conditional on the stated source data. -/
theorem all_primes (sources : TheoremInputs n p F rank notSmall) :
    AllPrimeFamily (PSp n F) := by
  intro ell prime divides
  let D := sources ell prime divides
  let target := AllCases.actualTarget n p ell F prime rank notSmall D
  obtain ⟨witness⟩ := AllCases.full_block_condition_source_instantiated
    n p ell F prime rank notSmall D divides
  exact ⟨⟨target.family, target.cover, target.simpleEquiv, witness⟩⟩

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
