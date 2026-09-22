import ManuscriptIBAW.FamilyCertificate
import ManuscriptIBAW.TypeC.Theorem
import ModularRep.PaperProofs.TypeBCurrentCensus

/-!
# Reduction of the remaining Type B groups to Types A and C

The finite group identifications and the published theorem for PSL2 are
explicit structural and published assumptions. The symplectic case uses the
Type C theorem. The theorem for odd characteristic in rank at least three is
supplied separately and is applied to the same group.

Only the simple group coordinates change under an isomorphism. The covering
group, characters and root convention remain the same.
-/

noncomputable section

namespace ManuscriptIBAW.TypeB.Census

open ModularRep.PaperProofs
open TypeBCurrentCertificate TypeBCurrentCensus
open OddTwoConformalProjectiveRealisation (PSp)

/-- The published rank-one result gives a full covering family. -/
theorem lowRank_complete {ell : ℕ} {F : Type} [Field F] [Finite F]
    {prime : Nat.Prime ell} (D : LowRankInputs ell F prime)
    (divides : ell ∣ Nat.card (PSL2 F)) : Nonempty (FamilyCertificate (PSL2 F) ell) := by
  letI : IsSimpleGroup D.cover.S := D.cover.simple
  have simple : IsSimpleGroup (PSL2 F) := D.base.symm.isSimpleGroup
  have nonabelian : ¬ IsMulCommutative (PSL2 F) := by
    intro commutative
    letI := commutative
    apply D.cover.nonabelian
    refine ⟨⟨fun (x y : D.cover.S) => ?_⟩⟩
    apply D.base.injective
    simp only [map_mul]
    exact mul_comm' (D.base x) (D.base y)
  obtain ⟨witness⟩ := D.published.allBlocks F ell prime D.H D.cover D.base
    D.primitive simple nonabelian divides
  exact ⟨⟨D.primitive.family, D.cover, D.base, witness⟩⟩

/-- The stated finite group isomorphism, with the source assumptions of the Type
C proof at the same rank, field and prime. -/
structure SymplecticInputs (n p ell : ℕ) (F : Type)
    [Field F] [Finite F] [CharP F p] (prime : Nat.Prime ell)
    (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2)) where
  identification : TypeBOrthogonalOmegaCarriers.Omega n F ≃* PSp n F
  source : TypeC.AllCases.SourceInputs n p ell F prime rank notSmall

/-- The numerical case fixes which structural and published assumptions
are required. The higher rank Type B theorem is applied separately. -/
def CaseInputs (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (prime : Nat.Prime ell) (c : CensusCase n p (Nat.card F)) : Type 1 := by
  cases c with
  | rankOne rank =>
      subst n
      exact RankOneInputs ell F prime
  | exceptional rank _ =>
      subst n
      exact TypeBCurrentCensus.ExceptionalInputs ell F prime
  | symplectic rank _ notSmall =>
      exact SymplecticInputs n p ell F prime rank notSmall
  | oddHigher _ _ => exact PUnit

/-- Apply the theorem in the selected case without changing its covering
group or its complete inductive condition. -/
theorem complete_at_case (n p ell : ℕ) (F : Type)
    [Field F] [Finite F] [CharP F p] (prime : Nat.Prime ell)
    (c : CensusCase n p (Nat.card F)) (D : CaseInputs n p ell F prime c)
    (oddHigh : 3 ≤ n → Odd p → AllPrimeFamily (TypeBOrthogonalOmegaCarriers.Omega n F))
    (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    Nonempty (FamilyCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) ell) := by
  cases c with
  | rankOne rank =>
      subst n
      have order := Nat.card_congr D.identification.toEquiv
      obtain ⟨certificate⟩ := lowRank_complete D.lowRank (order ▸ divides)
      exact ⟨certificate.along D.identification.symm⟩
  | exceptional rank fieldTwo =>
      subst n
      have order := Nat.card_congr D.identification.toEquiv
      obtain ⟨certificate⟩ := lowRank_complete D.lowRank (order ▸ divides)
      exact ⟨certificate.along D.identification.symm⟩
  | symplectic rank scope notSmall =>
      let target := TypeC.AllCases.actualTarget n p ell F prime rank notSmall D.source
      have order := Nat.card_congr D.identification.toEquiv
      obtain ⟨witness⟩ := TypeC.AllCases.full_block_condition_source_instantiated
        n p ell F prime rank notSmall D.source (order ▸ divides)
      exact ⟨⟨target.family, target.cover,
        (target.simpleEquiv.trans D.identification.symm), witness⟩⟩
  | oddHigher rank odd => exact oddHigh rank odd ell prime divides

abbrev SourceInputs (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (prime : Nat.Prime ell) (rank : 1 ≤ n) :=
  CaseInputs n p ell F prime (censusCase n p F rank)

/-- The complete condition at every prime in each numerical case. The
higher rank argument remains a theorem parameter at this intermediate step. -/
theorem all_cases (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 1 ≤ n)
    (sources : ∀ ell (prime : Nat.Prime ell),
      ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F) →
        SourceInputs n p ell F prime rank)
    (oddHigh : 3 ≤ n → Odd p → AllPrimeFamily (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    AllPrimeFamily (TypeBOrthogonalOmegaCarriers.Omega n F) := by
  intro ell prime divides
  exact complete_at_case n p ell F prime (censusCase n p F rank)
    (sources ell prime divides) oddHigh divides

/-- Transfer the result along the stated Type B group isomorphism.
The final application supplies the higher rank theorem from its sources. -/
theorem of_presentation {S : Type} [Group S] (P : Presentation S)
    (sources : ∀ ell (prime : Nat.Prime ell),
      ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega P.n P.F) →
        SourceInputs P.n P.p ell P.F prime P.rank)
    (oddHigh : 3 ≤ P.n → Odd P.p →
      AllPrimeFamily (TypeBOrthogonalOmegaCarriers.Omega P.n P.F)) : AllPrimeFamily S :=
  (all_cases P.n P.p P.F P.rank sources oddHigh).along P.identification

end ManuscriptIBAW.TypeB.Census

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
