import ModularRep.PaperProofs.TypeBCurrentCertificate
import ModularRep.PaperProofs.TypeBCurrentPrimeCases
import ModularRep.PaperProofs.TypeCCurrentAllCaseSourceApplication
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Current Type B census through exact finite group identifications

Current Corollary 4.15 uses the odd high-rank theorem, the Type C theorem,
and Feng--Conghui Li--Zhang, J. Algebra 631 (2023), Proposition 4.6, p.297.
The latter covers simple PSL_n(q), PSU_n(q) for n <= 7 at all primes,
including the exceptional PSL2(9). Its source application below uses the
actual universal prime-to-ell cover, not an assumed SL2 full cover.

The low/even structural inputs are actual finite group equivalences from
the same matrix Omega carrier. The exceptional rank-two field-two case
uses its derived convention and maps to PSL2(9), not to nonsimple Sp4(2).
No arbitrary goodness predicate or Type B census conclusion is supplied.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCurrentCensus

open ModularRep
open TypeBCurrentCertificate TypeBCliffordCarriers
open TypeCActualCaseSourceData TypeCActualNumericalCases
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family TypeBFullBlockCondition
open OddTwoConformalProjectiveRealisation (PSp)

/-- The literal matrix special linear group modulo its actual centre. -/
abbrev PSL2 (F : Type) [Field F] :=
  Matrix.SpecialLinearGroup (Fin 2) F ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)

local instance primeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- A specified field of nine elements, including its actual field structure. -/
abbrev FieldNine := GaloisField 3 2

@[simp] theorem fieldNine_card : Nat.card FieldNine = 9 := by
  exact GaloisField.card 3 2 (by decide)

/-- The fixed low-rank published source. Its codomain is the complete
specified primitive FamilyWitness on the supplied actual prime-to-ell
cover of literal PSL2. There is no chosen result relation. -/
structure FLZ2023Proposition46 : Prop where
  allBlocks : ∀ (F : Type) [Field F] [Finite F] (ell : ℕ) (prime : Nat.Prime ell)
      (H : Type) [Group H] [Fintype H]
      (cover : EllPrimeCoverSource ell H) (base : cover.S ≃* PSL2 F)
      (primitive : PrimitiveData ell H prime),
    IsSimpleGroup (PSL2 F) → ¬ IsMulCommutative (PSL2 F) →
    ell ∣ Nat.card (PSL2 F) → Nonempty (FamilyWitness primitive.family cover)

/-- Raw cover, specified local/primitive data and the exact source theorem.
The complete witness is obtained only by the application below. -/
structure LowRankInputs (ell : ℕ) (F : Type) [Field F] (prime : Nat.Prime ell) where
  H : Type
  [groupH : Group H]
  [finiteH : Fintype H]
  cover : EllPrimeCoverSource ell H
  base : cover.S ≃* PSL2 F
  primitive : PrimitiveData ell H prime
  published : FLZ2023Proposition46

attribute [instance] LowRankInputs.groupH LowRankInputs.finiteH

/-- The target PSL2 is simple and nonabelian because it is the specified
simple quotient of the actual cover, not because of a group name. -/
theorem LowRankInputs.complete {ell : ℕ} {F : Type} [Field F] [Finite F]
    {prime : Nat.Prime ell} (D : LowRankInputs ell F prime)
    (divides : ell ∣ Nat.card (PSL2 F)) : Nonempty (IBAWCertificate (PSL2 F) ell) := by
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
  exact ⟨.family D.primitive.family D.cover D.base witness⟩

/-- Numeric census alternatives, with exact structural scope guards. -/
inductive CensusCase (n p q : ℕ) : Type
  | rankOne (rank : n = 1)
  | exceptional (rank : n = 2) (fieldTwo : q = 2)
  | symplectic (rank : 2 ≤ n) (scope : p = 2 ∨ n = 2)
      (notSmall : ¬ (n = 2 ∧ q = 2))
  | oddHigher (rank : 3 ≤ n) (odd : Odd p)

/-- Pure arithmetic, applied to the actual characteristic and field order. -/
def censusCase (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 1 ≤ n) : CensusCase n p (Nat.card F) := by
  classical
  by_cases one : n = 1
  · exact .rankOne one
  by_cases two : n = 2
  · by_cases small : Nat.card F = 2
    · exact .exceptional two small
    · exact .symplectic (by omega) (Or.inr two) (fun h => small h.2)
  by_cases characteristic : p = 2
  · exact .symplectic (by omega) (Or.inl characteristic) (fun h => two h.1)
  · exact .oddHigher (by omega) ((characteristic_prime F p).odd_of_ne_two characteristic)

/-- A positive exponent for the root's odd high-rank theorem is derived
from the original finite field instead of being a census assumption. -/
theorem odd_parameters (p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (odd : Odd p) : ∃ f : ℕ, OddFieldParameters F p f := by
  obtain ⟨f, positive, order⟩ := card_prime_power F p
  exact ⟨f, characteristic_prime F p, odd, positive, order⟩

/-- E1/U B1=A1 identification of the same derived matrix Omega carrier.
It is used only when the original group is simple and nonabelian. -/
structure RankOneInputs (ell : ℕ) (F : Type) [Field F] (prime : Nat.Prime ell) where
  identification : TypeBOrthogonalOmegaCarriers.Omega 1 F ≃* PSL2 F
  lowRank : LowRankInputs ell F prime

/-- E1/U identification of B2(2)' with PSL2(9), including the derived
convention of the actual Omega matrices in characteristic two. -/
structure ExceptionalInputs (ell : ℕ) (F : Type) [Field F] (prime : Nat.Prime ell) where
  identification : TypeBOrthogonalOmegaCarriers.Omega 2 F ≃* PSL2 FieldNine
  lowRank : LowRankInputs ell FieldNine prime

/-- E1/U B=C identification of the same actual finite matrix group, with
the existing current Type C source input on its computed family/cover. -/
structure SymplecticInputs (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (prime : Nat.Prime ell) (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2)) where
  identification : TypeBOrthogonalOmegaCarriers.Omega n F ≃* PSp n F
  source : TypeCCurrentAllCaseSourceApplication.SourceInputs n p ell F prime rank notSmall

/-- Only the numeric branch's specific source data are requested. The
odd high-rank branch uses the separately proved theorem supplied below. -/
def CaseInputs (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (prime : Nat.Prime ell) (c : CensusCase n p (Nat.card F)) : Type 1 := by
  cases c with
  | rankOne rank =>
      subst n
      exact RankOneInputs ell F prime
  | exceptional rank _ =>
      subst n
      exact ExceptionalInputs ell F prime
  | symplectic rank _ notSmall =>
      exact SymplecticInputs n p ell F prime rank notSmall
  | oddHigher _ _ => exact PUnit

/-- The prior odd-high theorem is a fixed complete iBAW certificate on the
same Omega carrier. It is a theorem argument, not an external census source
and not a freely chosen notion of goodness. -/
theorem complete_at_case (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (prime : Nat.Prime ell) (c : CensusCase n p (Nat.card F))
    (D : CaseInputs n p ell F prime c)
    (oddHigh : 3 ≤ n → Odd p → AllPrimeIBAW (TypeBOrthogonalOmegaCarriers.Omega n F))
    (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    Nonempty (IBAWCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) ell) := by
  cases c with
  | rankOne rank =>
      subst n
      have order := Nat.card_congr D.identification.toEquiv
      obtain ⟨certificate⟩ := D.lowRank.complete (order ▸ divides)
      exact ⟨certificate.along D.identification.symm⟩
  | exceptional rank fieldTwo =>
      subst n
      have order := Nat.card_congr D.identification.toEquiv
      obtain ⟨certificate⟩ := D.lowRank.complete (order ▸ divides)
      exact ⟨certificate.along D.identification.symm⟩
  | symplectic rank scope notSmall =>
      let target := TypeCCurrentAllCaseSourceApplication.actualTarget
        n p ell F prime rank notSmall D.source
      have order := Nat.card_congr D.identification.toEquiv
      obtain ⟨witness⟩ := TypeCCurrentAllCaseSourceApplication.full_block_condition_source_instantiated
        n p ell F prime rank notSmall D.source (order ▸ divides)
      exact ⟨.family target.family target.cover
        (target.simpleEquiv.trans D.identification.symm) witness⟩
  | oddHigher rank odd => exact oddHigh rank odd ell prime divides

abbrev SourceInputs (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (prime : Nat.Prime ell) (rank : 1 ≤ n) :=
  CaseInputs n p ell F prime (censusCase n p F rank)

/-- Current census construction on the actual simple group. Each low/even
branch invokes a fixed complete source application; the high-rank branch
uses the separately proved current theorem on this same original group. -/
theorem census (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 1 ≤ n) [IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)]
    (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F))
    (sources : ∀ ell (prime : Nat.Prime ell),
      ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F) →
        SourceInputs n p ell F prime rank)
    (oddHigh : 3 ≤ n → Odd p → AllPrimeIBAW (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    AllPrimeIBAW (TypeBOrthogonalOmegaCarriers.Omega n F) := by
  intro ell prime divides
  exact complete_at_case n p ell F prime (censusCase n p F rank)
    (sources ell prime divides) oddHigh divides

/-- E1/U presentation of a finite simple group of type B by the same
explicit matrix model. This is group data, not an iBAW premise. -/
structure Presentation (S : Type) [Group S] where
  n : ℕ
  p : ℕ
  F : Type
  [fieldF : Field F]
  [finiteF : Finite F]
  [charF : CharP F p]
  rank : 1 ≤ n
  identification : TypeBOrthogonalOmegaCarriers.Omega n F ≃* S

attribute [instance] Presentation.fieldF Presentation.finiteF Presentation.charF

/-- Census for a finite simple group supplied through its actual Type B
presentation. Only the group coordinate is transported; both complete
certificate presentations retain their original roots and covers. -/
theorem census_of_presentation {S : Type} [Group S] [IsSimpleGroup S]
    (P : Presentation S) (nonabelian : ¬ IsMulCommutative S)
    (sources : ∀ ell (prime : Nat.Prime ell),
      ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega P.n P.F) →
        SourceInputs P.n P.p ell P.F prime P.rank)
    (oddHigh : 3 ≤ P.n → Odd P.p →
      AllPrimeIBAW (TypeBOrthogonalOmegaCarriers.Omega P.n P.F)) : AllPrimeIBAW S := by
  letI : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega P.n P.F) :=
    P.identification.isSimpleGroup
  have matrixNonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega P.n P.F) := by
    intro commutative
    letI := commutative
    apply nonabelian
    refine ⟨⟨fun (x y : S) => ?_⟩⟩
    apply P.identification.symm.injective
    simp only [map_mul]
    exact mul_comm' (P.identification.symm x) (P.identification.symm y)
  exact AllPrimeIBAW.along P.identification
    (census P.n P.p P.F P.rank matrixNonabelian sources oddHigh)

end ModularRep.PaperProofs.TypeBCurrentCensus



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
