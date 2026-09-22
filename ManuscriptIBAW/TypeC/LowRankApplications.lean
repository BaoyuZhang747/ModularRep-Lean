import ManuscriptIBAW.TypeC.PrincipalApplicationComplete
import ManuscriptIBAW.TypeC.LiLiSource

/-!
# Small rank Type C applications

Proposition 3.5 is proved on the actual Sp4 or PSp4 cover selected by the
coefficient prime. Defining characteristic uses Späth's Theorem C, even
fields use Schaeffer Fry's Theorem 5.5, and every nondefining prime over
an odd field uses Li–Li's Theorem 1.1. Its source for each block and the
separate compatibility of the complete family are explicit.

The Sp6(2) application follows the manuscript: Theorem 5.5 applies at every
odd prime on the actual double cover. Each assumption on a family of
primitive blocks retains its standard coefficient, root and interpretation
of the specified primitive blocks.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation (Sp PSp spProjection)
open ModularRep.PaperProofs.TypeBFullBlockCondition
open ModularRep.PaperProofs.TypeCActualCaseSourceData
  (ActualTarget PrimitiveData DefiningInputs LowEvenInputs)
open ModularRep.PaperProofs.TypeCActualSimpleQuotientCoordinates
open ModularRep.PaperProofs.TypeCActualNumericalCases

local instance lowRankApplicationFintype (G : Type) [Finite G] : Fintype G :=
  Fintype.ofFinite G

section RankTwo

/-- The four numerical branches of the rank two proof. -/
inductive RankTwoCase (p ell q : ℕ) : Type
  | defining (equal : ell = p)
  | evenNondefining (characteristic : p = 2) (fieldLarge : 2 < q)
      (primeNeTwo : ell ≠ 2)
  | oddTwo (fieldOdd : Odd q) (equal : ell = 2) (nondefining : ell ≠ p)
  | oddNondefining (fieldOdd : Odd q) (primeNeTwo : ell ≠ 2)
      (notDvd : ¬ ell ∣ q)

variable (p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
variable (prime : Nat.Prime ell) (fieldLarge : 2 < Nat.card F)

/-- Numerical selection uses the actual characteristic and field order,
with defining characteristic tested first. -/
def rankTwoCase : RankTwoCase p ell (Nat.card F) := by
  classical
  by_cases defining : ell = p
  · exact .defining defining
  by_cases fieldOdd : Odd (Nat.card F)
  · by_cases two : ell = 2
    · exact .oddTwo fieldOdd two defining
    · exact .oddNondefining fieldOdd two (not_dvd_card_of_ne F p ell prime defining)
  · have fieldEven : Even (Nat.card F) := (Nat.even_or_odd _).resolve_right fieldOdd
    have characteristic : p = 2 := characteristic_eq_two_of_even F p fieldEven
    exact .evenNondefining characteristic fieldLarge
      (fun equal => defining (equal.trans characteristic.symm))

/-- Only the source hypotheses for the selected numerical branch are required.
Both odd-field branches use the same Li–Li source at the original prime. -/
def RankTwoSourceInputs (c : RankTwoCase p ell (Nat.card F)) : Type 1 := by
  cases c with
  | defining equal =>
      subst ell
      exact DefiningInputs 2 p F
  | evenNondefining characteristic _ _ =>
      subst p
      exact LowEvenInputs 2 ell F prime
  | oddTwo _ equal _ =>
      subst ell
      exact LiLiSource.Inputs 2 F prime
  | oddNondefining _ _ _ =>
      exact LiLiSource.Inputs ell F prime

/-- The family, cover and PSp4 identification are fixed before applying a
published character theorem. -/
def rankTwoTarget (c : RankTwoCase p ell (Nat.card F))
    (D : RankTwoSourceInputs p ell F prime c) : ActualTarget 2 ell F := by
  cases c with
  | defining equal =>
      subst ell
      exact D.target
  | evenNondefining characteristic _ _ =>
      subst p
      exact D.target
  | oddTwo _ equal _ =>
      subst ell
      exact D.target
  | oddNondefining _ _ _ =>
      exact D.target

/-- The same prime divisor is used in the complete family. Li–Li covers
every nondefining prime over an odd field, including two. -/
theorem rankTwo_complete_at_case (c : RankTwoCase p ell (Nat.card F))
    (D : RankTwoSourceInputs p ell F prime c)
    (divides : ell ∣ Nat.card (PSp 2 F)) :
    Nonempty (FamilyWitness (rankTwoTarget p ell F prime c D).family
      (rankTwoTarget p ell F prime c D).cover) := by
  cases c with
  | defining equal =>
      subst ell
      exact D.complete
  | evenNondefining characteristic large primeNeTwo =>
      subst p
      exact LowEvenInputs.complete 2 ell F prime D (Or.inl rfl) large primeNeTwo
  | oddTwo _ equal nondefining =>
      subst ell
      exact D.complete (not_dvd_card_of_ne F p 2 prime nondefining) divides
  | oddNondefining _ _ notDvd =>
      exact D.complete notDvd divides

/-- The assumptions for Proposition 3.5, over a finite field of order greater
than two and at a specified coefficient prime. -/
abbrev Prop34SourceInputs :=
  RankTwoSourceInputs p ell F prime (rankTwoCase p ell F prime fieldLarge)

/-- The exact target of Proposition 3.5 under its selected source data. -/
def prop34Target (D : Prop34SourceInputs p ell F prime fieldLarge) : ActualTarget 2 ell F :=
  rankTwoTarget p ell F prime (rankTwoCase p ell F prime fieldLarge) D

/-- Conditional Proposition 3.5. Its conclusion contains every block on the
actual selected cover of PSp4(F). -/
theorem prop34_full_block_condition
    (D : Prop34SourceInputs p ell F prime fieldLarge)
    (divides : ell ∣ Nat.card (PSp 2 F)) :
    Nonempty (FamilyWitness (prop34Target p ell F prime fieldLarge D).family
      (prop34Target p ell F prime fieldLarge D).cover) :=
  rankTwo_complete_at_case p ell F prime (rankTwoCase p ell F prime fieldLarge) D divides

/-- The chosen data satisfy the full inductive condition on the specified
family. -/
def prop34FamilyWitness (D : Prop34SourceInputs p ell F prime fieldLarge)
    (divides : ell ∣ Nat.card (PSp 2 F)) :
    FamilyWitness (prop34Target p ell F prime fieldLarge D).family
      (prop34Target p ell F prime fieldLarge D).cover :=
  Classical.choice (prop34_full_block_condition p ell F prime fieldLarge D divides)

end RankTwo

section EvenLowRank

variable (r ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
variable (prime : Nat.Prime ell)

/-- Schaeffer Fry's Theorem 5.5 in the common range q greater than two, with the
full automorphism action and specified projection from Sp. The theorem holds
at every odd prime. Divisibility of the simple group order records the
manuscript's application domain. -/
theorem lowRankEven_all_odd_primes (D : LowEvenInputs r ell F prime)
    (rank : r = 2 ∨ r = 3) (fieldLarge : 2 < Nat.card F) (primeNeTwo : ell ≠ 2)
    (_divides : ell ∣ Nat.card (PSp r F)) :
    Nonempty (FamilyWitness D.target.family D.target.cover) :=
  LowEvenInputs.complete r ell F prime D rank fieldLarge primeNeTwo

end EvenLowRank

section Sp6Two

variable (ell : ℕ) (prime : Nat.Prime ell)

/-- The exceptional double cover and the assumptions for Theorem 5.5 at every
odd prime. No separate result for cyclic defect groups is assumed. -/
structure Sp6TwoOddInputs where
  U : Type
  [groupU : Group U]
  [finiteU : Fintype U]
  projection : U →* ModularRep.PaperProofs.TypeCSp6TwoSourceApplication.SimpleGroup
  facts : ModularRep.PaperProofs.TypeCSp6TwoSourceApplication.FullCoverSource U projection
  primitive : PrimitiveData ell U prime
  source : ModularRep.PaperProofs.TypeCSp6TwoSourceApplication.Theorem55Sp6TwoCertificate

attribute [instance] Sp6TwoOddInputs.groupU Sp6TwoOddInputs.finiteU

namespace Sp6TwoOddInputs

variable {ell prime} (D : Sp6TwoOddInputs ell prime)
variable (F : Type) [Field F] [Finite F]
variable (primeNeTwo : ell ≠ 2) (fieldTwo : Nat.card F = 2)

/-- The covering group is U. The specified coordinates over the field with two
elements identify its simple quotient with PSp6(F). -/
def target : ActualTarget 3 ell F where
  family := D.primitive.family
  cover := ModularRep.PaperProofs.TypeCSp6TwoSourceApplication.actualCover
    D.U D.projection D.facts ell prime primeNeTwo
  simpleEquiv := (twoElementProjectiveEquiv F fieldTwo 3).symm

/-- Apply Theorem 5.5 at every odd prime. The square involving the covering
projection commutes by definition before changing the field coordinates. -/
theorem complete (_divides : ell ∣ Nat.card (PSp 3 F)) :
    Nonempty (FamilyWitness (D.target F primeNeTwo fieldTwo).family
      (D.target F primeNeTwo fieldTwo).cover) :=
  D.source.allBlocks ell D.U D.primitive.k D.primitive.K prime D.projection D.facts
    D.primitive.iota D.primitive.injective D.primitive.blocks D.primitive.localSource
    D.primitive.coefficient
    (ModularRep.PaperProofs.TypeCSp6TwoSourceApplication.actualCover
      D.U D.projection D.facts ell prime primeNeTwo)
    (MulEquiv.refl _) primeNeTwo rfl

@[simp] theorem projection_eq :
    (D.target F primeNeTwo fieldTwo).projection =
      projectionOverTwoElementField F fieldTwo D.projection := rfl

end Sp6TwoOddInputs

/-- The Sp6(2) application preserves the actual original divisor and invokes
Schaeffer Fry at all odd primes through the same cover. -/
theorem sp6Two_all_odd_primes (D : Sp6TwoOddInputs ell prime)
    (F : Type) [Field F] [Finite F] (primeNeTwo : ell ≠ 2) (fieldTwo : Nat.card F = 2)
    (divides : ell ∣ Nat.card (PSp 3 F)) :
    Nonempty (FamilyWitness (D.target F primeNeTwo fieldTwo).family
      (D.target F primeNeTwo fieldTwo).cover) :=
  D.complete F primeNeTwo fieldTwo divides

end Sp6Two

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
