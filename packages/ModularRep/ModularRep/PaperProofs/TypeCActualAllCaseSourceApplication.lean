import ModularRep.PaperProofs.TypeCActualCaseSourceData

/-!
# Actual all-case Type C source application

The numerical selector is defining-first and depends only on the actual
field/rank/prime. Its dependent input type contains only the corresponding
existing endpoint's E1/E2 data. The family, cover and actual PSp coordinate
are computed before a complete witness is obtained from that endpoint.

The conclusion remains conditional on those authenticated sources. It is
the fixed complete family condition, not an abstract Inputs Verified gate.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCActualAllCaseSourceApplication

open ModularRep
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family TypeBFullBlockCondition
open OddTwoConformalProjectiveRealisation (PSp)
open TypeCActualNumericalCases TypeCActualCaseSourceData

variable (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
variable (prime : Nat.Prime ell)

/-- Only the selected numerical branch's existing source arguments.
Equality elimination changes indices, never a character or root choice. -/
def CaseInputs (c : NumericalCase n p ell (Nat.card F)) : Type 1 := by
  cases c with
  | defining equal =>
      subst ell
      exact DefiningInputs n p F
  | oddTwo _ equal _ _ =>
      subst ell
      exact OddTwoInputs n p F
  | rankTwoEven _ characteristic _ _ _ _ _ =>
      subst p
      exact LowEvenInputs n ell F prime
  | rankTwoOdd rank _ _ _ _ =>
      subst n
      exact RankTwoOddInputs ell F prime
  | oddHigherRank _ _ _ _ _ =>
      exact HigherOddInputs n ell F
  | sp6Two rank _ _ _ _ _ =>
      subst n
      exact Sp6TwoInputs ell prime
  | rankThreeEven _ characteristic _ _ _ _ _ =>
      subst p
      exact LowEvenInputs n ell F prime
  | evenHigherRank _ _ _ _ _ _ =>
      exact HigherEvenInputs n ell F

/-- Target data are computed without reading a complete endpoint output. -/
def target (c : NumericalCase n p ell (Nat.card F))
    (D : CaseInputs n p ell F prime c) : ActualTarget n ell F := by
  cases c with
  | defining equal =>
      subst ell
      exact DefiningInputs.target n p F D
  | oddTwo _ equal _ _ =>
      subst ell
      exact OddTwoInputs.target n p F D
  | rankTwoEven _ characteristic _ _ _ _ _ =>
      subst p
      exact LowEvenInputs.target n ell F prime D
  | rankTwoOdd rank _ odd _ _ =>
      subst n
      exact RankTwoOddInputs.target ell F prime D (by intro h; obtain ⟨k, hk⟩ := odd; omega)
  | oddHigherRank _ _ _ _ _ =>
      exact HigherOddInputs.target n ell F D
  | sp6Two rank characteristic fieldTwo _ nondefining _ =>
      subst n
      exact Sp6TwoInputs.target ell prime D F
        (fun h => nondefining (h.trans characteristic.symm)) fieldTwo
  | rankThreeEven _ characteristic _ _ _ _ _ =>
      subst p
      exact LowEvenInputs.target n ell F prime D
  | evenHigherRank _ _ _ _ _ _ =>
      exact HigherEvenInputs.target n ell F D

/-- Each branch invokes its existing source application on exactly the
previously computed family and cover. The original divisor is retained. -/
theorem complete_at_case (c : NumericalCase n p ell (Nat.card F))
    (D : CaseInputs n p ell F prime c) (divides : ell ∣ Nat.card (PSp n F)) :
    Nonempty (FamilyWitness (target n p ell F prime c D).family
      (target n p ell F prime c D).cover) := by
  cases c with
  | defining equal =>
      subst ell
      exact DefiningInputs.complete n p F D
  | oddTwo _ equal _ _ =>
      subst ell
      exact OddTwoInputs.complete n p F D
  | rankTwoEven rank characteristic _ large _ nondefining _ =>
      subst p
      exact LowEvenInputs.complete n ell F prime D (Or.inl rank) large nondefining
  | rankTwoOdd rank _ odd _ notDvd =>
      subst n
      exact RankTwoOddInputs.complete ell F prime D
        (by intro h; obtain ⟨k, hk⟩ := odd; omega) divides notDvd
  | oddHigherRank _ _ _ _ _ =>
      exact HigherOddInputs.complete n ell F D
  | sp6Two rank characteristic fieldTwo _ nondefining _ =>
      subst n
      exact Sp6TwoInputs.complete ell prime D F
        (fun h => nondefining (h.trans characteristic.symm)) fieldTwo divides
  | rankThreeEven rank characteristic _ large _ nondefining _ =>
      subst p
      exact LowEvenInputs.complete n ell F prime D (Or.inr rank) large nondefining
  | evenHigherRank rank _ _ _ _ _ =>
      exact HigherEvenInputs.complete n ell F D rank

variable (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2))

/-- The final source input type is fixed by the actual numerical selector. -/
abbrev SourceInputs :=
  CaseInputs n p ell F prime (numericalCase n p ell F prime rank notSmall)

/-- The actual family/cover/simple-group coordinates precede any theorem output. -/
def actualTarget (D : SourceInputs n p ell F prime rank notSmall) : ActualTarget n ell F :=
  target n p ell F prime (numericalCase n p ell F prime rank notSmall) D

/-- Exact conditional complete Type C application at all allowed numerical
parameters. The source input has no branch conclusion or witness field. -/
theorem full_block_condition_source_instantiated
    (D : SourceInputs n p ell F prime rank notSmall)
    (divides : ell ∣ Nat.card (PSp n F)) :
    Nonempty (FamilyWitness (actualTarget n p ell F prime rank notSmall D).family
      (actualTarget n p ell F prime rank notSmall D).cover) :=
  complete_at_case n p ell F prime (numericalCase n p ell F prime rank notSmall) D divides

/-- Choose only after the complete source-instantiated result is proved. -/
def familyWitness (D : SourceInputs n p ell F prime rank notSmall)
    (divides : ell ∣ Nat.card (PSp n F)) :
    FamilyWitness (actualTarget n p ell F prime rank notSmall D).family
      (actualTarget n p ell F prime rank notSmall D).cover :=
  Classical.choice
    (full_block_condition_source_instantiated n p ell F prime rank notSmall D divides)

/-- The final map is the actual cover projection in the computed PSp coordinates. -/
def typeCProjection (D : SourceInputs n p ell F prime rank notSmall) :
    (actualTarget n p ell F prime rank notSmall D).family.H →* PSp n F :=
  (actualTarget n p ell F prime rank notSmall D).projection

theorem typeCProjection_square (D : SourceInputs n p ell F prime rank notSmall) :
    typeCProjection n p ell F prime rank notSmall D =
      (actualTarget n p ell F prime rank notSmall D).simpleEquiv.toMonoidHom.comp
        (actualTarget n p ell F prime rank notSmall D).cover.quotient := rfl

end ModularRep.PaperProofs.TypeCActualAllCaseSourceApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
