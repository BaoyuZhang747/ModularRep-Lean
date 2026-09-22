import ManuscriptIBAW.TypeC.LowRankApplications
import ManuscriptIBAW.TypeC.LiLiSource
import ManuscriptIBAW.TypeC.HigherOddApplication
import ManuscriptIBAW.TypeC.HigherEvenApplication

/-!
# The Type C theorem in all numerical cases

The case distinction depends only on the actual field order, characteristic,
rank and coefficient prime. Each case fixes its cover and character data
before a published theorem or a conditional deduction is applied.

The hypotheses of the literature used in a case remain explicit. In
particular, this theorem does not assert that those hypotheses have all been
constructed from general Lean representation theory.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC.AllCases

open ModularRep ModularRep.PaperProofs
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family TypeBFullBlockCondition
open OddTwoConformalProjectiveRealisation (PSp)
open TypeCActualNumericalCases TypeCActualCaseSourceData

variable (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
variable (prime : Nat.Prime ell)

/-- The hypotheses depend on the numerical case. Rank two in odd
characteristic uses Li–Li at every nondefining prime. The remaining cases
use the manuscript's conditional higher rank arguments or the applicable
published results in small rank and defining characteristic. -/
def CaseInputs (c : NumericalCase n p ell (Nat.card F)) : Type 1 := by
  cases c with
  | defining equal =>
      subst ell
      exact DefiningInputs n p F
  | oddTwo _ equal _ _ =>
      subst ell
      exact if n = 2 then LiLiSource.Inputs 2 F prime else OddTwoApplicationInputs n p F
  | rankTwoEven _ characteristic _ _ _ _ _ =>
      subst p
      exact LowEvenInputs n ell F prime
  | rankTwoOdd rank _ _ _ _ =>
      subst n
      exact LiLiSource.Inputs ell F prime
  | oddHigherRank _ _ _ _ _ =>
      exact HigherOddInputs n ell F
  | sp6Two rank _ _ _ _ _ =>
      subst n
      exact Sp6TwoOddInputs ell prime
  | rankThreeEven _ characteristic _ _ _ _ _ =>
      subst p
      exact LowEvenInputs n ell F prime
  | evenHigherRank _ _ _ _ _ _ =>
      exact HigherEvenApplicationInputs n ell F

/-- The family, cover and simple group identification are fixed before applying
the theorem for the selected case. -/
def target (c : NumericalCase n p ell (Nat.card F))
    (D : CaseInputs n p ell F prime c) : ActualTarget n ell F := by
  cases c with
  | defining equal =>
      subst ell
      exact DefiningInputs.target n p F D
  | oddTwo _ equal _ _ =>
      subst ell
      by_cases rankTwo : n = 2
      · subst n
        exact (show LiLiSource.Inputs 2 F prime from D).target
      · let inputs : OddTwoApplicationInputs n p F := by
          simpa only [CaseInputs, if_neg rankTwo] using D
        exact inputs.target
  | rankTwoEven _ characteristic _ _ _ _ _ =>
      subst p
      exact LowEvenInputs.target n ell F prime D
  | rankTwoOdd rank _ _ _ _ =>
      subst n
      exact (show LiLiSource.Inputs ell F prime from D).target
  | oddHigherRank _ _ _ _ _ =>
      exact HigherOddInputs.target n ell F D
  | sp6Two rank characteristic fieldTwo _ nondefining _ =>
      subst n
      exact D.target F
        (fun h => nondefining (h.trans characteristic.symm)) fieldTwo
  | rankThreeEven _ characteristic _ _ _ _ _ =>
      subst p
      exact LowEvenInputs.target n ell F prime D
  | evenHigherRank _ _ _ _ _ _ =>
      exact HigherEvenApplicationInputs.target n ell F D

/-- Every case proves the complete condition on its specified family and cover,
with the same original prime divisor. -/
theorem complete_at_case (c : NumericalCase n p ell (Nat.card F))
    (D : CaseInputs n p ell F prime c) (divides : ell ∣ Nat.card (PSp n F)) :
    Nonempty (FamilyWitness (target n p ell F prime c D).family
      (target n p ell F prime c D).cover) := by
  cases c with
  | defining equal =>
      subst ell
      exact DefiningInputs.complete n p F D
  | oddTwo fieldOdd equal nondefining notDvd =>
      subst ell
      by_cases rankTwo : n = 2
      · subst n
        exact (show LiLiSource.Inputs 2 F prime from D).complete notDvd divides
      · let inputs : OddTwoApplicationInputs n p F := by
          simpa only [CaseInputs, if_neg rankTwo] using D
        have target_eq :
            target n p 2 F prime
              (.oddTwo fieldOdd rfl nondefining notDvd) D = inputs.target := by
          simp only [target, dif_neg rankTwo]
          rfl
        exact Eq.mpr
          (congrArg (fun T : ActualTarget n 2 F =>
            Nonempty (FamilyWitness T.family T.cover)) target_eq)
          inputs.complete
  | rankTwoEven rank characteristic _ large _ nondefining _ =>
      subst p
      exact LowEvenInputs.complete n ell F prime D (Or.inl rank) large nondefining
  | rankTwoOdd rank _ _ _ notDvd =>
      subst n
      exact (show LiLiSource.Inputs ell F prime from D).complete notDvd divides
  | oddHigherRank _ _ _ _ _ =>
      exact HigherOddInputs.complete n ell F D
  | sp6Two rank characteristic fieldTwo _ nondefining _ =>
      subst n
      exact D.complete F
        (fun h => nondefining (h.trans characteristic.symm)) fieldTwo divides
  | rankThreeEven rank characteristic _ large _ nondefining _ =>
      subst p
      exact LowEvenInputs.complete n ell F prime D (Or.inr rank) large nondefining
  | evenHigherRank rank _ _ _ _ _ =>
      exact HigherEvenApplicationInputs.complete n ell F D rank

variable (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2))

/-- The numerical case determines which assumptions are required. -/
abbrev SourceInputs :=
  CaseInputs n p ell F prime (numericalCase n p ell F prime rank notSmall)

/-- The family, cover and simple group identification precede the application of
the selected theorem. -/
def actualTarget (D : SourceInputs n p ell F prime rank notSmall) : ActualTarget n ell F :=
  target n p ell F prime (numericalCase n p ell F prime rank notSmall) D

/-- The complete Type C condition for every allowed set of numerical parameters,
conditional on the stated assumptions for the selected case. -/
theorem full_block_condition_source_instantiated
    (D : SourceInputs n p ell F prime rank notSmall)
    (divides : ell ∣ Nat.card (PSp n F)) :
    Nonempty (FamilyWitness (actualTarget n p ell F prime rank notSmall D).family
      (actualTarget n p ell F prime rank notSmall D).cover) :=
  complete_at_case n p ell F prime (numericalCase n p ell F prime rank notSmall) D divides

/-- Choose data satisfying the complete condition after proving the result under
the specified source assumptions. -/
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

end ManuscriptIBAW.TypeC.AllCases

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
