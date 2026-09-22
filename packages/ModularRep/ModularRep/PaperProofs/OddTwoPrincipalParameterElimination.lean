import Mathlib

/-!
# Principal-block parameter elimination in the odd-field type C argument

For the block labelled by the identity semisimple element, every elementary
divisor other than `x - 1` has multiplicity zero.  Feng--Malle define
`w_Gamma = m_Gamma` for `Gamma` in `F_1 union F_2`.  Hence every such
`w_Gamma` is zero.  This elementary deduction is the only bridge needed to
remove from the principal-block calculation the corrected
`E_{d_Gamma,1,1}` branch on p. 11 of Feng--Malle.

The source-specific statements remain E2: the interpretation of
`multiplicity`, the equation `m_Gamma = w_Gamma` away from `x - 1`, and the
fact that a nontrivial local factor in the assignment contributes positively
to `w_Gamma`.  The declarations below neither assume nor conclude an iBAW
bijection, BAW-goodness, a block-label comparison, or any character-triple
condition.
-/

namespace ModularRep.PaperProofs.OddTwoPrincipalParameterElimination

universe u

/-- Source-shaped numerical data for the identity semisimple label.

The two equalities are precisely the numerical parts of the principal label
and Feng--Malle's definition of `w_Gamma`.  No character, weight, or block
bijection is included. -/
structure PrincipalLabelData (Gamma : Type u) where
  xMinusOne : Gamma
  multiplicity : Gamma → Nat
  weightParameter : Gamma → Nat
  principal_nonX_multiplicity_zero :
    ∀ gamma, gamma ≠ xMinusOne → multiplicity gamma = 0
  nonX_multiplicity_eq_weight :
    ∀ gamma, gamma ≠ xMinusOne →
      multiplicity gamma = weightParameter gamma

/-- Every non-`x - 1` Feng--Malle weight parameter is zero for the principal
semisimple label. -/
theorem PrincipalLabelData.nonX_weightParameter_zero
    {Gamma : Type u} (D : PrincipalLabelData Gamma)
    (gamma : Gamma) (hGamma : gamma ≠ D.xMinusOne) :
    D.weightParameter gamma = 0 := by
  exact (D.nonX_multiplicity_eq_weight gamma hGamma).symm.trans
    (D.principal_nonX_multiplicity_zero gamma hGamma)

/-- There is no non-`x - 1` parameter with positive size.  In the source
assignment formula this says that no nontrivial local factor from those
elementary divisors occurs. -/
theorem PrincipalLabelData.no_positive_nonX_weightParameter
    {Gamma : Type u} (D : PrincipalLabelData Gamma) :
    ¬ ∃ gamma, gamma ≠ D.xMinusOne ∧ 0 < D.weightParameter gamma := by
  rintro ⟨gamma, hGamma, hPositive⟩
  rw [D.nonX_weightParameter_zero gamma hGamma] at hPositive
  exact Nat.not_lt_zero 0 hPositive

/-- A carrier for a selected nontrivial coordinate in one of the
non-`x - 1` factors.  Its emptiness is a non-conclusion-shaped formulation of
the parameter elimination used in the manuscript. -/
def NonXCoordinate {Gamma : Type u} (D : PrincipalLabelData Gamma) :=
  (gamma : { gamma // gamma ≠ D.xMinusOne }) × Fin (D.weightParameter gamma)

/-- The product of the non-`x - 1` parameter sets has only its empty
assignment: there is no selected positive coordinate. -/
theorem PrincipalLabelData.nonXCoordinate_isEmpty
    {Gamma : Type u} (D : PrincipalLabelData Gamma) :
    IsEmpty (NonXCoordinate D) := by
  constructor
  rintro ⟨gamma, i⟩
  have hZero := D.nonX_weightParameter_zero gamma gamma.2
  have hi : i.1 < 0 := by simpa [hZero] using i.2
  exact Nat.not_lt_zero _ hi

/-- Source-shaped data for one nontrivial local contribution in the
Feng--Malle assignment formula.  The weighted sum formula supplies
`amount_le_weight`; positivity says that the selected partition coordinate is
nonempty. -/
structure NonXLocalContribution {Gamma : Type u}
    (D : PrincipalLabelData Gamma) where
  gamma : Gamma
  gamma_ne_xMinusOne : gamma ≠ D.xMinusOne
  amount : Nat
  amount_positive : 0 < amount
  amount_le_weight : amount ≤ D.weightParameter gamma

/-- The principal identity label admits no nontrivial contribution from an
elementary divisor other than `x - 1`. -/
theorem PrincipalLabelData.nonXLocalContribution_isEmpty
    {Gamma : Type u} (D : PrincipalLabelData Gamma) :
    IsEmpty (NonXLocalContribution D) := by
  constructor
  intro c
  have hWeight := D.nonX_weightParameter_zero c.gamma c.gamma_ne_xMinusOne
  have hAmountZero : c.amount = 0 := by
    have hLe := c.amount_le_weight
    rw [hWeight] at hLe
    exact Nat.eq_zero_of_le_zero hLe
  exact (Nat.ne_of_gt c.amount_positive) hAmountZero

end ModularRep.PaperProofs.OddTwoPrincipalParameterElimination


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
