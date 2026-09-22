import ModularRep.CharacterWeightRadicalProjection
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Radical-order fixedness for character weights

The canonical radical projection assigns a subgroup order to every
character-weight class.  This order is invariant under automorphisms.  Hence
an exhaustive two-point fibre whose two points have different radical orders
is fixed pointwise by its block stabiliser.
-/

noncomputable section

namespace ModularRep.CharacterWeight

universe u

namespace RadicalSubgroup

/-- Automorphism preimage preserves the cardinality of a radical subgroup. -/
theorem natCard_rightTwist
    {p : Nat} {G : Type u} [Group G]
    (Q : RadicalSubgroup (p := p) (G := G))
    (alpha : MulAut G) :
    Nat.card (Q.rightTwist alpha).1 = Nat.card Q.1 := by
  change Nat.card (Q.1.comap alpha.toMonoidHom) = Nat.card Q.1
  rw [Subgroup.comap_equiv_eq_map_symm' alpha Q.1]
  exact Subgroup.card_map_of_injective
    (K := Q.1) alpha.symm.injective

end RadicalSubgroup

namespace RadicalConjugacyClass

/-- Cardinality of the subgroup represented by a radical conjugacy class. -/
def subgroupCard
    {p : Nat} {G : Type u} [Group G]
    (q : RadicalConjugacyClass (p := p) (G := G)) : Nat :=
  Quotient.lift (fun Q => Nat.card Q.1) (by
    intro Q R h
    rcases h with ⟨g, rfl⟩
    simpa only [RadicalSubgroup.smul_eq_rightTwist_conj] using
      RadicalSubgroup.natCard_rightTwist R (MulAut.conj g⁻¹)) q

/-- Radical-subgroup cardinality is invariant under automorphisms. -/
@[simp]
theorem subgroupCard_smul
    {p : Nat} {G : Type u} [Group G]
    (alpha : (MulAut G)ᵐᵒᵖ)
    (q : RadicalConjugacyClass (p := p) (G := G)) :
    subgroupCard (alpha • q) = subgroupCard q := by
  refine Quotient.inductionOn q ?_
  intro Q
  change Nat.card (Q.rightTwist alpha.unop).1 = Nat.card Q.1
  exact RadicalSubgroup.natCard_rightTwist Q alpha.unop

end RadicalConjugacyClass

/-- The order of the radical support of a character-weight conjugacy class. -/
def radicalOrder
    {p : Nat} {K G : Type u}
    [Field K] [CharZero K] [Group G] [Finite G]
    (weight : ConjugacyClass (p := p) (K := K) (G := G)) : Nat :=
  RadicalConjugacyClass.subgroupCard (radicalClass weight)

/-- Canonical radical order is invariant under every ambient automorphism. -/
@[simp]
theorem radicalOrder_smul
    {p : Nat} {K G : Type u}
    [Field K] [CharZero K] [Group G] [Finite G]
    (alpha : (MulAut G)ᵐᵒᵖ)
    (weight : ConjugacyClass (p := p) (K := K) (G := G)) :
    radicalOrder (alpha • weight) = radicalOrder weight := by
  simp only [radicalOrder, radicalClass_equivariant,
    RadicalConjugacyClass.subgroupCard_smul]

namespace EquivariantBlockAssignment

/-- Two exhaustive weight classes with radical orders eight and four are
fixed by the whole stabiliser of their block. -/
theorem fibre_smul_eq_self_of_orders_eight_four
    {p : Nat} {K G Block : Type u}
    [Field K] [CharZero K] [Group G] [Finite G]
    [MulAction (MulAut G)ᵐᵒᵖ Block]
    (D : EquivariantBlockAssignment
      (p := p) (K := K) (G := G) Block)
    (b : Block)
    (weightEight weightFour : D.Fibre b)
    (exhaustive : ∀ weight : D.Fibre b,
      weight = weightEight ∨ weight = weightFour)
    (orderEight : radicalOrder weightEight.1 = 8)
    (orderFour : radicalOrder weightFour.1 = 4) :
    ∀ (alpha : MulAction.stabilizer (MulAut G)ᵐᵒᵖ b)
      (weight : D.Fibre b),
      alpha • weight = weight := by
  intro alpha weight
  have hImage := exhaustive (alpha • weight)
  have hOrder :
      radicalOrder ((alpha • weight : D.Fibre b).1) =
        radicalOrder weight.1 := by
    rw [EquivariantBlockAssignment.fibre_smul_val D b alpha weight,
      radicalOrder_smul]
  rcases exhaustive weight with hWeight | hWeight
  · subst weight
    rcases hImage with h | h
    · exact h
    · exfalso
      have hcross :
          radicalOrder weightFour.1 = radicalOrder weightEight.1 :=
        (congrArg (fun w : D.Fibre b => radicalOrder w.1) h).symm.trans hOrder
      have hbad : (4 : Nat) = 8 :=
        orderFour.symm.trans (hcross.trans orderEight)
      exact (by decide : (4 : Nat) ≠ 8) hbad
  · subst weight
    rcases hImage with h | h
    · exfalso
      have hcross :
          radicalOrder weightEight.1 = radicalOrder weightFour.1 :=
        (congrArg (fun w : D.Fibre b => radicalOrder w.1) h).symm.trans hOrder
      have hbad : (8 : Nat) = 4 :=
        orderEight.symm.trans (hcross.trans orderFour)
      exact (by decide : (8 : Nat) ≠ 4) hbad
    · exact h

end EquivariantBlockAssignment

end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
