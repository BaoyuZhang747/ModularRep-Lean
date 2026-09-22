import ModularRep.OrdinaryBlockFibre

/-!
# A common inflated ordinary character from a one-way fibre inclusion

This source-neutral K adapter turns a supplied one-way inclusion of inflated
quotient ordinary-character fibres into a common character witness.  In the
Lemma 5.2 application, the inclusion is the literal E1/U rendering of the
one-way ordinary-character implication in Spath, Corollary 2.11, and the
chosen labels are the induced quotient block and the fixed cover block.

The file does not assert that inclusion, does not package Corollary 2.11, and
does not construct the first common witness or any block equality.
-/

noncomputable section

namespace ModularRep.OrdinaryBlockFibreCommonWitness

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.OrdinaryBlockFibre

universe u v w

/-- A quotient ordinary character whose inflation belongs simultaneously to
the selected quotient fibre and selected cover fibre. -/
def CommonInflatedOrdinaryCharacter
    {K CoverG QuotientG : Type u}
    {CoverBlock : Type v} {QuotientBlock : Type w}
    [Field K] [CharZero K] [Group CoverG] [Group QuotientG]
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi)
    (quotientBlockOf :
      OrdinaryIrreducibleCharacter.Irr K QuotientG -> QuotientBlock)
    (coverBlockOf :
      OrdinaryIrreducibleCharacter.Irr K CoverG -> CoverBlock)
    (q : QuotientBlock) (B : CoverBlock) : Prop :=
  ∃ chi : OrdinaryIrreducibleCharacter.Irr K QuotientG,
    quotientBlockOf chi = q ∧
      coverBlockOf (inflateAlong pi hpi chi) = B

/-- Selector surjectivity supplies a member of the quotient fibre, and a
one-way inflated-fibre inclusion supplies its cover membership.  This is the
K construction of the second common witness once the Spath inclusion has
been bound literally. -/
theorem commonInflatedOrdinaryCharacter_of_image_fibre_subset
    {K CoverG QuotientG : Type u}
    {CoverBlock : Type v} {QuotientBlock : Type w}
    [Field K] [CharZero K] [Group CoverG] [Group QuotientG]
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi)
    (quotientBlockOf :
      OrdinaryIrreducibleCharacter.Irr K QuotientG -> QuotientBlock)
    (coverBlockOf :
      OrdinaryIrreducibleCharacter.Irr K CoverG -> CoverBlock)
    (hquotientBlockOf : Function.Surjective quotientBlockOf)
    {q : QuotientBlock} {B : CoverBlock}
    (hsubset :
      Set.image (inflateAlong pi hpi)
          (ordinaryBlockFibreSet quotientBlockOf q) ≤
        ordinaryBlockFibreSet coverBlockOf B) :
    CommonInflatedOrdinaryCharacter pi hpi
      quotientBlockOf coverBlockOf q B := by
  obtain ⟨chi, hchi⟩ := hquotientBlockOf q
  refine ⟨chi, hchi, ?_⟩
  have hmem :
      inflateAlong pi hpi chi ∈
        ordinaryBlockFibreSet coverBlockOf B := by
    apply hsubset
    exact ⟨chi, hchi, rfl⟩
  change coverBlockOf (inflateAlong pi hpi chi) = B at hmem
  exact hmem

end ModularRep.OrdinaryBlockFibreCommonWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
