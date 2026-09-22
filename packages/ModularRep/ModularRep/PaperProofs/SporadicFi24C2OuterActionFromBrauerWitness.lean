import ModularRep.PaperProofs.SporadicFi24C2OuterQuotientCardTwoReduction

/-!
# The Fischer outer action from a Brauer character witness

This module replaces the independent assertion that the selected Fischer
automorphism is not inner by the narrower statement that it moves a literal
irreducible Brauer character.  Inner automorphisms fix all such characters,
so the noninnerness required by the cardinality two outer quotient reduction
is then a kernel deduction.

The two source fields below are intended for separate bindings to the
published automorphism group description and to the computed character
action.  Neither field supplies a character to weight map, a blockwise
equivalence, a principal block signature, extension data, BAW, or iBAW.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24C2OuterActionFromBrauerWitness

open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24C2OuterActionSourceReduction
open ModularRep.PaperProofs.SporadicFi24C2OuterQuotientCardTwoReduction

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

omit [Fintype X] in
/-- The range of the literal inner automorphisms is normal in the opposite
automorphism group. -/
private theorem innerInverseOpRange_normal :
    (RepresentationWeight.innerInverseOpHom (G := X)).range.Normal := by
  constructor
  intro beta hbeta alpha
  rcases hbeta with ⟨x, rfl⟩
  refine ⟨(alpha.unop⁻¹) x, ?_⟩
  apply MulOpposite.unop_injective
  ext y
  simp [RepresentationWeight.innerInverseOpHom, mul_assoc]

local instance innerInverseOpRangeNormal :
    (RepresentationWeight.innerInverseOpHom (G := X)).range.Normal :=
  innerInverseOpRange_normal

noncomputable local instance mulAutFinite : Finite (MulAut X) :=
  Finite.of_injective (fun alpha : MulAut X ↦ (alpha : X → X))
    DFunLike.coe_injective

noncomputable local instance mulAutOpFinite : Finite (MulAut X)ᵐᵒᵖ :=
  Finite.of_equiv (MulAut X) MulOpposite.opEquiv

noncomputable local instance outerQuotientFinite :
    Finite
      ((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range) :=
  Finite.of_surjective
    (QuotientGroup.mk'
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (QuotientGroup.mk'_surjective
      (RepresentationWeight.innerInverseOpHom (G := X)).range)

/-- The source facts needed to identify the selected involution with the
nontrivial class of a two element outer quotient.  The moved character is an
explicit witness on the literal Brauer carrier, not a character to weight
correspondence. -/
structure Fi24C2OuterActionBrauerWitnessSource
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X)) : Prop where
  quotient_card_two :
    Nat.card
      ((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range) = 2
  moves_brauer : ∃ phi : IBr iota, S.outer • phi ≠ phi

/-- Moving a literal Brauer character proves that the selected automorphism
is not inner. -/
theorem selectedOuter_not_inner_of_movesBrauer
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (W : Fi24C2OuterActionBrauerWitnessSource iota S) :
    S.outer ∉
      (RepresentationWeight.innerInverseOpHom (G := X)).range := by
  intro hinner
  obtain ⟨x, hx⟩ := hinner
  obtain ⟨phi, hmove⟩ := W.moves_brauer
  apply hmove
  rw [← hx]
  change IrreducibleBrauerCharacter.twist iota phi
    (MulAut.conj x⁻¹) = phi
  exact inner_fixes_ibr iota x phi

/-- Package the two source fields as the cardinality two quotient source.
The selected automorphism's noninnerness is proved rather than assumed. -/
theorem quotientCardTwoSource_ofBrauerWitness
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (W : Fi24C2OuterActionBrauerWitnessSource iota S) :
    Fi24C2OuterQuotientCardTwoSource S where
  quotient_card_two := W.quotient_card_two
  selectedOuter_not_inner :=
    selectedOuter_not_inner_of_movesBrauer iota S W

/-- Construct the structural quotient binding while retaining access to its
exact inner kernel for later selected outer arguments. -/
noncomputable def quotientBinding_ofBrauerWitness
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (W : Fi24C2OuterActionBrauerWitnessSource iota S) :
    Fi24C2OuterQuotientBinding S :=
  fi24C2OuterQuotientBinding_ofCardTwo S
    (quotientCardTwoSource_ofBrauerWitness iota S W)

/-- Construct the operational action needed for full automorphism promotion
from the two source facts.  Kernel fixation on both literal carriers is
proved by the existing quotient reduction. -/
noncomputable def c2OuterActionSource_ofBrauerWitness
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (W : Fi24C2OuterActionBrauerWitnessSource iota S) :
    C2OuterActionSource iota S :=
  c2OuterActionSource_ofQuotientBinding iota S
    (quotientBinding_ofBrauerWitness iota S W)

end ModularRep.PaperProofs.SporadicFi24C2OuterActionFromBrauerWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
