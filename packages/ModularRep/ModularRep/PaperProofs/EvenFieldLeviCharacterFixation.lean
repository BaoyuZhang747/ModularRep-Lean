import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair

/-!
# Fixation of the selected Levi character

This module formalises the character-transport step in manuscript Lemma 3.6,
lines 360--373.  A group equivalence identifies the standard rational Levi
fixed points with the selected finite Levi.  The standard field automorphism
and the inner twisted automorphism are required to satisfy the manuscript's
intertwining equation under this equivalence.

The selected character is pulled back along the group equivalence.  The only
character-fixation input is the universal E3 statement that the standard
field automorphism fixes every unipotent character on the standard rational
Levi.  Fixation of the selected character is derived by transport; it is not
an input.
-/

namespace ModularRep.PaperProofs.EvenFieldLeviCharacterFixation

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair

universe u

variable {k StandardLevi SelectedLevi : Type u}
    [Field k] [CharZero k]
    [Group StandardLevi] [Group SelectedLevi]

/-- Transport of an irreducible character commutes with intertwined
automorphisms.  The equation is oriented as in the manuscript:
`equiv (sigma x) = tau (equiv x)`. -/
theorem transportIrr_twist_of_intertwining
    (equiv : StandardLevi ≃* SelectedLevi)
    (sigma : MulAut StandardLevi) (tau : MulAut SelectedLevi)
    (intertwines : ∀ x : StandardLevi,
      equiv (sigma x) = tau (equiv x))
    (chi : Irr k StandardLevi) :
    transportIrr equiv (twist k StandardLevi chi sigma) =
      twist k SelectedLevi (transportIrr equiv chi) tau := by
  apply OrdinaryIrreducibleCharacter.ext
  intro y
  rw [transportIrr_apply, twist_apply, twist_apply, transportIrr_apply]
  apply congrArg chi
  apply equiv.injective
  rw [equiv.apply_symm_apply]
  simpa using intertwines (equiv.symm y)

/-- Pullback along `equiv` followed by transport along `equiv` returns the
original irreducible character. -/
@[simp]
theorem transportIrr_symm_cancel
    (equiv : StandardLevi ≃* SelectedLevi)
    (lambda : Irr k SelectedLevi) :
    transportIrr equiv (transportIrr equiv.symm lambda) = lambda := by
  apply OrdinaryIrreducibleCharacter.ext
  intro y
  simp only [transportIrr_apply]
  change lambda (equiv (equiv.symm y)) = lambda y
  rw [equiv.apply_symm_apply]

/-- Universal unipotent-character fixation on the standard rational Levi
implies fixation of the selected Levi character under the intertwined
automorphism. -/
theorem selectedLeviCharacter_fixed
    (equiv : StandardLevi ≃* SelectedLevi)
    (sigma : MulAut StandardLevi) (tau : MulAut SelectedLevi)
    (intertwines : ∀ x : StandardLevi,
      equiv (sigma x) = tau (equiv x))
    (lambda : Irr k SelectedLevi)
    (Unipotent : Irr k StandardLevi → Prop)
    (pulled_unipotent : Unipotent (transportIrr equiv.symm lambda))
    (fieldFixesUnipotent : ∀ chi : Irr k StandardLevi,
      Unipotent chi → twist k StandardLevi chi sigma = chi) :
    twist k SelectedLevi lambda tau = lambda := by
  let lambdaStandard : Irr k StandardLevi :=
    transportIrr equiv.symm lambda
  have hstandard :
      twist k StandardLevi lambdaStandard sigma = lambdaStandard :=
    fieldFixesUnipotent lambdaStandard pulled_unipotent
  have htransport := congrArg (transportIrr equiv) hstandard
  rw [transportIrr_twist_of_intertwining equiv sigma tau intertwines]
    at htransport
  simpa [lambdaStandard] using htransport

end ModularRep.PaperProofs.EvenFieldLeviCharacterFixation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
