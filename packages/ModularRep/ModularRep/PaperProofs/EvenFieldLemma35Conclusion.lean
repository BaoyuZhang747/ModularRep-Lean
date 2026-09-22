import ModularRep.PaperProofs.EvenFieldFMZGenericPair
import ModularRep.PaperProofs.EvenFieldOrdinaryCharacters

/-!
# Exact fixation conclusion of manuscript Lemma 3.6

This module states the two conclusions of the lemma on the semantic
carriers used by the theorem-first development.  It deliberately contains
no source assumptions.  In particular, fixation of a generic weight means
that right transport of every valid representative determines the same
finite group conjugacy class.  This avoids introducing a left action with
the wrong orientation; a literal left action corresponding to the
manuscript's right convention would instead be an action of the opposite
field-automorphism group.
-/

namespace ModularRep.PaperProofs.EvenFieldLemma35Conclusion

open ModularRep.ManuscriptVerification.EvenFieldFixed
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters

universe u

variable {k H A Block E Dual : Type u}
    [Field k] [CharZero k] [Group H]
    [MulAction (MulAut H) A] [Group E] [Group Dual]

/-- Every standard field automorphism fixes every generic-weight orbit in
the manuscript's right-action convention.  The transported-validity proof
is returned rather than assumed, and equality is taken in the literal
quotient defining `W(C)`. -/
def WPointwiseFixed
    (D : Definitions k H A Block) (coherence : InnerCoherence D)
    (C : Block) (fieldAction : E →* MulAut H) : Prop :=
  ∀ (sigma : E) (v : GenericPair D coherence C),
    ∃ hvSigma : IsGenericFor D C
        (rightTransportPair v.1 (fieldAction sigma)),
      validConjugacyClass (innerStablePredicate D coherence C)
          ⟨rightTransportPair v.1 (fieldAction sigma), hvSigma⟩ =
        validConjugacyClass (innerStablePredicate D coherence C) v

/-- The exact conjunction proved in manuscript Lemma 3.6: pointwise
fixation of the ordinary-character set `X_C` and of the generic-weight
orbit set `W(C)`. -/
def FixationConclusion
    (ell : ℕ) (InBlock : Irr k H → Prop)
    (Series : Irr k H → Dual → Prop)
    (D : Definitions k H A Block) (coherence : InnerCoherence D)
    (C : Block) (fieldAction : E →* MulAut H) : Prop :=
  PointwiseFixed
      (fun sigma chi ↦ twist k H chi (fieldAction sigma))
      (XC ell InBlock Series) ∧
    WPointwiseFixed D coherence C fieldAction

end ModularRep.PaperProofs.EvenFieldLemma35Conclusion


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
