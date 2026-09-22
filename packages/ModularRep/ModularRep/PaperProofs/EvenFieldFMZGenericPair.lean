import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair

/-!
# The FMZ generic-pair carrier for a fixed block

This module gives a small semantic interface for the generic weights in
Feng--Malle--Zhang, Section 3.4, without formalising Lusztig induction or
Jordan-generalised cuspidality.

The label type `A` is intended to consist of the admissible algebraic
`e`-tori occurring in Definition 3.17(a): a label represents an `F'`-stable
algebraic `e`-torus `T` satisfying
`T = Z⁰(C_G(T))_(phi_e)`.  Definition 3.17(b) makes the generic-weight set
empty for every other torus, so restricting the label carrier in this way
does not change `W(C)`.

The finite normaliser is not supplied as arbitrary data.  It is the
stabiliser of the algebraic-torus label under inner conjugation, as defined
in `EvenFieldAlgebraicTorusPair`.  The only coherence input below is uniform
invariance of the defining predicate under inner conjugation.  No field
automorphism, fixedness assertion, action on the quotient, or comparison
with an independently supplied weight set occurs in the interface.
-/

namespace ModularRep.PaperProofs.EvenFieldFMZGenericPair

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair

universe u

variable {k H A Block : Type u}
    [Field k] [CharZero k] [Group H]
    [MulAction (MulAut H) A]

/-- Semantic definitions entering the FMZ generic-weight construction.

For an admissible algebraic `e`-torus label `T`, `levi T` represents the
finite group `C_G(T)^{F'}`, viewed as a subgroup of `N_H(T)`.  The proposition
`inL C T lambda` means exactly that `(C_G(T), lambda)` belongs to `L(C)` in
the paragraph immediately before Feng--Malle--Zhang, Definition 3.17.  In
particular, it includes the `e`-JGC, `ell'`-series, and Lusztig-induction
clauses in that paragraph.

The proposition `rdzAbove T eta lambda` means exactly
`eta ∈ rdz(N_H(T) | lambda)` in Definition 3.17.  Here `eta` already has
the concrete dependent type `Irr(N_H(T))`, with `N_H(T)` defined as the
inner-action stabiliser of `T`.
-/
structure Definitions (k H A Block : Type u)
    [Field k] [CharZero k] [Group H]
    [MulAction (MulAut H) A] where
  levi : (T : A) →
    Subgroup (finiteNormalizer (H := H) (A := A) T)
  inL : Block → (T : A) → Irr k (levi T) → Prop
  rdzAbove :
    (T : A) →
      Irr k (finiteNormalizer (H := H) (A := A) T) →
      Irr k (levi T) → Prop

/-- The exact predicate saying that a dependent pair is a generic
`(e, ell)`-weight belonging to `C`, following Feng--Malle--Zhang,
Definitions 3.17--3.18 and the paragraph preceding Definition 3.17. -/
def IsGenericFor (D : Definitions k H A Block) (C : Block)
    (P : LocalPair k H A) : Prop :=
  ∃ lambda : Irr k (D.levi P.1),
    D.inL C P.1 lambda ∧ D.rdzAbove P.1 P.2 lambda

/-- A selected witness that `P` is a generic pair belonging to `C`.

Using this structure at theorem boundaries keeps the finite Levi character
definitionally identical in the FMZ predicate, the inertia subgroup, and the
Gallagher--Clifford argument. -/
structure GenericWitness (D : Definitions k H A Block) (C : Block)
    (P : LocalPair k H A) where
  lambda : Irr k (D.levi P.1)
  inL : D.inL C P.1 lambda
  rdzAbove : D.rdzAbove P.1 P.2 lambda

/-- A selected generic witness supplies the existential predicate used to
form `W(C)`. -/
theorem GenericWitness.isGenericFor
    {D : Definitions k H A Block} {C : Block} {P : LocalPair k H A}
    (w : GenericWitness D C P) : IsGenericFor D C P :=
  ⟨w.lambda, w.inL, w.rdzAbove⟩

/-- The single coherence input required to form the FMZ orbit quotient.
It expresses, uniformly for every block and every pair, the invariance under
inner conjugation implicit in the definition `W(C) = W₀(C) / ~_H`.

This is semantic well-definedness of the published definition, not a
statement about any field automorphism or about fixation of an orbit. -/
structure InnerCoherence (D : Definitions k H A Block) : Prop where
  isGenericFor_inner :
    ∀ (C : Block) (h : H) (P : LocalPair k H A),
      IsGenericFor D C P →
        IsGenericFor D C ((MulAut.conj h) • P)

/-- The FMZ generic-pair predicate as the inner-stable predicate expected by
the dependent orbit construction. -/
def innerStablePredicate (D : Definitions k H A Block)
    (coherence : InnerCoherence D) (C : Block) :
    InnerStablePredicate k H A where
  predicate := IsGenericFor D C
  inner_stable := by
    intro h P hP
    exact coherence.isGenericFor_inner C h P hP

/-- Generic pairs belonging to `C`, before quotienting by `H`-conjugacy. -/
abbrev GenericPair (D : Definitions k H A Block)
    (coherence : InnerCoherence D) (C : Block) :=
  ValidPair k H A (innerStablePredicate D coherence C)

/-- The set `W(C)` of Feng--Malle--Zhang, Definition 3.18, defined literally
as the quotient of the valid generic pairs by `H`-conjugacy. -/
abbrev W (D : Definitions k H A Block)
    (coherence : InnerCoherence D) (C : Block) :=
  ValidConjugacyClass (innerStablePredicate D coherence C)

end ModularRep.PaperProofs.EvenFieldFMZGenericPair


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
