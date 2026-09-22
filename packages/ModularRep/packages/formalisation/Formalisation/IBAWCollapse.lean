import Formalisation.IBAWCore
import Formalisation.FibreTransport

/-!
# The finite set core of the complete-collapse argument

The complete-group argument in the sporadic section has two logically
different parts.  The numerical Alperin weight equality supplies bijections
between the fibres over each block, and trivial outer action makes their
construction equivariant.  The stronger intermediate-group block equalities,
extensions, and character-triple compatibility are separate
representation theoretic assertions.

This file proves only the first part.  In particular, an arbitrary equivalence
selected from fibre cardinalities need not satisfy the `Q = 1` normalisation.
-/

namespace Formalisation.IBAW

/-- An action fixes every point. -/
def ActionTrivial (A X : Type*) [Group A] [MulAction A X] : Prop :=
  ∀ (a : A) (x : X), a • x = x

variable {A B R S X Y DZ : Type*} [Group A]
  [MulAction A B] [MulAction A R] [MulAction A S]
  [MulAction A X] [MulAction A Y] [MulAction A DZ]

/-- Any equivalence between two sets with trivial `A`-actions is
`A`-equivariant. -/
theorem equivariant_of_trivial_actions (f : X ≃ Y)
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y)
    (a : A) (x : X) : f (a • x) = a • f x := by
  rw [hX, hY]

section NumericalMatching

variable [Fintype X] [Fintype Y] [DecidableEq B]

/-- Fibre cardinalities over every block determine a block-preserving global
equivalence. -/
noncomputable def blockMatching (pX : X → B) (pY : Y → B)
    (hcard : ∀ b : B, Fintype.card (Fibre pX b) = Fintype.card (Fibre pY b)) :
    X ≃ Y :=
  Equiv.ofFiberEquiv fun b => Fintype.equivOfCardEq (hcard b)

theorem blockMatching_preserves_block (pX : X → B) (pY : Y → B)
    (hcard : ∀ b : B, Fintype.card (Fibre pX b) = Fintype.card (Fibre pY b))
    (x : X) : pY (blockMatching pX pY hcard x) = pX x :=
  Equiv.ofFiberEquiv_map (fun b => Fintype.equivOfCardEq (hcard b)) x

variable {C : Context A B R S X Y DZ}

/-- The numerical blockwise equality gives a candidate when the relevant
outer action is trivial.  Its radical partition is then derived from the
radical labels of the matched local objects. -/
noncomputable def candidateOfNumericalCollapse
    (hcard : ∀ b : B,
      Fintype.card (Fibre C.brauerBlock b) =
        Fintype.card (Fibre C.weightBlock b))
    (hX : ActionTrivial A X) (hY : ActionTrivial A Y) : Candidate C where
  equiv := blockMatching C.brauerBlock C.weightBlock hcard
  equiv_equivariant := equivariant_of_trivial_actions _ hX hY
  block_preserving := blockMatching_preserves_block _ _ hcard

end NumericalMatching

end Formalisation.IBAW


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
