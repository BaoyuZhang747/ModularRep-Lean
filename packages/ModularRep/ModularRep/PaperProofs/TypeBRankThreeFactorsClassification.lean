import ModularRep.PaperProofs.TypeBRankThreeFactorsComponents
import ModularRep.PaperProofs.TypeBRankThreeFactorsPointSource
import ModularRep.PaperProofs.TypeBRankThreeFactorsDiagram
import ModularRep.PaperProofs.TypeBRankThreeFactorsClassicalModels

/-!
# Derived form guards on the actual rank-three root components

This module derives the one-component form guard from the actual connected
root-set index and the already classified selected-root action. Neither a
factor form nor a factor list is supplied by a source. The empty selected
diagram has no component index; the two isolated components retain their
different original roots. A2 reversal is internal to the single A2 component.

The names in ClassicalModels.Form designate later matrix models. The theorem
below supplies only the exact root-set/action guard for their normalization.
An algebraic embedding, its range and the same Frobenius square still belong
to the separately indexed specified normalization construction. No rational
group identification or completed manuscript inventory is asserted here.
-/

set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsClassification

open TypeBRankThreeFactorsDiagram TypeBRankThreeFactorsPointSource
open TypeBRankThreeFactorsComponents TypeBRankThreeFactorsClassicalModels

/-- Literal selected-root support and internal action of one actual component.
This is a guard derived by exists_component_form, not a classification input. -/
def ComponentHasForm (S : Finset Node) (action : SelectedAction S)
    (c : ComponentIndex S) : Form → Prop
  | .a1 => ∃ i : Node, c.val = ({i} : Set Node) ∧ action.permutation i = i
  | .a2 => c.val = ({0, 1} : Set Node) ∧ action.permutation = 1
  | .unitaryA2 => c.val = ({0, 1} : Set Node) ∧
      action.permutation = Equiv.swap (0 : Node) 1
  | .b2 => c.val = ({1, 2} : Set Node) ∧ action.permutation = 1

theorem singleton_component_val (i : Node) (c : ComponentIndex ({i} : Finset Node)) :
    c.val = ({i} : Set Node) :=
  (congrArg Subtype.val (singletonIndex_unique i c)).trans (singletonIndex_val i)

theorem a2_component_val (c : ComponentIndex ({0, 1} : Finset Node)) :
    c.val = ({0, 1} : Set Node) := by
  calc
    c.val = a2Index.val := congrArg Subtype.val (a2Index_unique c)
    _ = ({0, 1} : Set Node) := by simpa using a2Index_val

theorem b2_component_val (c : ComponentIndex ({1, 2} : Finset Node)) :
    c.val = ({1, 2} : Set Node) := by
  calc
    c.val = b2Index.val := congrArg Subtype.val (b2Index_unique c)
    _ = ({1, 2} : Set Node) := by simpa using b2Index_val

/-- Each original component has a derived form guard. The only inputs are
properness of the selected simple-root subset, its selected-diagram actor,
and the actual connected-component index. -/
theorem exists_component_form (S : Finset Node) (action : SelectedAction S)
    (proper : S ≠ Finset.univ) (c : ComponentIndex S) :
    ∃ form : Form, ComponentHasForm S action c form := by
  rcases action.proper_action_cases proper with
    ⟨hS, haction⟩ | ⟨hS, haction⟩ | ⟨hS, haction⟩ |
      ⟨hS, haction⟩ | ⟨⟨i, hS⟩, haction⟩ | ⟨hS, haction⟩
  · subst S
    exact ⟨.b2, b2_component_val c, haction⟩
  · subst S
    rcases isolatedIndex_cases c with hc | hc
    · refine ⟨.a1, 0, ?_, ?_⟩
      · exact (congrArg Subtype.val hc).trans longComponent_val
      · exact congrArg (fun e : Equiv.Perm Node => e 0) haction
    · refine ⟨.a1, 2, ?_, ?_⟩
      · exact (congrArg Subtype.val hc).trans shortComponent_val
      · exact congrArg (fun e : Equiv.Perm Node => e 2) haction
  · subst S
    exact ⟨.a2, a2_component_val c, haction⟩
  · subst S
    exact ⟨.unitaryA2, a2_component_val c, haction⟩
  · subst S
    refine ⟨.a1, i, singleton_component_val i c, ?_⟩
    exact congrArg (fun e : Equiv.Perm Node => e i) haction
  · subst S
    exact (componentIndex_empty_elim c).elim

end ModularRep.PaperProofs.TypeBRankThreeFactorsClassification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
