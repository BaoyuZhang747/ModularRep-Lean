import ModularRep.PaperProofs.TypeBRankThreeFactorsClassification

/-!
# Exhaustive inventories on the original rank-three component index

The six alternatives below are outputs of the selected-root calculation.
Their equivalences count the actual connected components, and their form
guards refer to those same components. In the disconnected case the two
positions retain the original long and short roots. No form, list, or
finished product is supplied as an input.
-/

set_option autoImplicit false

noncomputable section

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsInventoryCases

open TypeBRankThreeFactorsDiagram TypeBRankThreeFactorsPointSource
open TypeBRankThreeFactorsComponents TypeBRankThreeFactorsClassification
open TypeBRankThreeFactorsClassicalModels

/-- The empty selected diagram has exactly zero original components. -/
def emptyIndexEquiv : ComponentIndex (∅ : Finset Node) ≃ Fin 0 where
  toFun c := (componentIndex_empty_elim c).elim
  invFun i := Fin.elim0 i
  left_inv c := (componentIndex_empty_elim c).elim
  right_inv i := Fin.elim0 i

/-- Six exhaustive output alternatives, including multiplicity and the
literal root support of the two disconnected component positions. -/
def SixCases (S : Finset Node) (action : SelectedAction S) : Prop :=
  (S = {1, 2} ∧ ∃ _e : ComponentIndex S ≃ Fin 1,
    ∀ c, ComponentHasForm S action c .b2) ∨
  (S = {0, 2} ∧ ∃ e : ComponentIndex S ≃ Fin 2,
    (e.symm 0).val = ({0} : Set Node) ∧
    (e.symm 1).val = ({2} : Set Node) ∧
    ∀ c, ComponentHasForm S action c .a1) ∨
  (S = {0, 1} ∧ ∃ _e : ComponentIndex S ≃ Fin 1,
    ∀ c, ComponentHasForm S action c .a2) ∨
  (S = {0, 1} ∧ ∃ _e : ComponentIndex S ≃ Fin 1,
    ∀ c, ComponentHasForm S action c .unitaryA2) ∨
  ((∃ i : Node, S = {i}) ∧ ∃ _e : ComponentIndex S ≃ Fin 1,
    ∀ c, ComponentHasForm S action c .a1) ∨
  (S = ∅ ∧ Nonempty (ComponentIndex S ≃ Fin 0))

theorem isolatedIndexEquiv_zero_roots :
    (isolatedIndexEquiv.symm 0).val = ({0} : Set Node) := by
  have h := isolatedIndexEquiv.symm_apply_apply longComponent
  rw [isolatedIndexEquiv_long] at h
  exact (congrArg Subtype.val h).trans longComponent_val

theorem isolatedIndexEquiv_one_roots :
    (isolatedIndexEquiv.symm 1).val = ({2} : Set Node) := by
  have h := isolatedIndexEquiv.symm_apply_apply shortComponent
  rw [isolatedIndexEquiv_short] at h
  exact (congrArg Subtype.val h).trans shortComponent_val

/-- Properness and the actual selected-root action determine the full
zero-, one-, or two-component inventory and every recognized form. -/
theorem six_cases (S : Finset Node) (action : SelectedAction S)
    (proper : S ≠ Finset.univ) : SixCases S action := by
  unfold SixCases
  rcases action.proper_action_cases proper with
    ⟨hS, haction⟩ | ⟨hS, haction⟩ | ⟨hS, haction⟩ |
      ⟨hS, haction⟩ | ⟨⟨i, hS⟩, haction⟩ | ⟨hS, haction⟩
  · subst S
    exact Or.inl ⟨rfl, b2IndexEquiv, fun c => ⟨b2_component_val c, haction⟩⟩
  · subst S
    apply Or.inr
    apply Or.inl
    refine ⟨rfl, isolatedIndexEquiv, isolatedIndexEquiv_zero_roots,
      isolatedIndexEquiv_one_roots, ?_⟩
    intro c
    rcases isolatedIndex_cases c with hc | hc
    · refine ⟨0, ?_, ?_⟩
      · exact (congrArg Subtype.val hc).trans longComponent_val
      · exact congrArg (fun e : Equiv.Perm Node => e 0) haction
    · refine ⟨2, ?_, ?_⟩
      · exact (congrArg Subtype.val hc).trans shortComponent_val
      · exact congrArg (fun e : Equiv.Perm Node => e 2) haction
  · subst S
    exact Or.inr (Or.inr (Or.inl
      ⟨rfl, a2IndexEquiv, fun c => ⟨a2_component_val c, haction⟩⟩))
  · subst S
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, a2IndexEquiv, fun c => ⟨a2_component_val c, haction⟩⟩)))
  · subst S
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨i, rfl⟩, singletonIndexEquiv i, ?_⟩))))
    intro c
    refine ⟨i, singleton_component_val i c, ?_⟩
    exact congrArg (fun e : Equiv.Perm Node => e i) haction
  · subst S
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, ⟨emptyIndexEquiv⟩⟩))))

end ModularRep.PaperProofs.TypeBRankThreeFactorsInventoryCases


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
