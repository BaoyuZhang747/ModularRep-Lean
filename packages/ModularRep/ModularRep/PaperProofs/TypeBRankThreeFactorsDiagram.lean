import Mathlib.Data.Fintype.Fin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases

/-!
# Finite root diagram deductions for the proper rank-three Levi factors

This is supporting K combinatorics for the factor passage in
`prop:type-b-two-rank-three`. It does not identify an algebraic Levi or
its rational fixed groups. The specified simple-root chart, root lengths,
Cartan values and Frobenius restriction must be bound by the consumer.

The nodes are 0--1=>2, with squared lengths 2,2,1. Cartan entries use
root rows and coroot columns: entry (1,2) is -2 and entry (2,1) is -1.
An actor is extended by the identity outside its selected root subset.
Only SELECTED-root Cartan and length preservation are required. In
particular the reversal of the selected A2 diagram {0,1} is permitted;
it is not required to preserve the full B3 diagram.

Proper subsets and their possible actions are classified by finite
case analysis, with no classification list supplied as an input.
The connected-component statements retain the actual selected roots:
A2 reversal is internal to its one component, and the two isolated
different-length nodes 0 and 2 cannot be exchanged. No rational factor
type, desired factor list, block matching or criterion is a source here.
-/

set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsDiagram

abbrev Node := Fin 3

/-- Long nodes 0,1 and short node 2. -/
def squaredLength (i : Node) : ℕ := if i = 2 then 1 else 2

/-- Root-row, coroot-column Cartan convention for B3. -/
def cartan (i j : Node) : ℤ :=
  if i = j then 2
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then -1
  else if i = 1 ∧ j = 2 then -2
  else if i = 2 ∧ j = 1 then -1
  else 0

theorem node_cases (i : Node) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

theorem squaredLength_eq_one_iff (i : Node) : squaredLength i = 1 ↔ i = 2 := by
  fin_cases i <;> decide

theorem cartan_length_symmetry (i j : Node) :
    cartan i j * (squaredLength j : ℤ) = cartan j i * (squaredLength i : ℤ) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The two isolated nodes in the disconnected proper subset have unequal lengths. -/
theorem isolated_lengths_distinct : squaredLength 0 ≠ squaredLength 2 := by decide

theorem isolated_cartan_zero : cartan 0 2 = 0 ∧ cartan 2 0 = 0 := by decide

theorem a2_cartan : cartan 0 1 = -1 ∧ cartan 1 0 = -1 := by decide

theorem b2_cartan : cartan 1 2 = -2 ∧ cartan 2 1 = -1 := by decide

/-- A permutation on the selected roots, extended by identity on the complement.
Setwise preservation is derived below, rather than another source field. -/
structure SelectedAction (S : Finset Node) where
  permutation : Equiv.Perm Node
  fixed_off : ∀ i, i ∉ S → permutation i = i
  lengths : ∀ i, i ∈ S → squaredLength (permutation i) = squaredLength i
  cartan_values : ∀ i, i ∈ S → ∀ j, j ∈ S →
    cartan (permutation i) (permutation j) = cartan i j

namespace SelectedAction

variable {S : Finset Node} (a : SelectedAction S)

theorem mem_iff (i : Node) : a.permutation i ∈ S ↔ i ∈ S := by
  constructor
  · intro hi
    by_contra hout
    have fixed := a.fixed_off i hout
    exact hout (fixed ▸ hi)
  · intro hi
    by_contra hout
    have fixed := a.fixed_off (a.permutation i) hout
    have eq : a.permutation i = i := a.permutation.injective fixed
    exact hout (eq.symm ▸ hi)

theorem lengths_all (i : Node) : squaredLength (a.permutation i) = squaredLength i := by
  by_cases hi : i ∈ S
  · exact a.lengths i hi
  · rw [a.fixed_off i hi]

theorem fixes_short : a.permutation 2 = 2 := by
  apply (squaredLength_eq_one_iff (a.permutation 2)).mp
  exact (a.lengths_all 2).trans (by decide : squaredLength 2 = 1)

/-- Length preservation already restricts the ambient extension to these two maps.
The swap is not asserted to preserve the full B3 Cartan matrix. -/
theorem permutation_eq_one_or_swap :
    a.permutation = 1 ∨ a.permutation = Equiv.swap (0 : Node) 1 := by
  have h2 := a.fixes_short
  rcases node_cases (a.permutation 0) with h0 | h0 | h0
  · have h1 : a.permutation 1 = 1 := by
      rcases node_cases (a.permutation 1) with h1 | h1 | h1
      · exact ((by decide : (1 : Node) ≠ 0)
          (a.permutation.injective (h1.trans h0.symm))).elim
      · exact h1
      · exact ((by decide : (1 : Node) ≠ 2)
          (a.permutation.injective (h1.trans h2.symm))).elim
    left
    apply Equiv.ext
    intro i
    rcases node_cases i with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  · have h1 : a.permutation 1 = 0 := by
      rcases node_cases (a.permutation 1) with h1 | h1 | h1
      · exact h1
      · exact ((by decide : (1 : Node) ≠ 0)
          (a.permutation.injective (h1.trans h0.symm))).elim
      · exact ((by decide : (1 : Node) ≠ 2)
          (a.permutation.injective (h1.trans h2.symm))).elim
    right
    apply Equiv.ext
    intro i
    rcases node_cases i with rfl | rfl | rfl
    · exact h0.trans (Equiv.swap_apply_left (0 : Node) 1).symm
    · exact h1.trans (Equiv.swap_apply_right (0 : Node) 1).symm
    · exact h2.trans (by decide : Equiv.swap (0 : Node) 1 2 = 2).symm
  · exact ((by decide : (0 : Node) ≠ 2)
      (a.permutation.injective (h0.trans h2.symm))).elim

theorem swap_selected (hswap : a.permutation = Equiv.swap (0 : Node) 1) :
    (0 : Node) ∈ S ∧ (1 : Node) ∈ S := by
  constructor
  · by_contra h
    have fixed := a.fixed_off 0 h
    rw [hswap, Equiv.swap_apply_left] at fixed
    exact (by decide : (1 : Node) ≠ 0) fixed
  · by_contra h
    have fixed := a.fixed_off 1 h
    rw [hswap, Equiv.swap_apply_right] at fixed
    exact (by decide : (0 : Node) ≠ 1) fixed

end SelectedAction

/-- Exhaustive proper simple-root subsets, proved from the three membership bits. -/
theorem proper_subset_cases (S : Finset Node) (proper : S ≠ Finset.univ) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨
      S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} := by
  classical
  by_cases h0 : (0 : Node) ∈ S <;>
    by_cases h1 : (1 : Node) ∈ S <;>
    by_cases h2 : (2 : Node) ∈ S
  · exact (proper (by ext i; fin_cases i <;> simp_all)).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by ext i; fin_cases i <;> simp_all)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by ext i; fin_cases i <;> simp_all))))))
  · exact Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by ext i; fin_cases i <;> simp_all))))))
  · exact Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all))))
  · exact Or.inl (by ext i; fin_cases i <;> simp_all)

namespace SelectedAction

variable {S : Finset Node} (a : SelectedAction S)

theorem swap_subset_eq (proper : S ≠ Finset.univ)
    (hswap : a.permutation = Equiv.swap (0 : Node) 1) : S = {0, 1} := by
  classical
  obtain ⟨h0, h1⟩ := a.swap_selected hswap
  have h2 : (2 : Node) ∉ S := by
    intro h2
    apply proper
    ext i
    fin_cases i <;> simp_all
  ext i
  fin_cases i <;> simp_all

/-- Literal subset and internal-action classification. The six alternatives
map to B2, A1 A1, A2, twisted A2, A1 and torus only after specified realization. -/
theorem proper_action_cases (proper : S ≠ Finset.univ) :
    (S = {1, 2} ∧ a.permutation = 1) ∨
    (S = {0, 2} ∧ a.permutation = 1) ∨
    (S = {0, 1} ∧ a.permutation = 1) ∨
    (S = {0, 1} ∧ a.permutation = Equiv.swap (0 : Node) 1) ∨
    ((∃ i : Node, S = {i}) ∧ a.permutation = 1) ∨
    (S = ∅ ∧ a.permutation = 1) := by
  rcases a.permutation_eq_one_or_swap with hid | hswap
  · rcases proper_subset_cases S proper with h | h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hid⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨0, h⟩, hid⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨1, h⟩, hid⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨2, h⟩, hid⟩))))
    · exact Or.inr (Or.inr (Or.inl ⟨h, hid⟩))
    · exact Or.inr (Or.inl ⟨h, hid⟩)
    · exact Or.inl ⟨h, hid⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a.swap_subset_eq proper hswap, hswap⟩)))

theorem isolated_nodes_fixed (a : SelectedAction ({0, 2} : Finset Node)) :
    a.permutation 0 = 0 ∧ a.permutation 2 = 2 ∧ a.permutation = 1 := by
  rcases a.permutation_eq_one_or_swap with hid | hswap
  · exact ⟨congrArg (fun e : Equiv.Perm Node => e 0) hid,
      a.fixes_short, hid⟩
  · have h1 := (a.swap_selected hswap).2
    exact (by simpa using h1 : False).elim

end SelectedAction

/-- An edge of the actual induced root diagram. -/
def Adjacent (S : Finset Node) (i j : Node) : Prop :=
  i ∈ S ∧ j ∈ S ∧ i ≠ j ∧ cartan i j ≠ 0

/-- Connectedness by a finite sequence of selected-root edges. -/
def Connected (S : Finset Node) (i j : Node) : Prop :=
  Relation.ReflTransGen (Adjacent S) i j

/-- A component keeps the literal roots, rather than only its type name. -/
def component (S : Finset Node) (i : Node) : Set Node :=
  {j | j ∈ S ∧ Connected S i j}

namespace SelectedAction

variable {S : Finset Node} (a : SelectedAction S)

/-- Every selected-root actor moves each root only within its own component.
No properness assumption is needed for this statement. -/
theorem connected_to_image (i : Node) (hi : i ∈ S) :
    Connected S i (a.permutation i) := by
  rcases a.permutation_eq_one_or_swap with hid | hswap
  · rw [hid]
    exact Relation.ReflTransGen.refl
  · obtain ⟨h0, h1⟩ := a.swap_selected hswap
    rw [hswap]
    rcases node_cases i with rfl | rfl | rfl
    · rw [Equiv.swap_apply_left]
      exact Relation.ReflTransGen.single ⟨h0, h1, by decide, by decide⟩
    · rw [Equiv.swap_apply_right]
      exact Relation.ReflTransGen.single ⟨h1, h0, by decide, by decide⟩
    · rw [show Equiv.swap (0 : Node) 1 2 = 2 from by decide]
      exact Relation.ReflTransGen.refl

theorem image_connected_to_self (i : Node) (hi : i ∈ S) :
    Connected S (a.permutation i) i := by
  rcases a.permutation_eq_one_or_swap with hid | hswap
  · rw [hid]
    exact Relation.ReflTransGen.refl
  · obtain ⟨h0, h1⟩ := a.swap_selected hswap
    rw [hswap]
    rcases node_cases i with rfl | rfl | rfl
    · rw [Equiv.swap_apply_left]
      exact Relation.ReflTransGen.single ⟨h1, h0, by decide, by decide⟩
    · rw [Equiv.swap_apply_right]
      exact Relation.ReflTransGen.single ⟨h0, h1, by decide, by decide⟩
    · rw [show Equiv.swap (0 : Node) 1 2 = 2 from by decide]
      exact Relation.ReflTransGen.refl

theorem connected_image_iff (i j : Node) (hj : j ∈ S) :
    Connected S i (a.permutation j) ↔ Connected S i j := by
  constructor
  · intro h
    exact Relation.ReflTransGen.trans h (a.image_connected_to_self j hj)
  · intro h
    exact Relation.ReflTransGen.trans h (a.connected_to_image j hj)

/-- Every actual connected component is fixed setwise; A2 root reversal is
internal to its one component, not a permutation of algebraic components. -/
theorem component_image (i : Node) : a.permutation '' component S i = component S i := by
  ext j
  constructor
  · rintro ⟨k, ⟨hk, hc⟩, rfl⟩
    exact ⟨(a.mem_iff k).mpr hk, (a.connected_image_iff i k hk).mpr hc⟩
  · rintro ⟨hj, hc⟩
    let k := a.permutation.symm j
    have image : a.permutation k = j := a.permutation.apply_symm_apply j
    have hk : k ∈ S := (a.mem_iff k).mp (image.symm ▸ hj)
    have connected : Connected S i k :=
      (a.connected_image_iff i k hk).mp (image.symm ▸ hc)
    exact ⟨k, ⟨hk, connected⟩, image⟩

end SelectedAction

/-- The A2 reversal is a valid SELECTED-diagram actor. This confirms that
the interface does not inadvertently require full B3 diagram preservation. -/
def a2Reversal : SelectedAction ({0, 1} : Finset Node) where
  permutation := Equiv.swap 0 1
  fixed_off := by
    intro i hi
    fin_cases i
    · simp_all
    · simp_all
    · exact (by decide : Equiv.swap (0 : Node) 1 2 = 2)
  lengths := by
    intro i hi
    fin_cases i <;> simp_all [squaredLength]
  cartan_values := by
    intro i hi j hj
    fin_cases i <;> fin_cases j <;> simp_all [cartan]

theorem a2Reversal_not_full_cartan :
    cartan (a2Reversal.permutation 0) (a2Reversal.permutation 2) ≠ cartan 0 2 := by
  decide

end ModularRep.PaperProofs.TypeBRankThreeFactorsDiagram


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
