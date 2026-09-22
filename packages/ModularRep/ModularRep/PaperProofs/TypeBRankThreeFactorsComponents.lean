import ModularRep.PaperProofs.TypeBRankThreeFactorsPointSource

/-!
Actual connected root sets for the proper B3 diagrams. Connectivity uses
the reflexive transitive closure of the selected-root adjacency relation.
The index identifications retain these root sets and distinguish the two
isolated components by their original long and short roots. No component
count or factor inventory is supplied as an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsComponents

open TypeBRankThreeFactorsDiagram TypeBRankThreeFactorsPointSource

/-- A singleton selected root has its literal singleton component. -/
theorem component_singleton (i : Node) : component {i} i = ({i} : Set Node) := by
  ext j
  constructor
  · intro h
    exact Finset.mem_singleton.mp h.1
  · intro h
    have hj : j = i := h
    subst j
    exact ⟨by simp, Relation.ReflTransGen.refl⟩

private theorem connected_pair (a b : Node) (hne : a ≠ b)
    (hab : cartan a b ≠ 0) (hba : cartan b a ≠ 0)
    (i j : Node) (hi : i ∈ ({a, b} : Finset Node))
    (hj : j ∈ ({a, b} : Finset Node)) : Connected {a, b} i j := by
  have hi' : i = a ∨ i = b := by simpa using hi
  have hj' : j = a ∨ j = b := by simpa using hj
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, hne, hab⟩
  · exact Relation.ReflTransGen.single ⟨by simp, by simp, Ne.symm hne, hba⟩
  · exact Relation.ReflTransGen.refl

private theorem component_pair (a b : Node) (hne : a ≠ b)
    (hab : cartan a b ≠ 0) (hba : cartan b a ≠ 0)
    (i : Node) (hi : i ∈ ({a, b} : Finset Node)) :
    component {a, b} i = (↑({a, b} : Finset Node) : Set Node) := by
  ext j
  constructor
  · exact fun h => h.1
  · intro hj
    exact ⟨hj, connected_pair a b hne hab hba i j hi hj⟩

/-- Both selected A2 roots lie in the same actual component. -/
theorem component_a2 (i : Node) (hi : i ∈ ({0, 1} : Finset Node)) :
    component {0, 1} i = (↑({0, 1} : Finset Node) : Set Node) :=
  component_pair 0 1 (by decide) (by decide) (by decide) i hi

/-- Both selected B2 roots lie in the same actual component. -/
theorem component_b2 (i : Node) (hi : i ∈ ({1, 2} : Finset Node)) :
    component {1, 2} i = (↑({1, 2} : Finset Node) : Set Node) :=
  component_pair 1 2 (by decide) (by decide) (by decide) i hi

private theorem no_isolated_edge (i j : Node) :
    ¬ Adjacent ({0, 2} : Finset Node) i j := by
  fin_cases i <;> fin_cases j <;> simp [Adjacent, cartan]

private theorem isolated_connected_eq {i j : Node}
    (h : Connected ({0, 2} : Finset Node) i j) : i = j := by
  cases h with
  | refl => rfl
  | tail path edge => exact (no_isolated_edge _ _ edge).elim

/-- Reachability cannot connect the two selected roots without an edge. -/
theorem component_isolated (i : Node) (hi : i ∈ ({0, 2} : Finset Node)) :
    component {0, 2} i = ({i} : Set Node) := by
  ext j
  constructor
  · intro h
    exact (isolated_connected_eq h.2).symm
  · intro h
    have hj : j = i := h
    subst j
    exact ⟨hi, Relation.ReflTransGen.refl⟩

/-- A selected root determines its original component index. -/
def rootComponent (S : Finset Node) (i : Node) (hi : i ∈ S) : ComponentIndex S :=
  ⟨component S i, i, hi, rfl⟩

theorem componentIndex_empty_elim (c : ComponentIndex ∅) : False := by
  obtain ⟨i, hi, _⟩ := c.property
  simpa using hi

instance emptyIndex_isEmpty : IsEmpty (ComponentIndex ∅) :=
  ⟨componentIndex_empty_elim⟩

def singletonIndex (i : Node) : ComponentIndex {i} :=
  rootComponent {i} i (by simp)

@[simp] theorem singletonIndex_val (i : Node) :
    (singletonIndex i).val = ({i} : Set Node) := component_singleton i

theorem singletonIndex_unique (i : Node) (c : ComponentIndex {i}) :
    c = singletonIndex i := by
  apply Subtype.ext
  obtain ⟨j, hj, hc⟩ := c.property
  have hji : j = i := Finset.mem_singleton.mp hj
  subst j
  exact hc

def a2Index : ComponentIndex ({0, 1} : Finset Node) :=
  rootComponent {0, 1} 0 (by decide)

@[simp] theorem a2Index_val :
    a2Index.val = (↑({0, 1} : Finset Node) : Set Node) :=
  component_a2 0 (by decide)

theorem a2Index_unique (c : ComponentIndex ({0, 1} : Finset Node)) : c = a2Index := by
  apply Subtype.ext
  obtain ⟨i, hi, hc⟩ := c.property
  exact hc.trans ((component_a2 i hi).trans a2Index_val.symm)

def b2Index : ComponentIndex ({1, 2} : Finset Node) :=
  rootComponent {1, 2} 1 (by decide)

@[simp] theorem b2Index_val :
    b2Index.val = (↑({1, 2} : Finset Node) : Set Node) :=
  component_b2 1 (by decide)

theorem b2Index_unique (c : ComponentIndex ({1, 2} : Finset Node)) : c = b2Index := by
  apply Subtype.ext
  obtain ⟨i, hi, hc⟩ := c.property
  exact hc.trans ((component_b2 i hi).trans b2Index_val.symm)

private def uniqueIndexEquiv {T : Type} (x : T) (unique : ∀ y : T, y = x) : T ≃ Fin 1 where
  toFun _ := 0
  invFun _ := x
  left_inv y := (unique y).symm
  right_inv i := by fin_cases i; rfl

def singletonIndexEquiv (i : Node) : ComponentIndex {i} ≃ Fin 1 :=
  uniqueIndexEquiv (singletonIndex i) (singletonIndex_unique i)

def a2IndexEquiv : ComponentIndex ({0, 1} : Finset Node) ≃ Fin 1 :=
  uniqueIndexEquiv a2Index a2Index_unique

def b2IndexEquiv : ComponentIndex ({1, 2} : Finset Node) ≃ Fin 1 :=
  uniqueIndexEquiv b2Index b2Index_unique

def longComponent : ComponentIndex ({0, 2} : Finset Node) :=
  rootComponent {0, 2} 0 (by decide)

def shortComponent : ComponentIndex ({0, 2} : Finset Node) :=
  rootComponent {0, 2} 2 (by decide)

@[simp] theorem longComponent_val : longComponent.val = ({0} : Set Node) :=
  component_isolated 0 (by decide)

@[simp] theorem shortComponent_val : shortComponent.val = ({2} : Set Node) :=
  component_isolated 2 (by decide)

theorem longComponent_ne_shortComponent : longComponent ≠ shortComponent := by
  intro h
  have hval := congrArg Subtype.val h
  have member : (0 : Node) ∈ longComponent.val := by rw [longComponent_val]; simp
  rw [hval, shortComponent_val] at member
  exact (by simpa using member : False)

/-- The two original isolated component indices are exhaustive. -/
theorem isolatedIndex_cases (c : ComponentIndex ({0, 2} : Finset Node)) :
    c = longComponent ∨ c = shortComponent := by
  obtain ⟨i, hi, hc⟩ := c.property
  have hi' : i = 0 ∨ i = 2 := by simpa using hi
  rcases hi' with rfl | rfl
  · exact Or.inl (Subtype.ext hc)
  · exact Or.inr (Subtype.ext hc)

def isolatedIndexEquiv : ComponentIndex ({0, 2} : Finset Node) ≃ Fin 2 := by
  classical
  exact
    { toFun := fun c => if c = longComponent then 0 else 1
      invFun := fun i => if i = 0 then longComponent else shortComponent
      left_inv := by
        intro c
        rcases isolatedIndex_cases c with rfl | rfl <;>
          simp [Ne.symm longComponent_ne_shortComponent]
      right_inv := by
        intro i
        fin_cases i <;> simp [Ne.symm longComponent_ne_shortComponent] }

@[simp] theorem isolatedIndexEquiv_long : isolatedIndexEquiv longComponent = 0 := by
  classical
  simp [isolatedIndexEquiv]

@[simp] theorem isolatedIndexEquiv_short : isolatedIndexEquiv shortComponent = 1 := by
  classical
  simp [isolatedIndexEquiv, Ne.symm longComponent_ne_shortComponent]

/-- Root lengths distinguish the actual two component positions. -/
theorem isolatedIndex_lengths :
    (∀ i ∈ longComponent.val, squaredLength i = 2) ∧
    (∀ i ∈ shortComponent.val, squaredLength i = 1) := by
  constructor
  · intro i hi
    rw [longComponent_val] at hi
    have h : i = 0 := hi
    subst i
    decide
  · intro i hi
    rw [shortComponent_val] at hi
    have h : i = 2 := hi
    subst i
    decide

end ModularRep.PaperProofs.TypeBRankThreeFactorsComponents


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
