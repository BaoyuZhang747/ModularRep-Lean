import ModularRep.PaperProofs.TypeBRegularLeviComponentFixedPoints

/-!
# Singleton component fixed points on the original group

The rank-three root argument supplies nonpermutation before this adapter is
applied. The inputs here are original geometric coordinates, the original
Frobenius, and its coordinate equations on the literal component subgroups.
Every component cycle has length one. Its cycle coordinates and monomial
action are constructed here; the rational product uses the existing
fixedProductEquiv. No rational product or normalized-return equation is an
input. The geometric inclusion anchor is used separately to identify each
coordinate Frobenius with the same original point map.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsFixedPoints

open TypeBComponentCycleNormalization TypeBRegularLeviRationalCarriers

variable {C H : Type} [Group H]

abbrev cycleLength : C → ℕ := fun _ => 0

abbrev cycleGroups (component : C → Subgroup H)
    (i : Index (cycleLength (C := C))) : Type := component i.1

/-- Repeat the actual coordinate once, at the sole position of its cycle. -/
def singletonIndexEquiv (component : C → Subgroup H) :
    ((c : C) → component c) ≃*
      Original cycleLength (cycleGroups component) where
  toFun g i := g i.1
  invFun g c := g ⟨c, 0⟩
  left_inv _ := rfl
  right_inv g := by
    funext i
    rcases i with ⟨c, j⟩
    have hj : j = 0 := Fin.eq_zero (show Fin 1 from j)
    subst j
    rfl
  map_mul' _ _ := rfl

/-- The cycle coordinates still evaluate the original geometric product. -/
def singletonCoordinates (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) :
    H ≃* Original cycleLength (cycleGroups component) :=
  coordinates.trans (singletonIndexEquiv component)

/-- There are no successor edges; the wrap is the prescribed one-step map. -/
def singletonCycles (component : C → Subgroup H)
    (componentF : ∀ c, MulAut (component c)) :
    CycleCoordinates cycleLength (cycleGroups component) where
  edge _ j := Fin.elim0 j
  wrap c := componentF c

/-- Transport the same original Frobenius, rather than selecting another action. -/
def singletonFrobenius (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H) :
    MulAut (Original cycleLength (cycleGroups component)) :=
  MulAut.congr (singletonCoordinates component coordinates) Frob

/-- The original coordinate equation supplies the singleton monomial law. -/
theorem singletonMonomial (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H)
    (componentF : ∀ c, MulAut (component c))
    (coordinateEquation : ∀ h c, coordinates (Frob h) c = componentF c (coordinates h c)) :
    MonomialAction cycleLength (cycleGroups component) (singletonCycles component componentF)
      (singletonFrobenius component coordinates Frob) := by
  constructor
  · intro g c j
    exact Fin.elim0 j
  · intro g c
    change coordinates (Frob ((singletonCoordinates component coordinates).symm g)) c =
      componentF c (g ⟨c, 0⟩)
    rw [coordinateEquation]
    change componentF c (coordinates (coordinates.symm (fun d => g ⟨d, 0⟩)) c) = _
    rw [MulEquiv.apply_symm_apply]

/-- The computed cycle return is exactly the same one-step component Frobenius. -/
@[simp] theorem singletonReturn_eq (component : C → Subgroup H)
    (componentF : ∀ c, MulAut (component c)) (c : C) :
    fullReturn cycleLength (cycleGroups component) (singletonCycles component componentF) c =
      componentF c := by
  ext x
  rfl

/-- Restrict the geometric coordinate equivalence to the original fixed group. -/
def singletonFixedCoordinatesEquiv (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H) :
    fixedPoints Frob.toMonoidHom ≃*
      fixedPoints (singletonFrobenius component coordinates Frob).toMonoidHom where
  toFun x := ⟨singletonCoordinates component coordinates x.val, by
    change singletonCoordinates component coordinates
      (Frob ((singletonCoordinates component coordinates).symm
        (singletonCoordinates component coordinates x.val))) =
      singletonCoordinates component coordinates x.val
    rw [MulEquiv.symm_apply_apply]
    exact congrArg (singletonCoordinates component coordinates) x.property⟩
  invFun x := ⟨(singletonCoordinates component coordinates).symm x.val, by
    apply (singletonCoordinates component coordinates).injective
    change singletonFrobenius component coordinates Frob x.val =
      singletonCoordinates component coordinates ((singletonCoordinates component coordinates).symm x.val)
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((singletonCoordinates component coordinates).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((singletonCoordinates component coordinates).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((singletonCoordinates component coordinates).map_mul x.val y.val)

/-- The complete original fixed group is the product of the actual component
fixed groups. The only fixed-product theorem used is the existing cycle theorem. -/
def singletonFixedProductEquiv (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H)
    (componentF : ∀ c, MulAut (component c))
    (coordinateEquation : ∀ h c, coordinates (Frob h) c = componentF c (coordinates h c)) :
    fixedPoints Frob.toMonoidHom ≃* ((c : C) → fixedPoints (componentF c).toMonoidHom) :=
  (singletonFixedCoordinatesEquiv component coordinates Frob).trans
    (TypeBRegularLeviComponentFixedPoints.fixedProductEquiv cycleLength (cycleGroups component)
      (singletonCycles component componentF) (singletonFrobenius component coordinates Frob)
      (singletonMonomial component coordinates Frob componentF coordinateEquation))

@[simp] theorem singletonFixedProductEquiv_value (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H)
    (componentF : ∀ c, MulAut (component c))
    (coordinateEquation : ∀ h c, coordinates (Frob h) c = componentF c (coordinates h c))
    (x : fixedPoints Frob.toMonoidHom) (c : C) :
    (singletonFixedProductEquiv component coordinates Frob componentF coordinateEquation x c).val =
      coordinates x.val c := rfl

@[simp] theorem singletonFixedProductEquiv_symm_value (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H)
    (componentF : ∀ c, MulAut (component c))
    (coordinateEquation : ∀ h c, coordinates (Frob h) c = componentF c (coordinates h c))
    (theta : (c : C) → fixedPoints (componentF c).toMonoidHom) :
    ((singletonFixedProductEquiv component coordinates Frob componentF coordinateEquation).symm theta).val =
      coordinates.symm (fun c => (theta c).val) := rfl

@[simp] theorem singletonFixedProductEquiv_symm_coordinate (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H)
    (componentF : ∀ c, MulAut (component c))
    (coordinateEquation : ∀ h c, coordinates (Frob h) c = componentF c (coordinates h c))
    (theta : (c : C) → fixedPoints (componentF c).toMonoidHom) (c : C) :
    coordinates
      ((singletonFixedProductEquiv component coordinates Frob componentF coordinateEquation).symm theta).val c =
      (theta c).val := by
  rw [singletonFixedProductEquiv_symm_value, MulEquiv.apply_symm_apply]

section Inclusion

variable [DecidableEq C]

/-- The geometric single-coordinate inclusion authenticates each original
component map as the literal restriction of the same point Frobenius. -/
theorem componentFrobenius_value (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H)
    (componentF : ∀ c, MulAut (component c))
    (coordinateEquation : ∀ h c, coordinates (Frob h) c = componentF c (coordinates h c))
    (inclusion : ∀ c (x : component c), coordinates.symm (Function.update 1 c x) = (x : H))
    (c : C) (x : component c) : (componentF c x : H) = Frob (x : H) := by
  have hx : coordinates (x : H) = Function.update (1 : (d : C) → component d) c x := by
    rw [← inclusion c x, MulEquiv.apply_symm_apply]
  have hF : coordinates (Frob (x : H)) =
      Function.update (1 : (d : C) → component d) c (componentF c x) := by
    funext d
    rw [coordinateEquation, hx]
    by_cases hd : d = c
    · subst d
      simp
    · simp [Function.update, hd, Ne.symm hd]
  calc
    (componentF c x : H) = coordinates.symm (Function.update 1 c (componentF c x)) :=
      (inclusion c (componentF c x)).symm
    _ = coordinates.symm (coordinates (Frob (x : H))) := congrArg coordinates.symm hF.symm
    _ = Frob (x : H) := coordinates.symm_apply_apply _

/-- The computed full return is the original one-step Frobenius on the
literal component inclusion, not a separate return or a higher field power. -/
theorem singletonReturn_value (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H)
    (componentF : ∀ c, MulAut (component c))
    (coordinateEquation : ∀ h c, coordinates (Frob h) c = componentF c (coordinates h c))
    (inclusion : ∀ c (x : component c), coordinates.symm (Function.update 1 c x) = (x : H))
    (c : C) (x : component c) :
    (fullReturn cycleLength (cycleGroups component) (singletonCycles component componentF) c x : H) =
      Frob (x : H) := by
  rw [singletonReturn_eq]
  exact componentFrobenius_value component coordinates Frob componentF coordinateEquation inclusion c x

/-- The inverse rational product preserves the literal original inclusion. -/
theorem singletonFixedProductEquiv_symm_inclusion (component : C → Subgroup H)
    (coordinates : H ≃* ((c : C) → component c)) (Frob : MulAut H)
    (componentF : ∀ c, MulAut (component c))
    (coordinateEquation : ∀ h c, coordinates (Frob h) c = componentF c (coordinates h c))
    (inclusion : ∀ c (x : component c), coordinates.symm (Function.update 1 c x) = (x : H))
    (c : C) (x : fixedPoints (componentF c).toMonoidHom) :
    ((singletonFixedProductEquiv component coordinates Frob componentF coordinateEquation).symm
      (Function.update 1 c x)).val = (x.val : H) := by
  rw [singletonFixedProductEquiv_symm_value]
  have ht : (fun d => (Function.update (1 : (d : C) → fixedPoints (componentF d).toMonoidHom) c x d).val) =
      Function.update (1 : (d : C) → component d) c x.val := by
    funext d
    by_cases hd : d = c
    · subst d
      exact (congrArg
        (fun z : fixedPoints (componentF c).toMonoidHom => z.val)
        (show Function.update (1 : (d : C) → fixedPoints (componentF d).toMonoidHom) c x c = x from by
          simp only [Function.update_self])).trans
        (show Function.update (1 : (d : C) → component d) c x.val c = x.val from by
          simp only [Function.update_self]).symm
    · simp [Function.update, hd, Ne.symm hd]
  rw [ht]
  exact inclusion c x.val

end Inclusion

end ModularRep.PaperProofs.TypeBRankThreeFactorsFixedPoints


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
