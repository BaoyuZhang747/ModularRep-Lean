import ModularRep.PaperProofs.TypeBLeviRepresentativeSelection

/-!
# The original geometric component's rational carrier

The source is the existing ComponentPointData on the same geometric paired
Levi and its actual derived subgroup. Its inclusion and original Frobenius
square, together with the checked monomial cycle equations, determine the
full-return power on the included component. No finite model, return law,
principal block, character, or selected representative is supplied here.

This supporting all-rank carrier join is the first step in the principal
Spin selection construction. Authentic simple components and
the original Frobenius presentation retain ComponentPointData's E1/U scope.
The equivalence below only reorders the actual component membership and
fixedness conditions after proving their literal ambient power equation.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnSpinOriginalCarrier

open TypeBComponentCycleNormalization TypeBRegularLeviRationalCarriers
open TypeBRegularLeviComponentPointSource TypeBRegularLeviSupportedLift
open TypeBRegularLeviProductProjection

section MonomialPower

variable {C : Type} (m : C → ℕ) (V : Index m → Type)
variable [∀ i, Group (V i)] (S : CycleCoordinates m V)
variable (a : MulAut (Original m V)) (ha : MonomialAction m V S a)

local instance : DecidableEq (Index m) := Classical.decEq _

include ha

private theorem cycleProjection_power (c : C) (n : ℕ) (g : Original m V) :
    cycleProjection m V c ((a ^ n) g) =
      (a ^ n) (cycleProjection m V c g) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change cycleProjection m V c ((a ^ n) (a g)) =
        (a ^ n) (a (cycleProjection m V c g))
      rw [ih, cycleProjection_frobenius m V S a ha]

private theorem full_power_coordinate (c : C) (j : Fin (m c + 1))
    (g : Original m V) :
    toBase m V S c j ((a ^ (m c + 1)) g ⟨c, j⟩) =
      fullReturn m V S c (toBase m V S c j (g ⟨c, j⟩)) := by
  calc
    _ = (a ^ j.val) ((a ^ (m c + 1)) g) (first m c) :=
      toBase_eq_power m V S ha c j _
    _ = (a ^ (m c + 1)) ((a ^ j.val) g) (first m c) := by
      change ((a ^ j.val) * (a ^ (m c + 1))) g (first m c) =
        ((a ^ (m c + 1)) * (a ^ j.val)) g (first m c)
      rw [← pow_add, ← pow_add, Nat.add_comm]
    _ = fullReturn m V S c ((a ^ j.val) g (first m c)) :=
      (TypeBRegularLeviComponentFixedPoints.factorReturn_power_value
        m V S a ha c ((a ^ j.val) g)).symm
    _ = _ := congrArg (fullReturn m V S c)
      (toBase_eq_power m V S ha c j g).symm

/-- A full circuit preserves the actual single component, not only its
first-coordinate projection. -/
theorem full_power_single (c : C) (x : V (first m c)) :
    (a ^ (m c + 1)) (Function.update (1 : Original m V) (first m c) x) =
      Function.update (1 : Original m V) (first m c) (fullReturn m V S c x) := by
  classical
  let g : Original m V := Function.update (1 : Original m V) (first m c) x
  have masked : cycleProjection m V c g = g := by
    funext i
    by_cases hi : i = first m c
    · subst i
      simp [g, cycleProjection, first]
    · simp [g, cycleProjection, hi]
  have powered : cycleProjection m V c ((a ^ (m c + 1)) g) =
      (a ^ (m c + 1)) g := by
    rw [cycleProjection_power m V S a ha, masked]
  funext i
  rcases i with ⟨d, j⟩
  by_cases hdc : d = c
  · subst d
    apply (toBase m V S c j).injective
    rw [full_power_coordinate m V S a ha]
    by_cases hj : j = 0
    · subst j
      simp [first]
    · have hi : (⟨c, j⟩ : Index m) ≠ first m c := by
        intro hi
        have : j = 0 := by cases hi; rfl
        exact hj this
      simp [hi]
  · have hi : (⟨d, j⟩ : Index m) ≠ first m c := by
      intro hi
      exact hdc (congrArg Sigma.fst hi)
    have hp := congrFun powered ⟨d, j⟩
    simp only [cycleProjection_value, if_neg hdc] at hp
    simpa [g, hi] using hp.symm

end MonomialPower

section Component

variable {B C : Type} [Group B] (F : Monoid.End B)
variable (H : Subgroup B) (hH : ∀ x ∈ H, F x ∈ H)
variable (lengths : C → ℕ) (data : ComponentPointData F H hH lengths)

local instance : DecidableEq (Index lengths) := Classical.decEq _

local notation "V" => componentGroup F H hH lengths data

/-- The actual derived restriction, with its composition monoid explicit. -/
def derivedFrobeniusEnd : Monoid.End H :=
  derivedFrobenius F H hH

/-- The actual first geometric component mapped along the subgroup inclusion. -/
def componentSubgroup (c : C) : Subgroup B :=
  (data.component (first lengths c)).map H.subtype

/-- The component-to-image equivalence uses only the actual inclusion. -/
def componentEquiv (c : C) :
    V (first lengths c) ≃* componentSubgroup F H hH lengths data c :=
  (data.component (first lengths c)).equivMapOfInjective
    H.subtype Subtype.val_injective

@[simp] theorem componentEquiv_value (c : C) (x : V (first lengths c)) :
    (componentEquiv F H hH lengths data c x).val = ((x : H) : B) := rfl

@[simp] theorem componentEquiv_symm_value (c : C)
    (x : componentSubgroup F H hH lengths data c) :
    (((componentEquiv F H hH lengths data c).symm x : H) : B) = x.val :=
  congrArg Subtype.val ((componentEquiv F H hH lengths data c).apply_symm_apply x)

private theorem coordinates_inclusion (c : C) (x : V (first lengths c)) :
    data.coordinates (x : H) =
      Function.update (1 : Original lengths V) (first lengths c) x := by
  rw [← data.inclusion (first lengths c) x, MulEquiv.apply_symm_apply]

private theorem coordinates_power (n : ℕ) (x : H) :
    data.coordinates ((derivedFrobeniusEnd F H hH ^ n) x) =
      (data.frobenius ^ n) (data.coordinates x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change data.coordinates ((derivedFrobeniusEnd F H hH ^ n)
        (derivedFrobenius F H hH x)) =
          (data.frobenius ^ n) (data.frobenius (data.coordinates x))
      rw [ih, data.frobenius_value]

private theorem derived_power_value (n : ℕ) (x : H) :
    ((derivedFrobeniusEnd F H hH ^ n) x : B) = (F ^ n) (x : B) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change ((derivedFrobeniusEnd F H hH ^ n)
        (derivedFrobenius F H hH x) : B) = (F ^ n) (F (x : B))
      exact ih (derivedFrobenius F H hH x)

/-- The actual included component return is the original geometric power.
Its support on that component is proved from the monomial equations. -/
theorem componentReturn_value (c : C) (x : V (first lengths c)) :
    ((fullReturn lengths V data.cycles c x : H) : B) =
      (F ^ (lengths c + 1)) ((x : H) : B) := by
  have h : (derivedFrobeniusEnd F H hH ^ (lengths c + 1)) (x : H) =
      (fullReturn lengths V data.cycles c x : H) := by
    apply data.coordinates.injective
    calc
      data.coordinates ((derivedFrobeniusEnd F H hH ^ (lengths c + 1)) (x : H)) =
          (data.frobenius ^ (lengths c + 1)) (data.coordinates (x : H)) :=
        coordinates_power F H hH lengths data (lengths c + 1) (x : H)
      _ = (data.frobenius ^ (lengths c + 1))
          (Function.update (1 : Original lengths V) (first lengths c) x) :=
        congrArg (fun g : Original lengths V => (data.frobenius ^ (lengths c + 1)) g)
          (coordinates_inclusion F H hH lengths data c x)
      _ = Function.update (1 : Original lengths V) (first lengths c)
          (fullReturn lengths V data.cycles c x) :=
        full_power_single lengths V data.cycles data.frobenius data.monomial c x
      _ = data.coordinates (fullReturn lengths V data.cycles c x : H) :=
        (coordinates_inclusion F H hH lengths data c
          (fullReturn lengths V data.cycles c x)).symm
  exact (congrArg (fun y : H => (y : B)) h).symm.trans
    (derived_power_value F H hH (lengths c + 1) (x : H))

/-- Reorder actual fixedness and component membership after the proved
ambient power square. No finite group identification is sourced. -/
def componentFixedEquivRational (c : C) :
    rationalFactor F H hH lengths data c ≃*
      rationalSubgroup (F ^ (lengths c + 1))
        (componentSubgroup F H hH lengths data c) where
  toFun x := ⟨⟨((x.val : H) : B),
    (componentReturn_value F H hH lengths data c x.val).symm.trans
      (congrArg (fun y : V (first lengths c) => ((y : H) : B)) x.property)⟩,
    Subgroup.mem_map.mpr ⟨(x.val : H), x.val.property, rfl⟩⟩
  invFun x := ⟨(componentEquiv F H hH lengths data c).symm ⟨x.val.val, x.property⟩, by
    apply Subtype.ext
    apply Subtype.ext
    let y : V (first lengths c) :=
      (componentEquiv F H hH lengths data c).symm ⟨x.val.val, x.property⟩
    change ((fullReturn lengths V data.cycles c y : H) : B) = ((y : H) : B)
    have hy : ((y : H) : B) = x.val.val :=
      componentEquiv_symm_value F H hH lengths data c ⟨x.val.val, x.property⟩
    calc
      ((fullReturn lengths V data.cycles c y : H) : B) =
          (F ^ (lengths c + 1)) ((y : H) : B) :=
        componentReturn_value F H hH lengths data c y
      _ = (F ^ (lengths c + 1)) x.val.val :=
        congrArg (fun z : B => (F ^ (lengths c + 1)) z) hy
      _ = x.val.val := x.val.property
      _ = ((y : H) : B) := hy.symm⟩
  left_inv x := by
    apply Subtype.ext
    exact (componentEquiv F H hH lengths data c).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact componentEquiv_symm_value F H hH lengths data c ⟨x.val.val, x.property⟩
  map_mul' _ _ := rfl

@[simp] theorem componentFixedEquivRational_value (c : C)
    (x : rationalFactor F H hH lengths data c) :
    (componentFixedEquivRational F H hH lengths data c x).val.val =
      ((x.val : H) : B) := rfl

@[simp] theorem componentFixedEquivRational_symm_value (c : C)
    (x : rationalSubgroup (F ^ (lengths c + 1))
      (componentSubgroup F H hH lengths data c)) :
    ((((componentFixedEquivRational F H hH lengths data c).symm x).val : H) : B) =
      x.val.val :=
  componentEquiv_symm_value F H hH lengths data c ⟨x.val.val, x.property⟩

end Component

section OriginalLevi

open TypeBLeviRepresentativeSelection TypeBLeviRepresentativeGeometry

variable {A C : Type} [Group A] (Frob : MulAut A) (Lbar : Subgroup A)
variable (stable : Lbar.map Frob.toMonoidHom = Lbar) (m : C → ℕ)
variable (geometry : PrimalData Frob Lbar stable m)

/-- The original paired Frobenius as an endomorphism under composition. -/
def pairedFrobeniusEnd : Monoid.End (pairedLevi Lbar) :=
  pairedFrobenius Frob Lbar stable

/-- The actual geometric component at the first original field-cycle index. -/
abbrev originalComponent (c : C) : Subgroup (pairedLevi Lbar) :=
  componentSubgroup (pairedFrobenius Frob Lbar stable) (derivedInside Lbar)
    (derived_stable Frob Lbar stable) geometry.geometricLength geometry.components (first m c)

/-- The prescribed original rational base, with its geometric period unchanged. -/
def originalBaseEquivRational (c : C) :
    Base m geometry.factor c ≃*
      rationalSubgroup
        ((pairedFrobeniusEnd Frob Lbar stable) ^
          (geometry.geometricLength (first m c) + 1))
        (originalComponent Frob Lbar stable m geometry c) :=
  componentFixedEquivRational (pairedFrobenius Frob Lbar stable) (derivedInside Lbar)
    (derived_stable Frob Lbar stable) geometry.geometricLength geometry.components (first m c)

@[simp] theorem originalBaseEquivRational_value (c : C) (x : Base m geometry.factor c) :
    (originalBaseEquivRational Frob Lbar stable m geometry c x).val.val =
      ((x.val : derivedInside Lbar) : pairedLevi Lbar) := rfl

@[simp] theorem originalBaseEquivRational_symm_value (c : C)
    (x : rationalSubgroup
      ((pairedFrobeniusEnd Frob Lbar stable) ^
        (geometry.geometricLength (first m c) + 1))
      (originalComponent Frob Lbar stable m geometry c)) :
    ((((originalBaseEquivRational Frob Lbar stable m geometry c).symm x).val :
      derivedInside Lbar) : pairedLevi Lbar) = x.val.val :=
  componentFixedEquivRational_symm_value (pairedFrobenius Frob Lbar stable)
    (derivedInside Lbar) (derived_stable Frob Lbar stable)
    geometry.geometricLength geometry.components (first m c) x

/-- The same original product coordinate, with the rational-derived copy
reordered explicitly. This is the coordinate used by the return consumer. -/
@[simp] theorem originalBaseEquivRational_componentProduct_value (c : C)
    (x : TypeBLeviRepresentativeCarriers.N Frob Lbar) :
    (originalBaseEquivRational Frob Lbar stable m geometry c
      (geometry.componentProduct x (first m c))).val.val =
      ((geometry.components.coordinates
        ⟨((rationalDerivedEquiv Frob Lbar stable).symm x).val.val,
          ((rationalDerivedEquiv Frob Lbar stable).symm x).property⟩
        (first geometry.geometricLength (first m c)) : derivedInside Lbar) :
          pairedLevi Lbar) := rfl

end OriginalLevi

end ModularRep.PaperProofs.TypeBLeviReturnSpinOriginalCarrier


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
