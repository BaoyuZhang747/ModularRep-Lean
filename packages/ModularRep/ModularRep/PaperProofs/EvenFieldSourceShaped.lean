import ModularRep.EvenFieldFixed
import ModularRep.PaperProofs.EvenFieldCliffordEndgame
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Source-shaped structural steps in the even-field fixed-point lemma

This file formalises the elementary group and class-function calculations in
manuscript Lemma 3.6.  Lang--Steinberg surjectivity, maximal extendibility,
and the representation theoretic Clifford and Gallagher theorems remain
explicit inputs at the application boundary.  The deductions below do not
assume that a character or a generic-weight representative is fixed.
-/

namespace ModularRep.PaperProofs.EvenFieldSourceShaped

universe uG uV

variable {G : Type uG} [Group G]

/-- The finite fixed-point group associated with an endomorphism. -/
def frobeniusFixedSubgroup (F : G →* G) : Subgroup G where
  carrier := {x | F x = x}
  one_mem' := map_one F
  mul_mem' := by
    intro x y hx hy
    change F x = x at hx
    change F y = y at hy
    simpa [hx, hy]
  inv_mem' := by
    intro x hx
    simpa using congrArg Inv.inv hx

/-- An endomorphism commuting with `F` restricts to an endomorphism of the
finite fixed-point group. -/
def frobeniusFixedSubgroupHom (F sigma : G →* G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x)) :
    frobeniusFixedSubgroup F →* frobeniusFixedSubgroup F where
  toFun x := ⟨sigma x, by
    change F (sigma (x : G)) = sigma x
    rw [commute, x.property]⟩
  map_one' := by
    ext
    exact map_one sigma
  map_mul' x y := by
    ext
    exact map_mul sigma (x : G) (y : G)

/-- A compatible map on a group and on a set descends to the quotient by
group orbits. -/
def inducedOrbitMap
    {H X : Type*} [Group H] [MulAction H X]
    (groupMap : H →* H) (pointMap : X → X)
    (compatible : ∀ h x, pointMap (h • x) = groupMap h • pointMap x) :
    MulAction.orbitRel.Quotient H X →
      MulAction.orbitRel.Quotient H X :=
  Quotient.map pointMap (by
    intro x y hxy
    change MulAction.orbitRel H X x y at hxy
    change MulAction.orbitRel H X (pointMap x) (pointMap y)
    rw [MulAction.orbitRel_apply] at hxy ⊢
    obtain ⟨h, hxy⟩ := MulAction.mem_orbit_iff.mp hxy
    refine MulAction.mem_orbit_iff.mpr ⟨groupMap h, ?_⟩
    rw [← compatible]
    exact congrArg pointMap hxy)

@[simp]
theorem inducedOrbitMap_mk
    {H X : Type*} [Group H] [MulAction H X]
    (groupMap : H →* H) (pointMap : X → X)
    (compatible : ∀ h x, pointMap (h • x) = groupMap h • pointMap x)
    (x : X) :
    inducedOrbitMap groupMap pointMap compatible (Quotient.mk'' x) =
      Quotient.mk'' (pointMap x) :=
  rfl

/-- The inner-twist element constructed from a Lang witness. -/
def innerTwistElement (sigma : G →* G) (g : G) : G :=
  g * (sigma g)⁻¹

/-- The calculation in Lemma 3.6 showing that the inner-twist element belongs
to the finite fixed-point group.  Existence of `g` with the displayed Lang
equation is deliberately not assumed here as a specialised fixedness claim. -/
theorem innerTwistElement_mem_frobeniusFixedSubgroup
    (F sigma : G →* G) (g w : G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (langEquation : g⁻¹ * F g = w)
    (w_fixed : sigma w = w) :
    innerTwistElement sigma g ∈ frobeniusFixedSubgroup F := by
  have hFg : F g = g * w := by
    calc
      F g = g * (g⁻¹ * F g) := by simp
      _ = g * w := congrArg (g * ·) langEquation
  have hFsigma : F (sigma g) = sigma g * w := by
    calc
      F (sigma g) = sigma (F g) := commute g
      _ = sigma (g * w) := congrArg sigma hFg
      _ = sigma g * sigma w := map_mul sigma g w
      _ = sigma g * w := by rw [w_fixed]
  change F (g * (sigma g)⁻¹) = g * (sigma g)⁻¹
  rw [map_mul, map_inv, hFg, hFsigma]
  simp [mul_assoc]

/-- A function constant on conjugacy classes.  This is the only property of
ordinary characters needed in the restriction and inner-action arguments. -/
def IsConjugationInvariant {Value : Type uV} (chi : G → Value) : Prop :=
  ∀ a x : G, chi (a * x * a⁻¹) = chi x

/-- Restriction of a function to a subgroup. -/
def restrictFunction {Value : Type uV} (I : Subgroup G)
    (chi : G → Value) : I → Value :=
  fun x ↦ chi x

/-- The element `tau` conjugates `I` into itself.  In the manuscript this is
deduced because the inner-twisted field automorphism stabilises the inertia
group. -/
def ConjugatesInto (I : Subgroup G) (tau : G) : Prop :=
  ∀ x : I, tau * (x : G) * tau⁻¹ ∈ I

/-- Conjugation action on functions on a subgroup, defined only after the
normalising property has been supplied. -/
def conjugationActionOnSubgroup {Value : Type uV}
    (I : Subgroup G) (tau : G) (normalises : ConjugatesInto I tau)
    (mu : I → Value) : I → Value :=
  fun x ↦ mu ⟨tau * (x : G) * tau⁻¹, normalises x⟩

/-- Restricting a class function from a group containing `tau` produces a
`tau`-invariant function on every subgroup normalised by `tau`. -/
theorem restricted_classFunction_fixed {Value : Type uV}
    (I : Subgroup G) (tau : G) (normalises : ConjugatesInto I tau)
    (chi : G → Value) (hchi : IsConjugationInvariant chi) :
    conjugationActionOnSubgroup I tau normalises
        (restrictFunction I chi) =
      restrictFunction I chi := by
  funext x
  exact hchi tau x

/-- Conjugation action on functions on a group. -/
def innerConjugationAction {Value : Type uV}
    (tau : G) (chi : G → Value) : G → Value :=
  fun x ↦ chi (tau * x * tau⁻¹)

/-- Inner automorphisms fix every class function.  Cabanes--Späth,
Proposition 2.3 supplies innerness of the field action on the relative Weyl
group; this lemma supplies the character-theoretic consequence. -/
theorem innerConjugationAction_fixed {Value : Type uV}
    (tau : G) (chi : G → Value)
    (hchi : IsConjugationInvariant chi) :
    innerConjugationAction tau chi = chi := by
  funext x
  exact hchi tau x

end ModularRep.PaperProofs.EvenFieldSourceShaped


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
