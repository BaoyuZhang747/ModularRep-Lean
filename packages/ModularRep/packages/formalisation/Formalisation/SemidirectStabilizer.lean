import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Stabilizers for a compatible semidirect product action

This file formalises the group-theoretic stabilizer calculation used in the manuscript's
component-return argument.  Let `D` and `E` act on `X`, and let `phi : E -> MulAut D` describe
the semidirect product.  The compatibility hypothesis says that applying `e` after `d` has the
same effect as applying `phi e d` after `e`.  Under this hypothesis, `(d,e)` acts as
`d * (e * x)`.

If every element of `E` fixes `x`, the final theorem proves, for an actual Mathlib semidirect
product, that `(d,e)` fixes `x` exactly when `d` and `e` fix `x` separately.  This is the
elementwise form of the stabilizer factorization `(D semidirect E)_x = D_x E_x`.

The result is purely group theoretic.  Its application to Brauer characters still requires the
representation theoretic input that the relevant diagonal and field automorphisms give the
compatible actions modelled here.
-/

namespace Formalisation

section SemidirectStabilizer

variable {D E X : Type*} [Group D] [Group E]
variable [MulAction D X] [MulAction E X]

/-- The compatibility needed for the formula `(d,e) * x = d * (e * x)` to define an action of
the semidirect product. -/
def SemidirectActionCompatible (phi : E →* MulAut D) : Prop :=
  ∀ (e : E) (d : D) (x : X), e • (d • x) = (phi e d) • (e • x)

/-- The action of `D ⋊ E` obtained from compatible actions of `D` and `E`. -/
@[instance_reducible]
def semidirectMulAction (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi) :
    MulAction (D ⋊[phi] E) X where
  smul p x := p.left • (p.right • x)
  one_smul x := by
    change (1 : D) • ((1 : E) • x) = x
    rw [one_smul, one_smul]
  mul_smul p q x := by
    change
      (p.left * phi p.right q.left) • ((p.right * q.right) • x) =
        p.left • (p.right • (q.left • (q.right • x)))
    rw [mul_smul, mul_smul, hcompat]

/-- With the compatible semidirect product action, the canonical copy of `D` acts by the
original `D`-action. -/
theorem semidirect_inl_smul (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi) (d : D) (x : X) :
    letI := semidirectMulAction phi hcompat
    SemidirectProduct.inl (φ := phi) d • x = d • x := by
  let _ := semidirectMulAction phi hcompat
  change d • ((1 : E) • x) = d • x
  rw [one_smul]

/-- With the compatible semidirect product action, the canonical copy of `E` acts by the
original `E`-action. -/
theorem semidirect_inr_smul (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi) (e : E) (x : X) :
    letI := semidirectMulAction phi hcompat
    SemidirectProduct.inr (φ := phi) e • x = e • x := by
  let _ := semidirectMulAction phi hcompat
  change (1 : D) • (e • x) = e • x
  rw [one_smul]

/-- If `E` fixes `x`, an element of `D ⋊ E` fixes `x` exactly when its `D`- and `E`-parts
fix `x` separately.  This is the elementwise stabilizer factorization used in the
component-return argument. -/
theorem mem_semidirect_stabilizer_iff (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi) (x : X)
    (hfixed : ∀ e : E, e • x = x) :
    letI := semidirectMulAction phi hcompat
    ∀ p : D ⋊[phi] E,
      p ∈ MulAction.stabilizer (D ⋊[phi] E) x ↔
        p.left ∈ MulAction.stabilizer D x ∧ p.right ∈ MulAction.stabilizer E x := by
  let _ := semidirectMulAction phi hcompat
  intro p
  change p.left • (p.right • x) = x ↔ p.left • x = x ∧ p.right • x = x
  have he : p.right • x = x := hfixed p.right
  constructor
  · intro hp
    constructor
    · simpa [semidirectMulAction, he] using hp
    · exact he
  · rintro ⟨hd, _⟩
    simpa [semidirectMulAction, he] using hd

/-- If the normal factor acts trivially on the whole set, membership in a
semidirect product stabilizer is determined exactly by the outer component.
Unlike `mem_semidirect_stabilizer_iff`, this statement does not assume that
the whole outer factor fixes `x`. -/
theorem mem_semidirect_stabilizer_iff_right_of_left_trivial
    (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi)
    (hleft : ∀ (d : D) (y : X), d • y = y)
    (x : X) :
    letI := semidirectMulAction phi hcompat
    ∀ p : D ⋊[phi] E,
      p ∈ MulAction.stabilizer (D ⋊[phi] E) x ↔
        p.right ∈ MulAction.stabilizer E x := by
  let _ := semidirectMulAction phi hcompat
  intro p
  change p.left • (p.right • x) = x ↔ p.right • x = x
  rw [hleft]

/-- Subgroup form of
`mem_semidirect_stabilizer_iff_right_of_left_trivial`: the full stabilizer is
the inverse image of the outer stabilizer under the right projection. -/
theorem semidirect_stabilizer_eq_comap_right_stabilizer_of_left_trivial
    (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi)
    (hleft : ∀ (d : D) (y : X), d • y = y)
    (x : X) :
    letI := semidirectMulAction phi hcompat
    MulAction.stabilizer (D ⋊[phi] E) x =
      (MulAction.stabilizer E x).comap SemidirectProduct.rightHom := by
  let _ := semidirectMulAction phi hcompat
  ext p
  exact mem_semidirect_stabilizer_iff_right_of_left_trivial
    phi hcompat hleft x p

/-- Under a trivial action of the normal factor, every element of the full
stabilizer has its canonical factorization into an arbitrary normal-factor
element and an outer-factor element stabilizing the point. -/
theorem mem_semidirect_stabilizer_iff_exists_right_factorization
    (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi)
    (hleft : ∀ (d : D) (y : X), d • y = y)
    (x : X) :
    letI := semidirectMulAction phi hcompat
    ∀ p : D ⋊[phi] E,
      p ∈ MulAction.stabilizer (D ⋊[phi] E) x ↔
        ∃ d : D, ∃ e : E,
          e ∈ MulAction.stabilizer E x ∧
            p = SemidirectProduct.inl (φ := phi) d *
              SemidirectProduct.inr (φ := phi) e := by
  let _ := semidirectMulAction phi hcompat
  intro p
  rw [mem_semidirect_stabilizer_iff_right_of_left_trivial
    phi hcompat hleft x p]
  constructor
  · intro he
    exact ⟨p.left, p.right, he,
      (SemidirectProduct.inl_left_mul_inr_right p).symm⟩
  · rintro ⟨d, e, he, hp⟩
    rw [hp]
    simpa using he

/-- The same result expressed as an actual factorisation into the two canonical copies.  Every
element of the semidirect-product stabilizer has a unique normal form
`inl d * inr e`, and both factors stabilize `x`. -/
theorem mem_semidirect_stabilizer_iff_exists_factorization (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi) (x : X)
    (hfixed : ∀ e : E, e • x = x) :
    letI := semidirectMulAction phi hcompat
    ∀ p : D ⋊[phi] E,
      p ∈ MulAction.stabilizer (D ⋊[phi] E) x ↔
        ∃ d : D, d ∈ MulAction.stabilizer D x ∧
          ∃ e : E, e ∈ MulAction.stabilizer E x ∧
            p = SemidirectProduct.inl (φ := phi) d * SemidirectProduct.inr (φ := phi) e := by
  let _ := semidirectMulAction phi hcompat
  intro p
  rw [mem_semidirect_stabilizer_iff phi hcompat x hfixed p]
  constructor
  · rintro ⟨hd, he⟩
    exact ⟨p.left, hd, p.right, he, (SemidirectProduct.inl_left_mul_inr_right p).symm⟩
  · rintro ⟨d, hd, e, he, rfl⟩
    simpa using And.intro hd he

end SemidirectStabilizer

section SemidirectEquivariance

variable {D E X Y : Type*} [Group D] [Group E]
variable [MulAction D X] [MulAction E X]
variable [MulAction D Y] [MulAction E Y]

/-- An `E`-equivariant equivalence is equivariant for the compatible
semidirect-product actions when the normal factor `D` acts trivially on both
sets.  This is the elementary equivariance step used when inner
automorphisms act trivially on character and weight classes. -/
theorem equivariant_equiv_semidirect_of_left_trivial
    (phi : E →* MulAut D)
    (hcompatX : SemidirectActionCompatible (X := X) phi)
    (hcompatY : SemidirectActionCompatible (X := Y) phi)
    (f : X ≃ Y)
    (hE : ∀ (e : E) (x : X), f (e • x) = e • f x)
    (hDX : ∀ (d : D) (x : X), d • x = x)
    (hDY : ∀ (d : D) (y : Y), d • y = y) :
    letI := semidirectMulAction phi hcompatX
    letI := semidirectMulAction phi hcompatY
    ∀ p : D ⋊[phi] E, ∀ x, f (p • x) = p • f x := by
  let _ := semidirectMulAction phi hcompatX
  let _ := semidirectMulAction phi hcompatY
  intro p x
  change f (p.left • (p.right • x)) =
    p.left • (p.right • f x)
  rw [hDX, hE, hDY]

end SemidirectEquivariance

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
