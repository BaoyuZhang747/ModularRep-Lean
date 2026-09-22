import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.FDRep
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
Literal balanced tensor for a representation of G times the opposite of L.
The quotient, residual action and maps are fixed before any Morita hypothesis.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaTensor

universe u

variable {k G L : Type u} [CommRing k] [Group G] [Group L]

/-- The inverse-opposite map gives the balancing action of L. -/
def balancingIn : L →* G × Lᵐᵒᵖ :=
  (1 : L →* G).prod (MulEquiv.inv' L).toMonoidHom

@[simp]
theorem balancingIn_apply (l : L) :
    balancingIn (G := G) l = (1, MulOpposite.op (l⁻¹)) := rfl

/-- Restrict the right action with the inverse required by balancing. -/
abbrev balancingRepresentation (M : Rep k (G × Lᵐᵒᵖ)) :
    Representation k L M :=
  M.ρ.comp balancingIn

/-- The diagonal action whose coinvariants are the balanced tensor. -/
abbrev delta (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L) :
    Representation k L (M ⊗[k] V) :=
  (balancingRepresentation M).tprod V.ρ

/-- The actual coinvariant quotient, with no replacement carrier. -/
abbrev TensorCarrier (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L) :=
  Representation.Coinvariants (delta M V)

/-- The class of a literal elementary tensor. -/
def tensorClass (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L)
    (m : M) (v : V) : TensorCarrier M V :=
  Representation.Coinvariants.mk (delta M V) (m ⊗ₜ[k] v)

@[simp]
theorem delta_tmul (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L)
    (l : L) (m : M) (v : V) :
    delta M V l (m ⊗ₜ[k] v) =
      M.ρ (1, MulOpposite.op (l⁻¹)) m ⊗ₜ[k] V.ρ l v := rfl

theorem tensorClass_diagonal (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L)
    (l : L) (m : M) (v : V) :
    tensorClass M V (M.ρ (1, MulOpposite.op (l⁻¹)) m) (V.ρ l v) =
      tensorClass M V m v :=
  Representation.Coinvariants.mk_self_apply (delta M V) l (m ⊗ₜ[k] v)

@[ext]
theorem tensorLinearMap_ext (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L)
    {W : Type*} [AddCommGroup W] [Module k W]
    {f g : TensorCarrier M V →ₗ[k] W}
    (h : ∀ m v, f (tensorClass M V m v) = g (tensorClass M V m v)) :
    f = g := by
  apply Representation.Coinvariants.hom_ext
  apply TensorProduct.ext'
  exact h

/-- The commuting left action is an endomorphism of the balancing representation. -/
def leftIntertwiner (M : Rep k (G × Lᵐᵒᵖ)) (g : G) :
    (balancingRepresentation M).IntertwiningMap (balancingRepresentation M) where
  toLinearMap := M.ρ (g, 1)
  isIntertwining' l := by
    change M.ρ (g, 1) * M.ρ (1, MulOpposite.op (l⁻¹)) =
      M.ρ (1, MulOpposite.op (l⁻¹)) * M.ρ (g, 1)
    rw [← map_mul, ← map_mul]
    simp

/-- Descend the literal left tensor action to the fixed quotient. -/
def residualMap (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L) (g : G) :
    TensorCarrier M V →ₗ[k] TensorCarrier M V :=
  Representation.Coinvariants.map _ _ ((leftIntertwiner M g).rTensor V.ρ)

@[simp]
theorem residualMap_class (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L)
    (g : G) (m : M) (v : V) :
    residualMap M V g (tensorClass M V m v) =
      tensorClass M V (M.ρ (g, 1) m) v := rfl

/-- The residual G representation on the actual coinvariant carrier. -/
def residualRepresentation (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L) :
    Representation k G (TensorCarrier M V) where
  toFun := residualMap M V
  map_one' := by
    apply tensorLinearMap_ext M V
    intro m v
    change tensorClass M V (M.ρ 1 m) v = tensorClass M V m v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply tensorLinearMap_ext M V
    intro m v
    change tensorClass M V (M.ρ (g * h, 1) m) v =
      tensorClass M V (M.ρ (g, 1) (M.ρ (h, 1) m)) v
    have hm : M.ρ (g * h, 1) = M.ρ (g, 1) * M.ρ (h, 1) := by
      simpa using M.ρ.map_mul (g, 1) (h, 1)
    rw [hm]
    rfl

@[simp]
theorem residualRepresentation_class (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L)
    (g : G) (m : M) (v : V) :
    residualRepresentation M V g (tensorClass M V m v) =
      tensorClass M V (M.ρ (g, 1) m) v := rfl

/-- The canonical map induced by id M tensor f. -/
def tensorLinearMap (M : Rep k (G × Lᵐᵒᵖ)) {V W : Rep k L} (f : V ⟶ W) :
    TensorCarrier M V →ₗ[k] TensorCarrier M W :=
  Representation.Coinvariants.map _ _
    (f.hom.lTensor (balancingRepresentation M))

@[simp]
theorem tensorLinearMap_class (M : Rep k (G × Lᵐᵒᵖ)) {V W : Rep k L}
    (f : V ⟶ W) (m : M) (v : V) :
    tensorLinearMap M f (tensorClass M V m v) =
      tensorClass M W m (f.hom v) := rfl

/-- The exact tensor map is equivariant for the residual actions. -/
def tensorIntertwiner (M : Rep k (G × Lᵐᵒᵖ)) {V W : Rep k L} (f : V ⟶ W) :
    (residualRepresentation M V).IntertwiningMap (residualRepresentation M W) where
  toLinearMap := tensorLinearMap M f
  isIntertwining' g := by
    apply tensorLinearMap_ext M V
    intro m v
    rfl

/-- The actual representation object used by the tensor functor. -/
abbrev tensorObj (M : Rep k (G × Lᵐᵒᵖ)) (V : Rep k L) : Rep k G :=
  Rep.of (residualRepresentation M V)

/-- The balanced tensor functor of the displayed bimodule. -/
def tensorFunctor (M : Rep k (G × Lᵐᵒᵖ)) : Rep k L ⥤ Rep k G where
  obj := tensorObj M
  map f := Rep.ofHom (tensorIntertwiner M f)
  map_id V := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply tensorLinearMap_ext M V
    intro m v
    rfl
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply tensorLinearMap_ext M _
    intro m v
    rfl

@[simp]
theorem tensorFunctor_map_class (M : Rep k (G × Lᵐᵒᵖ)) {V W : Rep k L}
    (f : V ⟶ W) (m : M) (v : V) :
    ((tensorFunctor M).map f).hom (tensorClass M V m v) =
      tensorClass M W m (f.hom v) := rfl

/-- Literal support by one specified group algebra idempotent. -/
def supported (e : k[G]) : ObjectProperty (FDRep k G) :=
  fun V => Representation.asAlgebraHom V.ρ e = 1

/-- All finite representations supported by the specified algebra element. -/
abbrev SupportedFDRep (e : k[G]) := (supported e).FullSubcategory

theorem supported_iff (e : k[G]) (V : FDRep k G) :
    supported e V ↔ ∀ v : V, Representation.asAlgebraHom V.ρ e v = v := by
  constructor
  · intro h v
    change Representation.asAlgebraHom V.ρ e = 1 at h
    rw [h]
    rfl
  · intro h
    change Representation.asAlgebraHom V.ρ e = 1
    exact LinearMap.ext h

end ModularRep.PaperProofs.TypeBRankThreeMoritaTensor


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
