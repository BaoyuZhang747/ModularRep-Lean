import ModularRep.PaperProofs.TypeBRankThreeMoritaTensor
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite representations for the same balanced tensor

The actual bimodule remains a Rep object. Finiteness of its module and of the
input passes through the tensor product and the existing coinvariant quotient.
The resulting FDRep functor uses the same residual representation and maps.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaFiniteTensor

open TypeBRankThreeMoritaTensor

universe u

variable {k G L : Type u} [CommRing k] [Group G] [Group L]

/-- Forget only the finiteness packaging, retaining the same representation. -/
abbrev underlyingRep (V : FDRep k L) : Rep k L :=
  (forget₂ (FDRep k L) (Rep k L)).obj V

instance tensorCarrierFinite (M : Rep k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (V : FDRep k L) : Module.Finite k (TensorCarrier M (underlyingRep V)) := by
  letI : Module.Finite k (underlyingRep V) := inferInstanceAs (Module.Finite k V)
  change Module.Finite k (Representation.Coinvariants (delta M (underlyingRep V)))
  infer_instance

/-- The same quotient and residual action, with the derived finite-module instance. -/
abbrev tensorFDObj (M : Rep k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (V : FDRep k L) : FDRep k G :=
  FDRep.of (residualRepresentation M (underlyingRep V))

@[simp] theorem tensorFDObj_rho (M : Rep k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (V : FDRep k L) :
    (tensorFDObj M V).ρ = residualRepresentation M (underlyingRep V) := rfl

@[simp] theorem tensorFDObj_forget (M : Rep k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (V : FDRep k L) :
    (forget₂ (FDRep k G) (Rep k G)).obj (tensorFDObj M V) =
      tensorObj M (underlyingRep V) := rfl

/-- The finite functor retains the literal tensor functor's object and morphism. -/
def tensorFDFunctor (M : Rep k (G × Lᵐᵒᵖ)) [Module.Finite k M] :
    FDRep k L ⥤ FDRep k G where
  obj := tensorFDObj M
  map {V W} f := FDRep.forget₂HomLinearEquiv (tensorFDObj M V) (tensorFDObj M W)
    ((tensorFunctor M).map ((forget₂ (FDRep k L) (Rep k L)).map f))
  map_id V := by
    apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change (tensorFunctor M).map
      ((forget₂ (FDRep k L) (Rep k L)).map (𝟙 V)) = 𝟙 _
    exact (tensorFunctor M).map_id (underlyingRep V)
  map_comp f g := by
    apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change (tensorFunctor M).map ((forget₂ (FDRep k L) (Rep k L)).map (f ≫ g)) =
      (tensorFunctor M).map ((forget₂ (FDRep k L) (Rep k L)).map f) ≫
        (tensorFunctor M).map ((forget₂ (FDRep k L) (Rep k L)).map g)
    simp only [Functor.map_comp]

@[simp] theorem tensorFDFunctor_obj (M : Rep k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (V : FDRep k L) : (tensorFDFunctor M).obj V = tensorFDObj M V := rfl

@[simp] theorem tensorFDFunctor_map_forget (M : Rep k (G × Lᵐᵒᵖ))
    [Module.Finite k M] {V W : FDRep k L} (f : V ⟶ W) :
    (forget₂ (FDRep k G) (Rep k G)).map ((tensorFDFunctor M).map f) =
      (tensorFunctor M).map ((forget₂ (FDRep k L) (Rep k L)).map f) := rfl

@[simp] theorem tensorFDFunctor_map_class (M : Rep k (G × Lᵐᵒᵖ))
    [Module.Finite k M] {V W : FDRep k L} (f : V ⟶ W) (m : M) (v : V) :
    ((forget₂ (FDRep k G) (Rep k G)).map ((tensorFDFunctor M).map f)).hom
        (tensorClass M (underlyingRep V) m v) =
      tensorClass M (underlyingRep W) m
        (((forget₂ (FDRep k L) (Rep k L)).map f).hom v) := rfl

/-- Restrict the same functor to supported objects using only support preservation. -/
def supportedTensorFDFunctor (M : Rep k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (eL : k[L]) (eG : k[G])
    (maps : ∀ V : FDRep k L, supported eL V → supported eG (tensorFDObj M V)) :
    SupportedFDRep eL ⥤ SupportedFDRep eG :=
  (supported eG).lift ((supported eL).ι ⋙ tensorFDFunctor M)
    (fun V => maps V.obj V.property)

@[simp] theorem supportedTensorFDFunctor_obj (M : Rep k (G × Lᵐᵒᵖ))
    [Module.Finite k M] (eL : k[L]) (eG : k[G])
    (maps : ∀ V : FDRep k L, supported eL V → supported eG (tensorFDObj M V))
    (V : SupportedFDRep eL) :
    ((supportedTensorFDFunctor M eL eG maps).obj V).obj = tensorFDObj M V.obj := rfl

@[simp] theorem supportedTensorFDFunctor_map (M : Rep k (G × Lᵐᵒᵖ))
    [Module.Finite k M] (eL : k[L]) (eG : k[G])
    (maps : ∀ V : FDRep k L, supported eL V → supported eG (tensorFDObj M V))
    {V W : SupportedFDRep eL} (f : V ⟶ W) :
    ((supportedTensorFDFunctor M eL eG maps).map f).hom =
      (tensorFDFunctor M).map f.hom := rfl

/-- Ordinary restriction of finite representations along the displayed hom. -/
def fdRestriction {H : Type u} [Group H] (f : H →* G) : FDRep k G ⥤ FDRep k H :=
  Action.res (FGModuleCat k) f

@[simp] theorem fdRestriction_rho {H : Type u} [Group H] (f : H →* G)
    (V : FDRep k G) : ((fdRestriction (k := k) f).obj V).ρ = V.ρ.comp f := by
  ext h v
  rfl

@[simp] theorem fdRestriction_map_hom {H : Type u} [Group H] (f : H →* G)
    {V W : FDRep k G} (g : V ⟶ W) :
    ((fdRestriction (k := k) f).map g).hom = g.hom := rfl

end ModularRep.PaperProofs.TypeBRankThreeMoritaFiniteTensor


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
