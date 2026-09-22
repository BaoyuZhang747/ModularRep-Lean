import ModularRep.PaperProofs.TypeBRankThreeMoritaSources

/-!
# Support under the literal restriction and an isomorphism

The group algebra image and finite-representation restriction use the same
displayed homomorphism. Support is also preserved by the existing linear
isomorphism of finite representations. Neither statement needs a new source
principle or a choice of representation.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaSupportTransport

open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaSources

universe u

variable {k G H Q : Type u} [CommRing k] [Group G] [Group H] [Group Q]

/-- The algebra action of the image is the algebra action after restriction. -/
theorem asAlgebraHom_mapDomain (f : H →* G) (e : k[H]) (V : FDRep k G) :
    Representation.asAlgebraHom V.ρ (MonoidAlgebra.mapDomainRingHom k f e) =
      Representation.asAlgebraHom ((fdRestriction f).obj V).ρ e := by
  rw [fdRestriction_rho]
  induction e using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero] <;> rfl
  | add x y hx hy => simp only [map_add, hx, hy] <;> rfl
  | single h c =>
      change Representation.asAlgebraHom V.ρ
          (MonoidAlgebra.mapDomain f (MonoidAlgebra.single h c)) =
        Representation.asAlgebraHom (V.ρ.comp f) (MonoidAlgebra.single h c)
      simp only [MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single,
        MonoidHom.comp_apply] <;> rfl

/-- Support by the image is exactly support after the same restriction. -/
theorem supported_mapDomain_iff (f : H →* G) (e : k[H]) (V : FDRep k G) :
    supported (MonoidAlgebra.mapDomainRingHom k f e) V ↔
      supported e ((fdRestriction f).obj V) := by
  change Representation.asAlgebraHom V.ρ (MonoidAlgebra.mapDomainRingHom k f e) = 1 ↔
    Representation.asAlgebraHom ((fdRestriction f).obj V).ρ e = 1
  rw [asAlgebraHom_mapDomain] <;> rfl

/-- The split-overgroup image uses its actual base inclusion. -/
theorem supported_inlImage_iff (a : Q →* MulAut G) (e : k[G])
    (V : FDRep k (G ⋊[a] Q)) :
    supported (inlImage a e) V ↔
      supported e
        ((fdRestriction (SemidirectProduct.inl : G →* G ⋊[a] Q)).obj V) :=
  supported_mapDomain_iff (SemidirectProduct.inl : G →* G ⋊[a] Q) e V

/-- The existing conjugacy of group actions extends to their algebra actions. -/
theorem asAlgebraHom_iso_conj {V W : FDRep k G} (i : V ≅ W) (e : k[G]) :
    Representation.asAlgebraHom W.ρ e =
      (FDRep.isoToLinearEquiv i).conj (Representation.asAlgebraHom V.ρ e) := by
  induction e using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g c =>
      simpa only [Representation.asAlgebraHom_single, map_smul] using
        congrArg (fun t : Module.End k W => c • t) (FDRep.Iso.conj_ρ i g)

/-- Transport support using the same finite-representation isomorphism. -/
theorem supported_of_iso (e : k[G]) {V W : FDRep k G} (i : V ≅ W)
    (h : supported e V) : supported e W := by
  change Representation.asAlgebraHom V.ρ e = 1 at h
  change Representation.asAlgebraHom W.ρ e = 1
  rw [asAlgebraHom_iso_conj i e, h]
  change (FDRep.isoToLinearEquiv i).conj LinearMap.id = LinearMap.id
  exact LinearEquiv.conj_id _

/-- The support predicate is invariant under an actual isomorphism. -/
theorem supported_iso_iff (e : k[G]) {V W : FDRep k G} (i : V ≅ W) :
    supported e V ↔ supported e W :=
  ⟨supported_of_iso e i, supported_of_iso e i.symm⟩

/-- Restrict the same finite representations to their supported subcategories. -/
def supportedRestriction (f : H →* G) (e : k[H]) :
    SupportedFDRep (MonoidAlgebra.mapDomainRingHom k f e) ⥤ SupportedFDRep e :=
  (supported e).lift
    ((supported (MonoidAlgebra.mapDomainRingHom k f e)).ι ⋙ fdRestriction f)
    (fun V => (supported_mapDomain_iff f e V.obj).mp V.property)

@[simp] theorem supportedRestriction_obj (f : H →* G) (e : k[H])
    (V : SupportedFDRep (MonoidAlgebra.mapDomainRingHom k f e)) :
    ((supportedRestriction f e).obj V).obj = (fdRestriction f).obj V.obj := rfl

@[simp] theorem supportedRestriction_map (f : H →* G) (e : k[H])
    {V W : SupportedFDRep (MonoidAlgebra.mapDomainRingHom k f e)} (g : V ⟶ W) :
    ((supportedRestriction f e).map g).hom = (fdRestriction f).map g.hom := rfl

/-- Supported restriction along the actual semidirect-product base inclusion. -/
abbrev supportedInlRestriction (a : Q →* MulAut G) (e : k[G]) :
    SupportedFDRep (inlImage a e) ⥤ SupportedFDRep e :=
  supportedRestriction (SemidirectProduct.inl : G →* G ⋊[a] Q) e

@[simp] theorem supportedInlRestriction_obj (a : Q →* MulAut G) (e : k[G])
    (V : SupportedFDRep (inlImage a e)) :
    ((supportedInlRestriction a e).obj V).obj =
      (fdRestriction (SemidirectProduct.inl : G →* G ⋊[a] Q)).obj V.obj := rfl

@[simp] theorem supportedInlRestriction_map (a : Q →* MulAut G) (e : k[G])
    {V W : SupportedFDRep (inlImage a e)} (g : V ⟶ W) :
    ((supportedInlRestriction a e).map g).hom =
      (fdRestriction (SemidirectProduct.inl : G →* G ⋊[a] Q)).map g.hom := rfl

end ModularRep.PaperProofs.TypeBRankThreeMoritaSupportTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
