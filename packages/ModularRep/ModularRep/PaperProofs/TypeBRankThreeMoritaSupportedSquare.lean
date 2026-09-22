import ModularRep.PaperProofs.TypeBRankThreeMoritaExtensionTransport
import ModularRep.PaperProofs.TypeBRankThreeMoritaSupportTransport
import Mathlib.CategoryTheory.Equivalence

/-!
# The supported restriction square and honest extensions

The full finite-representation square restricts to the supported
subcategories with the same object maps. The resulting equivalences
transport extension existence. The extension representations act on the
original vector spaces, obtained by the existing isomorphism conjugation.
These are intermediate deductions; a specified application constructs the
tensor objects, support maps, equivalences and square used here.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaSupportedSquare

open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaSources TypeBRankThreeMoritaSupportTransport
open TypeBRankThreeMoritaExtensionTransport

universe u

variable {k G H L Q : Type u} [Field k]
  [Group G] [Group H] [Group L] [Group Q]

/-- An extension on the original vector space, along the given map. -/
def HonestExtensionAlong (f : H →* G) (V : FDRep k H) : Prop :=
  ∃ rho : Representation k G V,
    Nonempty (Representation.Equiv (rho.comp f) V.ρ)

/-- An isomorphism after restriction transports the upper action to V itself. -/
theorem honestExtensionAlong_of_restrictionIso
    (f : H →* G) (V : FDRep k H) (U : FDRep k G)
    (i : (fdRestriction f).obj U ≅ V) : HonestExtensionAlong f V := by
  let e : U ≃ₗ[k] V := FDRep.isoToLinearEquiv i
  let rho : Representation k G V := e.conjRingEquiv.toMonoidHom.comp U.ρ
  have restriction : rho.comp f = V.ρ := by
    ext h v
    change e.conj (U.ρ (f h)) v = V.ρ h v
    have hi := FDRep.Iso.conj_ρ i h
    rw [fdRestriction_rho] at hi
    exact congrArg (fun t : Module.End k V => t v) hi.symm
  refine ⟨rho, ?_⟩
  rw [restriction]
  exact ⟨Representation.Equiv.refl _⟩

/-- An extension supplies the corresponding finite restriction isomorphism. -/
theorem restrictionIso_of_honestExtensionAlong
    (f : H →* G) (V : FDRep k H) (h : HonestExtensionAlong f V) :
    ∃ U : FDRep k G, Nonempty ((fdRestriction f).obj U ≅ V) := by
  obtain ⟨rho, ⟨e⟩⟩ := h
  let U : FDRep k G := FDRep.of rho
  refine ⟨U, ⟨?_⟩⟩
  apply (forget₂ (FDRep k H) (Rep k H)).preimageIso
  exact Rep.mkIso e

/-- Supported restriction has precisely the honest extensions of the same object. -/
theorem supported_essImage_iff_honestExtension
    (f : H →* G) (e : k[H]) (V : SupportedFDRep e) :
    (supportedRestriction f e).essImage V ↔ HonestExtensionAlong f V.obj := by
  constructor
  · intro h
    obtain ⟨U, ⟨i⟩⟩ := h
    exact honestExtensionAlong_of_restrictionIso f V.obj U.obj
      ((supported e).ι.mapIso i)
  · intro h
    obtain ⟨U, ⟨i⟩⟩ := restrictionIso_of_honestExtensionAlong f V.obj h
    have hU : supported (MonoidAlgebra.mapDomainRingHom k f e) U :=
      (supported_mapDomain_iff f e U).mpr
        (supported_of_iso e i.symm V.property)
    exact ⟨⟨U, hU⟩, ⟨(supported e).isoMk i⟩⟩

section Square

variable (aG : Q →* MulAut G) (aL : Q →* MulAut L)
  (eG : k[G]) (eL : k[L])
  (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
  (Mhat : Rep.{u} k ((G ⋊[aG] Q) × (L ⋊[aL] Q)ᵐᵒᵖ))
  [Module.Finite k Mhat]
  (baseMaps : ∀ V : FDRep k L,
    supported eL V → supported eG (tensorFDObj M V))
  (upperMaps : ∀ V : FDRep k (L ⋊[aL] Q),
    supported (inlImage aL eL) V →
      supported (inlImage aG eG) (tensorFDObj Mhat V))
  (square :
    (tensorFDFunctor Mhat ⋙
      fdRestriction (SemidirectProduct.inl : G →* G ⋊[aG] Q)) ≅
    (fdRestriction (SemidirectProduct.inl : L →* L ⋊[aL] Q) ⋙
      tensorFDFunctor M))

/-- Lift the same natural isomorphism to the full supported subcategories. -/
def supportedSquare :
    (supportedTensorFDFunctor Mhat (inlImage aL eL) (inlImage aG eG) upperMaps ⋙
      supportedInlRestriction aG eG) ≅
    (supportedInlRestriction aL eL ⋙ supportedTensorFDFunctor M eL eG baseMaps) :=
  NatIso.ofComponents
    (fun V => (supported eG).isoMk (square.app V.obj))
    (by
      intro V W f
      apply (supported eG).ι.map_injective
      exact square.hom.naturality f.hom)

include square

/-- The two actual supported tensor equivalences transport supported lifts. -/
theorem supported_essentialImage_iff
    (baseEquivalence : (supportedTensorFDFunctor M eL eG baseMaps).IsEquivalence)
    (upperEquivalence :
      (supportedTensorFDFunctor Mhat (inlImage aL eL) (inlImage aG eG)
        upperMaps).IsEquivalence)
    (W : SupportedFDRep eL) :
    (supportedInlRestriction aL eL).essImage W ↔
      (supportedInlRestriction aG eG).essImage
        ((supportedTensorFDFunctor M eL eG baseMaps).obj W) := by
  letI := baseEquivalence
  letI := upperEquivalence
  exact essentialImage_iff_of_square
    (supportedTensorFDFunctor M eL eG baseMaps)
    (supportedTensorFDFunctor Mhat (inlImage aL eL) (inlImage aG eG) upperMaps)
    (supportedInlRestriction aL eL) (supportedInlRestriction aG eG)
    (supportedSquare aG aL eG eL M Mhat baseMaps upperMaps square) W

/-- Extension existence for W and its literal balanced tensor image. -/
theorem honestExtension_iff
    (baseEquivalence : (supportedTensorFDFunctor M eL eG baseMaps).IsEquivalence)
    (upperEquivalence :
      (supportedTensorFDFunctor Mhat (inlImage aL eL) (inlImage aG eG)
        upperMaps).IsEquivalence)
    (W : FDRep k L) (hW : supported eL W) :
    HonestExtensionAlong (SemidirectProduct.inl : L →* L ⋊[aL] Q) W ↔
      HonestExtensionAlong (SemidirectProduct.inl : G →* G ⋊[aG] Q)
        (tensorFDObj M W) := by
  let V : SupportedFDRep eL := ⟨W, hW⟩
  exact
    (supported_essImage_iff_honestExtension
      (SemidirectProduct.inl : L →* L ⋊[aL] Q) eL V).symm.trans
      ((supported_essentialImage_iff aG aL eG eL M Mhat baseMaps upperMaps
        square baseEquivalence upperEquivalence V).trans
        (supported_essImage_iff_honestExtension
          (SemidirectProduct.inl : G →* G ⋊[aG] Q) eG
          ((supportedTensorFDFunctor M eL eG baseMaps).obj V)))

end Square

end ModularRep.PaperProofs.TypeBRankThreeMoritaSupportedSquare


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
