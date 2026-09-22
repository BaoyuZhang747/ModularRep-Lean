import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer

/-! Literal group identifications at Q=1. The existing actual local group,
equivalence and original map are retained for the common-extension branch. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneGroups

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer

universe u

variable {P : Definition35Problem.{u}} {psi : Definition35Brauer P}
variable {V : CharacterWeight P.p P.K P.H} {B : OriginalSpathAmbient P psi}

namespace OriginalLocalNormalizerData

variable (C : OriginalLocalNormalizerData P psi V B)

theorem D_eq_top (hV : V.subgroup = ⊥) : C.D = ⊤ := by
  rw [C.D_eq, hV, Subgroup.map_bot]
  exact Subgroup.normalizer_eq_top (⊥ : Subgroup B.A)

def qOneLocalEquiv (hV : V.subgroup = ⊥) : C.D ≃* B.A :=
  (MulEquiv.subgroupCongr (D_eq_top C hV)).trans Subgroup.topEquiv

theorem qOneLocalEquiv_toMonoidHom (hV : V.subgroup = ⊥) :
    (qOneLocalEquiv C hV).toMonoidHom = C.D.subtype := by
  ext x
  rfl

theorem qOneLocalMap_square (hV : V.subgroup = ⊥) :
    (qOneLocalEquiv C hV).toMonoidHom.comp C.localMap =
      B.rawMap.comp (Subgroup.normalizer (V.subgroup : Set P.H)).subtype := by
  rw [qOneLocalEquiv_toMonoidHom]
  exact C.localMap_natural

def qOneBaseEquiv (hV : V.subgroup = ⊥) : B.base ≃* C.localBase where
  toFun x := ⟨⟨x.1, by rw [D_eq_top C hV]; exact Subgroup.mem_top _⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem qOneBase_square (hV : V.subgroup = ⊥) :
    (qOneLocalEquiv C hV).toMonoidHom.comp C.localBase.subtype =
      B.base.subtype.comp (qOneBaseEquiv C hV).symm.toMonoidHom := by
  ext x
  rfl

end OriginalLocalNormalizerData

def qOneOwnNormalizerEquiv
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H) (hV : V.subgroup = ⊥) :
    Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
      Set (CentralCharacterQuotient P psi)) ≃* CentralCharacterQuotient P psi :=
  (MulEquiv.subgroupCongr (by
    rw [hV, Subgroup.map_bot]
    exact Subgroup.normalizer_eq_top (⊥ : Subgroup (CentralCharacterQuotient P psi)))).trans
    Subgroup.topEquiv

theorem qOneOwnNormalizerEquiv_square
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H) (hV : V.subgroup = ⊥) :
    (qOneOwnNormalizerEquiv P psi V hV).toMonoidHom.comp (ownNormalizerMap P psi V) =
      (centralCharacterQuotientMap P psi).comp
        (Subgroup.normalizer (V.subgroup : Set P.H)).subtype := by
  ext n
  rfl

namespace OriginalLocalNormalizerData

theorem qOneBaseEquiv_symm_eM (C : OriginalLocalNormalizerData P psi V B)
    (hV : V.subgroup = ⊥)
    (n : Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
      Set (CentralCharacterQuotient P psi))) :
    (qOneBaseEquiv C hV).symm (C.eM n) =
      B.baseEquiv (qOneOwnNormalizerEquiv P psi V hV n) := by
  apply Subtype.ext
  exact DFunLike.congr_fun C.eM_natural n

end OriginalLocalNormalizerData

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneGroups


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
