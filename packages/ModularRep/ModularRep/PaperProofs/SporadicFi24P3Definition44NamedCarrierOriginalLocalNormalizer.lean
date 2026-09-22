import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer

/-! An internal output component for the actual original-cover packet.
The local map is defined from the own-normalizer equivalence; its natural
square and range are deductions. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialCentralSector
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot

universe u

structure OriginalLocalNormalizerData
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H) (B : OriginalSpathAmbient P psi) where
  D : Subgroup B.A
  D_eq : D = Subgroup.normalizer (V.subgroup.map B.rawMap : Set B.A)
  eM : Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
      Set (CentralCharacterQuotient P psi)) ≃* B.base.comap D.subtype
  eM_natural : D.subtype.comp ((B.base.comap D.subtype).subtype.comp eM.toMonoidHom) =
    B.quotientEmbedding.comp (Subgroup.normalizer
      (V.subgroup.map (centralCharacterQuotientMap P psi) :
        Set (CentralCharacterQuotient P psi))).subtype

namespace OriginalLocalNormalizerData

variable {P : Definition35Problem.{u}} {psi : Definition35Brauer P}
variable {V : CharacterWeight P.p P.K P.H} {B : OriginalSpathAmbient P psi}
variable (C : OriginalLocalNormalizerData P psi V B)

abbrev localBase : Subgroup C.D := B.base.comap C.D.subtype

def localMap : Subgroup.normalizer (V.subgroup : Set P.H) →* C.D :=
  C.localBase.subtype.comp (C.eM.toMonoidHom.comp (ownNormalizerMap P psi V))

theorem localMap_natural : C.D.subtype.comp C.localMap =
    B.rawMap.comp (Subgroup.normalizer (V.subgroup : Set P.H)).subtype := by
  ext n
  exact DFunLike.congr_fun C.eM_natural (ownNormalizerMap P psi V n)

local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩

theorem localMap_range
    (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))
    (normalizers : NavarroTiep23cFixedCentralQuotientSource
      (centralCharacterKernel P psi)
      (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
      hprimeTo V.subgroup V.radical) : C.localMap.range = B.base.comap C.D.subtype := by
  let f := C.eM.toMonoidHom.comp (ownNormalizerMap P psi V)
  have hf : Function.Surjective f := C.eM.surjective.comp
    (ownNormalizerMap_surjective P psi V hprimeTo normalizers)
  change (C.localBase.subtype.comp f).range = C.localBase
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end OriginalLocalNormalizerData

def actualLocalNormalizerData
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H)
    {S : Type u} [Group S] (q : P.H →* S)
    (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
      psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
        psi.1.1 ⟨1, isPrimeRegular_one⟩) :
    OriginalLocalNormalizerData P psi V
      (trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal) := by
  let : Group.IsPerfect P.H := ⟨perfect_of_universalCentralExtension q hq⟩
  let B := trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal
  let r := centralCharacterQuotientMap P psi
  let i : CentralCharacterQuotient P psi →* B.A :=
    innerEmbedding (quotientRoot P.iota (centralCharacterKernel P psi)) (ownQuotientBrauer P psi)
  let Qbar := V.subgroup.map r
  let D := embeddedNormalizer i Qbar
  have hi : Function.Injective i :=
    innerEmbedding_injective _ (ownQuotientBrauer P psi)
      (ownQuotient_center_eq_bot P psi
        (centralCharacterKernel_eq_center_of_trivial_sector P psi hcenter hglobal))
  have hrawMap : B.rawMap = i.comp r := by ext x; rfl
  refine {
    D := D
    D_eq := ?_
    eM := normalizerBaseEquiv i hi Qbar
    eM_natural := ?_ }
  · change Subgroup.normalizer ((V.subgroup.map r).map i : Set B.A) = _
    rw [Subgroup.map_map, ← hrawMap]
  · ext n
    rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
