import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityPacket

/-! Unselected quotient catalogues and the already used generic lower
laws. The indices retain psi and V. The descriptor contains no newly
selected character, matched block, extension, induction equality,
correspondence or packet. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

universe u

local instance problemPrime (P : Definition35Problem.{u}) : Fact P.p.Prime := ⟨P.iota.prime⟩
local instance quotientFintype (P : Definition35Problem.{u}) (psi : Definition35Brauer P) :
    Fintype (CentralCharacterQuotient P psi) := Fintype.ofFinite _
local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

structure OriginalQuotientData (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H) (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H)) where
  normalizers : NavarroTiep23cFixedCentralQuotientSource
    (centralCharacterKernel P psi) inf_le_left (centralKernel_primeTo P psi hcenter) V.subgroup V.radical
  GlobalBlock : Type u
  LocalBlock : Type u
  [fintypeGlobalBlock : Fintype GlobalBlock]
  [fintypeLocalBlock : Fintype LocalBlock]
  globalIdempotent : GlobalBlock → P.k[CentralCharacterQuotient P psi]
  localIdempotent : LocalBlock → P.k[Subgroup.normalizer
    (V.subgroup.map (centralCharacterQuotientMap P psi) : Set (CentralCharacterQuotient P psi))]
  globalBlocks : BlockIdempotentDecomposition globalIdempotent
  localBlocks : BlockIdempotentDecomposition localIdempotent
  globalCatalogue : BlockCentralCharacterCatalogue globalBlocks
  localCatalogue : BlockCentralCharacterCatalogue localBlocks
  intervalLaw : Navarro414IntervalCentralCharacterSource
    (ownNormalizerInterval P psi V (centralKernel_primeTo P psi hcenter) normalizers)
    localBlocks localCatalogue
  globalImageLaw : CentralPrimeToPrimitiveImageSource (k := P.k)
    (centralCharacterQuotientMap P psi) (QuotientGroup.mk'_surjective _) P.iota.prime
    (own_quotient_ker_central P psi) (own_quotient_ker_primeTo P psi (centralKernel_primeTo P psi hcenter))
  localImageLaw : CentralPrimeToPrimitiveImageSource (k := P.k)
    (ownNormalizerMap P psi V)
    (ownNormalizerMap_surjective P psi V (centralKernel_primeTo P psi hcenter) normalizers) P.iota.prime
    (own_normalizer_ker_central P psi V)
    (own_normalizer_ker_primeTo P psi V (centralKernel_primeTo P psi hcenter))

attribute [instance] OriginalQuotientData.fintypeGlobalBlock OriginalQuotientData.fintypeLocalBlock

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
