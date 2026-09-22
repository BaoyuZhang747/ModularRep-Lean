import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

/-! Internal literal packet over the original character's own quotient.
The raw map has its exact central kernel. The ambient quotient describes
the original group's stabilizer, and the raw weight remains an index. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

theorem centralKernel_primeTo (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H)) :
    ¬ P.p ∣ Nat.card (centralCharacterKernel P psi) := by
  intro h
  exact hcenter (h.trans (Subgroup.card_dvd_of_le
    (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)))

structure OriginalActualWeightPacket (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) (V : CharacterWeight P.p P.K P.H) where
  quotient : CentralQuotientBrauerSource P psi psi
  ambient : OriginalSpathAmbient P psi
  localGroup : Subgroup ambient.A
  localGroup_eq : localGroup =
    Subgroup.normalizer (V.subgroup.map ambient.rawMap : Set ambient.A)
  localMap : Subgroup.normalizer (V.subgroup : Set P.H) →* localGroup
  localMap_natural : localGroup.subtype.comp localMap =
    ambient.rawMap.comp (Subgroup.normalizer (V.subgroup : Set P.H)).subtype
  localMap_range : localMap.range = ambient.base.comap localGroup.subtype
  globalRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A
  globalCharacter : IBr globalRoot
  globalRestriction : PrimeRegularClassFunction.pullback ambient.rawMap globalCharacter.1 = psi.1.1
  localRoot : PrimeRegularRootEmbedding P.p P.k P.K localGroup
  localCharacter : IBr localRoot
  localRestriction : ∀ n : PrimeRegularElement
      (G := Subgroup.normalizer (V.subgroup : Set P.H)) P.p,
    localCharacter.1 (PrimeRegularElement.map localMap n) = V.localCharacter (QuotientGroup.mk n.1)
  intermediateBlocks : ∀ J : Subgroup ambient.A, ambient.base ≤ J →
    ActualIntermediateBlockData P localGroup globalCharacter.1 localCharacter.1 J
  qOne : V.subgroup = ⊥ →
    PrimeRegularClassFunction.pullback localGroup.subtype globalCharacter.1 = localCharacter.1

namespace OriginalActualWeightPacket

variable {P : Definition35Problem.{u}} {psi : Definition35Brauer P}
variable {V : CharacterWeight P.p P.K P.H} (packet : OriginalActualWeightPacket P psi V)

theorem rawMap_ker : packet.ambient.rawMap.ker = centralCharacterKernel P psi :=
  packet.ambient.rawMap_ker

theorem quotientEmbedding_injective : Function.Injective packet.ambient.quotientEmbedding :=
  packet.ambient.quotientEmbedding_injective

end OriginalActualWeightPacket

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
