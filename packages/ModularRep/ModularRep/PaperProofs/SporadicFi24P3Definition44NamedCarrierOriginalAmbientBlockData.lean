import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
import ModularRep.Navarro414IntervalCentralCharacterAdapter

/-! Unselected specified block catalogues on the actual ambient and local
group. The normalizer interval is derived from the original raw radical. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbientBlockData

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H
local instance problemPrime (P : Definition35Problem.{u}) : Fact P.p.Prime := ⟨P.iota.prime⟩

theorem originalNormalizerInterval
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H) (B : OriginalSpathAmbient P psi)
    (C : OriginalLocalNormalizerData P psi V B) :
    CentralBrauerInterval (p := P.p) (V.subgroup.map B.rawMap) C.D := by
  rw [C.D_eq]
  exact {
    isPGroup := V.radical.isPGroup.map B.rawMap
    pCentralizer_le := sup_le (V.subgroup.map B.rawMap).le_normalizer
      (Subgroup.centralizer_le_normalizer _)
    le_normalizer := le_rfl }

structure OriginalAmbientBlockData
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H) (B : OriginalSpathAmbient P psi)
    (C : OriginalLocalNormalizerData P psi V B) where
  AmbientBlock : Type u
  LocalBlock : Type u
  [ambientFintype : Fintype AmbientBlock]
  [localFintype : Fintype LocalBlock]
  ambientIdempotent : AmbientBlock → P.k[B.A]
  localIdempotent : LocalBlock → P.k[C.D]
  ambientBlocks : BlockIdempotentDecomposition ambientIdempotent
  localBlocks : BlockIdempotentDecomposition localIdempotent
  ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks
  localCatalogue : BlockCentralCharacterCatalogue localBlocks
  intervalLaw : Navarro414IntervalCentralCharacterSource
    (originalNormalizerInterval P psi V B C) localBlocks localCatalogue

attribute [instance] OriginalAmbientBlockData.ambientFintype OriginalAmbientBlockData.localFintype

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbientBlockData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
