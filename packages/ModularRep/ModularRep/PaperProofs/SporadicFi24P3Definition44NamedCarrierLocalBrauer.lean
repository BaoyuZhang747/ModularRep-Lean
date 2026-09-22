import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSourceHBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralLift

/-! The local irreducible Brauer character in Spath 4.1(iii)(3) is derived
from the same packet's base restriction and actual ordinary character. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalBrauer

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

universe u
variable {P : Definition35Problem.{u}} {psi : Definition35Brauer P}
variable {V : CharacterWeight P.p P.K P.H}

theorem localMap_injective (packet : ActualWeightPacket P psi V) :
    Function.Injective packet.localMap := by
  intro n m h
  apply Subtype.ext
  apply packet.embeddingInjective
  exact (DFunLike.congr_fun packet.localMap_natural n).symm.trans
    ((congrArg Subtype.val h).trans (DFunLike.congr_fun packet.localMap_natural m))

def localBaseEquiv (packet : ActualWeightPacket P psi V) :
    Subgroup.normalizer (V.subgroup : Set P.H) ≃*
      localIntersection packet.localGroup packet.ambient.base :=
  ((MonoidHom.ofInjective (localMap_injective packet)).trans
    (MulEquiv.subgroupCongr packet.localMap_range)).trans
    (ModularRep.subgroupIntersectionEquiv packet.localGroup packet.ambient.base)

theorem localBaseEquiv_natural (packet : ActualWeightPacket P psi V) :
    (localInclusion packet.localGroup packet.ambient.base).comp
      (localBaseEquiv packet).toMonoidHom = packet.localMap := by
  ext n
  rfl

def localBrauerRoot (packet : ActualWeightPacket P psi V) :
    PrimeRegularRootEmbedding P.p P.k P.K (Subgroup.normalizer (V.subgroup : Set P.H)) :=
  (packet.intermediateBlocks packet.ambient.base le_rfl).localRoot.alongMulEquiv
    (localBaseEquiv packet).symm

def localBrauer (packet : ActualWeightPacket P psi V) : IBr (localBrauerRoot packet) :=
  IrreducibleBrauerCharacter.alongMulEquiv
    (packet.intermediateBlocks packet.ambient.base le_rfl).localRoot
    (localBaseEquiv packet).symm
    (packet.intermediateBlocks packet.ambient.base le_rfl).localBrauer

theorem localBrauer_restriction (packet : ActualWeightPacket P psi V) :
    PrimeRegularClassFunction.pullback packet.localMap packet.localCharacter.1 =
      (localBrauer packet).1 := by
  apply PrimeRegularClassFunction.ext
  intro n
  exact congrArg (fun f => f (PrimeRegularElement.map (localBaseEquiv packet).toMonoidHom n))
    (packet.intermediateBlocks packet.ambient.base le_rfl).localRestriction

theorem localBrauer_is_actual_reduction (packet : ActualWeightPacket P psi V) :
    IsBrauerReduction (localBrauerRoot packet)
      (inflateOrdinaryCharacter
        (V.subgroup.subgroupOf (Subgroup.normalizer (V.subgroup : Set P.H))) V.localCharacter)
      (localBrauer packet) := by
  intro n
  exact (packet.localRestriction n).symm.trans
    (congrArg (fun f => f n) (localBrauer_restriction packet))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalBrauer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
