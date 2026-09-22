import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathIntervals
import ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport

/-!
# All Q=1 intermediate data from the base and top

The selected quotient has order at most two. Construct the actual restricted
global characters and their complete catalogues at these two subgroups,
then derive the local block equalities on the same shared extension packet.
No family of intermediate character or block assertions is an input.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneGlobal

open ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock
open ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SpathQOneCharacterExtensions
open ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathIntervals
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneExtensions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlocks

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

variable (P : Definition35Problem.{u}) (M : EquivariantMatch P)
variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
variable (hcenter : Subgroup.center P.H = ⊥) (reference : Definition35Brauer P)
variable (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))

local instance outerFinite : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : P.H → P.H))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))


variable {weight : QuotientWeightBrauerSource P reference M.weight}
variable {localInflation : QuotientLocalInflationSource P reference M.weight weight}
variable (globalChoice : ChosenGlobalExtensionData (selectedOuterSpathAmbientCore P hcenter reference M.theta S haut))
variable (localData : QOneLocalTransportData localInflation (selectedOuterSpathAmbientCore P hcenter reference M.theta S haut))


variable {AmbientBlock : Type u} [Fintype AmbientBlock]
variable {ambientIdempotent : AmbientBlock → P.k[((selectedOuterSpathAmbientCore P hcenter reference M.theta S haut)).A]}
variable (ambientBlocks : BlockIdempotentDecomposition ambientIdempotent)
variable (ambientCharacters : BlockCentralCharacterCatalogue ambientBlocks)
variable (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)


def globalSourceOfSelectedAmbient : QOneIntermediateGlobalBlockSource (characterExtensionsOfGlobal globalChoice localData) := by
  classical
  let B := baseBlockCatalogueDataOfOperations hcenter (characterExtensionsOfGlobal globalChoice localData)
  let atBase : QOneIntermediateGlobalBlockData (characterExtensionsOfGlobal globalChoice localData) ((selectedOuterSpathAmbientCore P hcenter reference M.theta S haut)).base := {
    globalRoot := baseGlobalRoot (characterExtensionsOfGlobal globalChoice localData)
    globalBrauer := baseGlobalBrauer (characterExtensionsOfGlobal globalChoice localData)
    globalRestriction := baseGlobalRestriction (characterExtensionsOfGlobal globalChoice localData)
    Block := B.GlobalBlock
    fintypeBlock := B.fintypeGlobalBlock
    blockIdempotent := B.globalBlockIdempotent
    blocks := B.globalBlocks
    centralCharacters := B.globalCentralCharacters
    centralCharactersNavarro311 := ⟨fieldSource⟩ }
  let eA := (topToAmbientEquiv (selectedOuterSpathAmbientCore P hcenter reference M.theta S haut)).symm
  let atTop : QOneIntermediateGlobalBlockData (characterExtensionsOfGlobal globalChoice localData) (⊤ : Subgroup ((selectedOuterSpathAmbientCore P hcenter reference M.theta S haut)).A) := {
    globalRoot := topGlobalRoot (characterExtensionsOfGlobal globalChoice localData)
    globalBrauer := topGlobalBrauer (characterExtensionsOfGlobal globalChoice localData)
    globalRestriction := topGlobalRestriction (characterExtensionsOfGlobal globalChoice localData)
    Block := AmbientBlock
    fintypeBlock := inferInstance
    blockIdempotent := fun b ↦ MonoidAlgebra.domCongr P.k P.k eA (ambientIdempotent b)
    blocks := ambientBlocks.alongMulEquiv eA
    centralCharacters := ambientCharacters.alongMulEquiv eA
    centralCharactersNavarro311 := ⟨fieldSource⟩ }
  refine { globalAt := ?_ }
  intro J hJ
  by_cases hbase : J = ((selectedOuterSpathAmbientCore P hcenter reference M.theta S haut)).base
  · subst J
    exact atBase
  · have htop : J = ⊤ := (intermediate_eq_base_or_top P M S J hJ).resolve_left hbase
    subst J
    exact atTop


def intermediateBlocksOfSelectedAmbient :
    IntermediateBlockSource P reference M.theta M.weight (SelectedCentralQuotient P hcenter reference M.theta) weight localInflation (selectedOuterSpathAmbientCore P hcenter reference M.theta S haut) (characterExtensionsOfGlobal globalChoice localData) := by
  let globalSource := globalSourceOfSelectedAmbient P M S hcenter reference haut
    globalChoice localData ambientBlocks ambientCharacters fieldSource
  exact {
    equalityAt J hJ := intermediateBlockEqualityAtOfGlobalChoice
      globalChoice localData J (globalSource.globalAt J hJ) }

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneGlobal



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
