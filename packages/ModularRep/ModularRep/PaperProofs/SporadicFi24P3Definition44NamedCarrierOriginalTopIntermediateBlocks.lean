import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIntermediateGroups
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions

/-! The entire original-group interval inherits the specified canonical
block induction through literal top and intersection equivalences. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopIntermediateBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (catalogueAlong)
open SporadicFi24P3Definition44NamedCarrierOriginalIntermediateGroups
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
local instance subgroupFintype (J : Subgroup G) : Fintype J := Fintype.ofFinite J
local instance intersectionFintype (D J : Subgroup G) :
    Fintype (localIntersection D J) := Fintype.ofFinite _

theorem original_top_intermediate_blocks (D : Subgroup G)
    (rG : PrimeRegularRootEmbedding p k K G) (rD : PrimeRegularRootEmbedding p k K D)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injD : IrreducibleBrauerCharacterInjectivity rD)
    (phiG : IBr rG) (phiD : IBr rD) {BG BD : Type u}
    (dataG : AmbientBlockCatalogueData (k := k) (G := G) (Block := BG))
    (dataD : AmbientBlockCatalogueData (k := k) (G := D) (Block := BD))
    (hInd : letI : Fintype BG := dataG.fintypeBlock
      letI : Fintype BD := dataD.fintypeBlock
      BlockInducesTo D dataD.catalogue dataG.catalogue
        (irreducibleBrauerCharacterBlock rD injD dataD.blocks phiD)
        (irreducibleBrauerCharacterBlock rG injG dataG.blocks phiG)) :
    AllIntermediateBlocks (k := k) D phiG.val phiD.val (⊤ : Subgroup G) := by
  let : Fintype BG := dataG.fintypeBlock
  let : Fintype BD := dataD.fintypeBlock
  intro J hJ
  have htop : J = ⊤ := top_unique hJ
  subst J
  let eG : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
  let eD := (topIntersectionEquiv D).symm
  refine ⟨rG.alongMulEquiv eG, IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG,
    rD.alongMulEquiv eD, IrreducibleBrauerCharacter.alongMulEquiv rD eD phiD,
    BG, BD, catalogueAlong dataG eG, catalogueAlong dataD eD, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · change BlockInducesTo (localIntersection D (⊤ : Subgroup G))
      (dataD.catalogue.alongMulEquiv eD) (dataG.catalogue.alongMulEquiv eG)
      (irreducibleBrauerCharacterBlock (rD.alongMulEquiv eD)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) (dataD.blocks.alongMulEquiv eD)
        (IrreducibleBrauerCharacter.alongMulEquiv rD eD phiD))
      (irreducibleBrauerCharacterBlock (rG.alongMulEquiv eG)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) (dataG.blocks.alongMulEquiv eG)
        (IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG))
    rw [irreducibleBrauerCharacterBlock_alongMulEquiv rD injD eD
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataD.blocks phiD,
        irreducibleBrauerCharacterBlock_alongMulEquiv rG injG eG
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataG.blocks phiG]
    exact blockInducesTo_alongMulEquiv D (localIntersection D (⊤ : Subgroup G))
      eG eD (topIntersection_square D) dataD.catalogue dataG.catalogue
      (dataD.catalogue.alongMulEquiv eD) (dataG.catalogue.alongMulEquiv eG) rfl rfl hInd

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopIntermediateBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
