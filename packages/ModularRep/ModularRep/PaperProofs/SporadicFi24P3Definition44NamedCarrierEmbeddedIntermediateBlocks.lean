import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopIntermediateBlocks

/-! Base and top block deductions cover the actual intermediate interval.
Both restrictions refer to the same chosen global and fixed local extensions. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedIntermediateBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (catalogueAlong)
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
open SporadicFi24P3Definition44NamedCarrierOriginalTopIntermediateBlocks

universe u
variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A]
local instance subgroupFintype (B : Subgroup A) : Fintype B := Fintype.ofFinite _
local instance comapFintype (B D : Subgroup A) : Fintype (B.comap D.subtype) := Fintype.ofFinite _

theorem all_intermediate_blocks_of_base_top
    (B D : Subgroup A)
    (rA : PrimeRegularRootEmbedding p k K A)
    (rB : PrimeRegularRootEmbedding p k K B)
    (rD : PrimeRegularRootEmbedding p k K D)
    (rM : PrimeRegularRootEmbedding p k K (B.comap D.subtype))
    (phiB : IBr rB) (phiM : IBr rM)
    (selectedGlobal : BrauerCharacterExtensionWitness rA rB phiB)
    (fixedLocal : BrauerCharacterExtensionWitness rD rM phiM)
    {BA BB BD BM : Type u}
    (dataA : AmbientBlockCatalogueData (k := k) (G := A) (Block := BA))
    (dataB : AmbientBlockCatalogueData (k := k) (G := B) (Block := BB))
    (dataD : AmbientBlockCatalogueData (k := k) (G := D) (Block := BD))
    (dataM : AmbientBlockCatalogueData (k := k) (G := B.comap D.subtype) (Block := BM))
    (cases : ∀ J : Subgroup A, B ≤ J → J = B ∨ J = ⊤)
    (hbase : letI : Fintype BB := dataB.fintypeBlock
      letI : Fintype BM := dataM.fintypeBlock
      BlockInducesTo (localIntersection D B)
        (dataM.catalogue.alongMulEquiv (subgroupIntersectionEquiv D B)) dataB.catalogue
        (irreducibleBrauerCharacterBlock rM
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataM.blocks phiM)
        (irreducibleBrauerCharacterBlock rB
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataB.blocks phiB))
    (htop : letI : Fintype BA := dataA.fintypeBlock
      letI : Fintype BD := dataD.fintypeBlock
      BlockInducesTo D dataD.catalogue dataA.catalogue
        (irreducibleBrauerCharacterBlock rD
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataD.blocks fixedLocal.val)
        (irreducibleBrauerCharacterBlock rA
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataA.blocks selectedGlobal.val)) :
    AllIntermediateBlocks (k := k) D selectedGlobal.val.val fixedLocal.val.val B := by
  let : Fintype BA := dataA.fintypeBlock
  let : Fintype BB := dataB.fintypeBlock
  let : Fintype BD := dataD.fintypeBlock
  let : Fintype BM := dataM.fintypeBlock
  intro J hJ
  by_cases hJbase : J = B
  · subst J
    let d := subgroupIntersectionEquiv D B
    refine ⟨rB, phiB, rM.alongMulEquiv d,
      IrreducibleBrauerCharacter.alongMulEquiv rM d phiM,
      BB, BM, dataB, catalogueAlong dataM d, ?_⟩
    refine ⟨selectedGlobal.property, ?_, ?_⟩
    · apply PrimeRegularClassFunction.ext
      intro x
      exact congrArg
        (fun chi : PrimeRegularClassFunction K (B.comap D.subtype) p =>
          chi (PrimeRegularElement.map d.symm.toMonoidHom x)) fixedLocal.property
    · change BlockInducesTo (localIntersection D B)
        (dataM.catalogue.alongMulEquiv d) dataB.catalogue
        (irreducibleBrauerCharacterBlock (rM.alongMulEquiv d)
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
          (dataM.blocks.alongMulEquiv d) (IrreducibleBrauerCharacter.alongMulEquiv rM d phiM))
        (irreducibleBrauerCharacterBlock rB
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataB.blocks phiB)
      rw [irreducibleBrauerCharacterBlock_alongMulEquiv rM
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) d
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataM.blocks phiM]
      exact hbase
  · have hJtop := (cases J hJ).resolve_left hJbase
    subst J
    exact (original_top_intermediate_blocks D rA rD
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      selectedGlobal.val fixedLocal.val dataA dataD htop) ⊤ le_rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedIntermediateBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
