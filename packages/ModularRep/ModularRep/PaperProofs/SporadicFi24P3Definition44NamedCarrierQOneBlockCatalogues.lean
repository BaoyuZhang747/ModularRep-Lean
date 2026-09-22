import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
import ModularRep.CharacterWeightBlockAssignment

/-! Unselected catalogues and concrete existential intermediate block
conclusions; all local data are computed from the chosen global catalogue. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks

universe u
variable {k G A Block : Type u} [Field k] [IsAlgClosed k]
variable [Group G] [Fintype G] [Group A] [Fintype A]

def catalogueAlong (data : AmbientBlockCatalogueData (k := k) (G := G) (Block := Block))
    (e : G ≃* A) : AmbientBlockCatalogueData (k := k) (G := A) (Block := Block) := by
  letI : Fintype Block := data.fintypeBlock
  exact {
    fintypeBlock := data.fintypeBlock
    blockIdempotent := fun b => MonoidAlgebra.domCongr k k e (data.blockIdempotent b)
    blocks := data.blocks.alongMulEquiv e
    catalogue := data.catalogue.alongMulEquiv e }

def UnselectedCatalogue : Prop :=
  ∃ BlockA : Type u, Nonempty (AmbientBlockCatalogueData (k := k) (G := A) (Block := BlockA))

variable {p : ℕ} {K : Type u} [Field K] [CharP k p] [CharZero K]
local instance subgroupFintype (H : Subgroup A) : Fintype H := Fintype.ofFinite H
variable (D : Subgroup A) (hD : D = ⊤)
variable (globalCharacter : PrimeRegularClassFunction K A p)
variable (localCharacter : PrimeRegularClassFunction K D p)

def ExistsIntermediateBlocks (J : Subgroup A) : Prop :=
  ∃ (rJ : PrimeRegularRootEmbedding p k K J) (phiJ : IBr rJ) (BlockJ : Type u)
    (data : AmbientBlockCatalogueData (k := k) (G := J) (Block := BlockJ)),
    letI : Fintype BlockJ := data.fintypeBlock
    QOneIntermediateBlockOutput D hD globalCharacter localCharacter J rJ phiJ data.blocks data.catalogue

def AllIntermediateBlocks (B : Subgroup A) : Prop :=
  ∀ J : Subgroup A, B ≤ J → ExistsIntermediateBlocks (k := k) D hD globalCharacter localCharacter J

theorem exists_intermediate_blocks_of_catalogue
    (J : Subgroup A) (rJ : PrimeRegularRootEmbedding p k K J) (phiJ : IBr rJ)
    (data : AmbientBlockCatalogueData (k := k) (G := J) (Block := Block))
    (hcommon : PrimeRegularClassFunction.pullback D.subtype globalCharacter = localCharacter)
    (restriction : PrimeRegularClassFunction.pullback J.subtype globalCharacter = phiJ.val) :
    ExistsIntermediateBlocks (k := k) D hD globalCharacter localCharacter J := by
  let : Fintype Block := data.fintypeBlock
  exact ⟨rJ, phiJ, Block, data,
    qOne_intermediate_block_output D hD globalCharacter localCharacter J rJ phiJ
      data.blocks data.catalogue hcommon restriction⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
