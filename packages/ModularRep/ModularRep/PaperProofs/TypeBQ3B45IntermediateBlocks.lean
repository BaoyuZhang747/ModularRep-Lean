import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
import ModularRep.BrauerCharacterHomPullback

/-!
# Current intermediate block data for one Q=1 extension

These constructors specialize the checked Q=1 self-transport deduction to
the current `IntermediateBlockData`. They retain one common global/local
character and derive both the selected local block and self-induction from
one global catalogue. Over an index-at-most-two base, the same extension has
irreducible restrictions at every intermediate subgroup, since those are
exactly the base and the whole group. No covering choice, local extension,
local catalogue, or block-pasting theorem is supplied.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B45IntermediateBlocks

open ModularRep FDRepSimpleClassKZero
open Representation.Extension
open TypeBQ3PrincipalPairBlockChoice

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K A : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K] [Group A] [Finite A]

/-- The current block packet is a direct output of the checked Q=1
common-character restriction and specified self-induction calculation. -/
def qOneIntermediate
    (D : Subgroup A) (hD : D = ⊤)
    (globalCharacter : PrimeRegularClassFunction K A 2)
    (localCharacter : PrimeRegularClassFunction K D 2)
    (common : PrimeRegularClassFunction.pullback D.subtype globalCharacter = localCharacter)
    (J : Subgroup A) (rJ : PrimeRegularRootEmbedding 2 k K J) (phiJ : IBr rJ)
    (restriction : PrimeRegularClassFunction.pullback J.subtype globalCharacter = phiJ.val)
    {Block : Type} [Fintype Block] {blockIdempotent : Block → k[J]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two) :
    IntermediateBlockData 2 k K D globalCharacter localCharacter J := by
  let eJ := SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks.intersectionEquiv D J hD
  let rL := rJ.alongMulEquiv eJ.symm
  let phiL := IrreducibleBrauerCharacter.alongMulEquiv rJ eJ.symm phiJ
  have output :=
    SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks.qOne_intermediate_block_output
      D hD globalCharacter localCharacter J rJ phiJ blocks catalogue common restriction
  obtain ⟨globalRestriction, localRestriction, _selectedBlock, induction⟩ := output
  exact {
    globalRoot := rJ
    globalBrauer := phiJ
    globalRestriction := globalRestriction
    localRoot := rL
    localBrauer := phiL
    localRestriction := localRestriction
    GlobalBlock := Block
    LocalBlock := Block
    globalBlockIdempotent := blockIdempotent
    localBlockIdempotent := fun b => MonoidAlgebra.domCongr k k eJ.symm (blockIdempotent b)
    globalBlocks := blocks
    localBlocks := blocks.alongMulEquiv eJ.symm
    globalBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rJ
    localBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rL
    globalCentralCharacters := catalogue
    localCentralCharacters := catalogue.alongMulEquiv eJ.symm
    globalCentralCharactersNavarro311 := ⟨fieldSource⟩
    localCentralCharactersNavarro311 := ⟨fieldSource⟩
    inductionEquality := induction }

/-- Every intermediate restriction is irreducible because the quotient has
order at most two. Each local block catalogue is transported from the SAME
corresponding base or ambient catalogue, with no independent local choices. -/
def allIntermediate
    (B D : Subgroup A) [B.Normal] (hD : D = ⊤)
    (bound : Nat.card (A ⧸ B) ≤ 2)
    (rB : PrimeRegularRootEmbedding 2 k K B) (phiB : IBr rB)
    (rA : PrimeRegularRootEmbedding 2 k K A)
    (extension : BrauerCharacterExtensionWitness rA rB phiB)
    (rD : PrimeRegularRootEmbedding 2 k K D) (phiD : IBr rD)
    (common : PrimeRegularClassFunction.pullback D.subtype extension.val.val = phiD.val)
    {BaseBlock AmbientBlock : Type} [Fintype BaseBlock] [Fintype AmbientBlock]
    {baseIdempotent : BaseBlock → k[B]} {ambientIdempotent : AmbientBlock → k[A]}
    (baseBlocks : BlockIdempotentDecomposition baseIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientIdempotent)
    (baseCatalogue : BlockCentralCharacterCatalogue baseBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two) :
    ∀ J : Subgroup A, B ≤ J →
      IntermediateBlockData 2 k K D extension.val.val phiD.val J := by
  classical
  let atBase := qOneIntermediate D hD extension.val.val phiD.val common
    B rB phiB extension.property baseBlocks baseCatalogue fieldSource
  letI : Fintype (⊤ : Subgroup A) := groupFintype (⊤ : Subgroup A)
  let eA : A ≃* (⊤ : Subgroup A) := Subgroup.topEquiv.symm
  let rTop := rA.alongMulEquiv eA
  let phiTop := IrreducibleBrauerCharacter.alongMulEquiv rA eA extension.val
  have topRestriction :
      PrimeRegularClassFunction.pullback (⊤ : Subgroup A).subtype extension.val.val =
        phiTop.val := by
    apply PrimeRegularClassFunction.ext
    intro x
    rfl
  let atTop := qOneIntermediate D hD extension.val.val phiD.val common
    ⊤ rTop phiTop topRestriction (ambientBlocks.alongMulEquiv eA)
    (ambientCatalogue.alongMulEquiv eA) fieldSource
  intro J hJ
  by_cases hbase : J = B
  · subst J
    exact atBase
  · have htop :=
      (subgroup_eq_base_or_top_of_quotient_card_le_two B bound J hJ).resolve_left hbase
    subst J
    exact atTop

end ModularRep.PaperProofs.TypeBQ3B45IntermediateBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
