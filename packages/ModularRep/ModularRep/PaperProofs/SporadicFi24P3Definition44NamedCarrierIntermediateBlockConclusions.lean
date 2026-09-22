import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues

/-! Actual intermediate restrictions and block induction, with independent
global and local block indices and no Q=1 hypothesis. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks

universe u
variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A]
local instance subgroupFintype (J : Subgroup A) : Fintype J := Fintype.ofFinite J
local instance intersectionFintype (D J : Subgroup A) :
    Fintype (localIntersection D J) := Fintype.ofFinite _
variable (D : Subgroup A)
variable (globalCharacter : PrimeRegularClassFunction K A p)
variable (localCharacter : PrimeRegularClassFunction K D p)

def IntermediateBlockOutput (J : Subgroup A)
    (rJ : PrimeRegularRootEmbedding p k K J) (phiJ : IBr rJ)
    (rH : PrimeRegularRootEmbedding p k K (localIntersection D J)) (phiH : IBr rH)
    {BJ BH : Type u}
    (dataJ : AmbientBlockCatalogueData (k := k) (G := J) (Block := BJ))
    (dataH : AmbientBlockCatalogueData (k := k) (G := localIntersection D J) (Block := BH)) : Prop :=
  letI : Fintype BJ := dataJ.fintypeBlock
  letI : Fintype BH := dataH.fintypeBlock
  PrimeRegularClassFunction.pullback J.subtype globalCharacter = phiJ.val ∧
  PrimeRegularClassFunction.pullback (localInclusion D J) localCharacter = phiH.val ∧
  BlockInducesTo (localIntersection D J) dataH.catalogue dataJ.catalogue
    (irreducibleBrauerCharacterBlock rH
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding rH) dataH.blocks phiH)
    (irreducibleBrauerCharacterBlock rJ
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding rJ) dataJ.blocks phiJ)

def ExistsIntermediateBlocks (J : Subgroup A) : Prop :=
  ∃ (rJ : PrimeRegularRootEmbedding p k K J) (phiJ : IBr rJ)
    (rH : PrimeRegularRootEmbedding p k K (localIntersection D J)) (phiH : IBr rH)
    (BJ BH : Type u)
    (dataJ : AmbientBlockCatalogueData (k := k) (G := J) (Block := BJ))
    (dataH : AmbientBlockCatalogueData (k := k) (G := localIntersection D J) (Block := BH)),
    IntermediateBlockOutput D globalCharacter localCharacter J rJ phiJ rH phiH dataJ dataH

def AllIntermediateBlocks (B : Subgroup A) : Prop :=
  ∀ J : Subgroup A, B ≤ J →
    ExistsIntermediateBlocks (k := k) D globalCharacter localCharacter J

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
