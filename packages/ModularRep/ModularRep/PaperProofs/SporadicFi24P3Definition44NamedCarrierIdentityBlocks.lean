import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSourceHBlocks
import ModularRep.NavarroLocalReductionInflationBlockCompatibility

/-! The identity ambient interval has one member. Its actual block relation
is derived from the raw matched weight and the existing literal operations.
No independent catalogue, selected extension, or induction relation is input. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIdentityBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H
private theorem transportedInduction
    {p : ℕ} {k K G G' B L : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G] [Group G'] [Fintype G'] [Fintype B] [Fintype L]
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (square : eG.toMonoidHom.comp H.subtype = H'.subtype.comp eH.toMonoidHom)
    (rG : PrimeRegularRootEmbedding p k K G) (rH : PrimeRegularRootEmbedding p k K H)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injH : IrreducibleBrauerCharacterInjectivity rH)
    {bG : B → k[G]} {bH : L → k[H]}
    (blocksG : BlockIdempotentDecomposition bG) (blocksH : BlockIdempotentDecomposition bH)
    (catG : BlockCentralCharacterCatalogue blocksG) (catH : BlockCentralCharacterCatalogue blocksH)
    (chiG : IBr rG) (chiH : IBr rH)
    (induces : BlockInducesTo H catH catG
      (irreducibleBrauerCharacterBlock rH injH blocksH chiH)
      (irreducibleBrauerCharacterBlock rG injG blocksG chiG)) :
    BlockInducesTo H' (catH.alongMulEquiv eH) (catG.alongMulEquiv eG)
      (irreducibleBrauerCharacterBlock (rH.alongMulEquiv eH)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) (blocksH.alongMulEquiv eH)
        (IrreducibleBrauerCharacter.alongMulEquiv rH eH chiH))
      (irreducibleBrauerCharacterBlock (rG.alongMulEquiv eG)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) (blocksG.alongMulEquiv eG)
        (IrreducibleBrauerCharacter.alongMulEquiv rG eG chiG)) := by
  rw [irreducibleBrauerCharacterBlock_alongMulEquiv rH injH eH
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) blocksH chiH,
    irreducibleBrauerCharacterBlock_alongMulEquiv rG injG eG
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) blocksG chiG]
  exact blockInducesTo_alongMulEquiv H H' eG eH square catH catG
    (catH.alongMulEquiv eH) (catG.alongMulEquiv eG) rfl rfl induces

def normalizerTopEquiv (P : Definition35Problem.{u}) (V : CharacterWeight P.p P.K P.H) :
    Subgroup.normalizer (V.subgroup : Set P.H) ≃*
      localIntersection (Subgroup.normalizer (V.subgroup : Set P.H)) (⊤ : Subgroup P.H) where
  toFun n := ⟨⟨n.1, Subgroup.mem_top _⟩, n.2⟩
  invFun n := ⟨n.1.1, n.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def topBlockData (P : Definition35Problem.{u})
    (phi : IBr P.iota) (V : CharacterWeight P.p P.K P.H)
    (rootN : PrimeRegularRootEmbedding P.p P.k P.K (Subgroup.normalizer (V.subgroup : Set P.H)))
    (phiN : IBr rootN)
    (hReduction : NormalizerInflatedReduction V.subgroup V.localCharacter rootN phiN)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source P.blockSource.operations)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (hrawBlock :
      letI := P.blockSource.operations.ambientBlockData.fintypeBlock
      P.blockSource.operations.rawWeightBlock V =
        irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
          P.blockSource.operations.ambientBlockData.blocks phi) :
    ActualIntermediateBlockData P (Subgroup.normalizer (V.subgroup : Set P.H))
      phi.1 phiN.1 (⊤ : Subgroup P.H) := by
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData V.subgroup
  let := O.ambientBlockData.fintypeBlock
  let := localData.fintypeBlock
  let L := Subgroup.normalizer (V.subgroup : Set P.H)
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rootN
  have hlocal : irreducibleBrauerCharacterBlock rootN injN localData.blocks phiN =
      O.inflateToNormalizer V.subgroup (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero) :=
    compatibility.normalizerBrauerBlock_eq_inflateToNormalizer V rootN phiN hReduction
  have hbase : BlockInducesTo L localData.catalogue O.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock rootN injN localData.blocks phiN)
      (irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective O.ambientBlockData.blocks phi) := by
    rw [hlocal, ← hrawBlock]
    exact inducedBlock_spec L localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer V.subgroup (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
      (O.blockInductionDefined V)
  let eG : P.H ≃* (⊤ : Subgroup P.H) := Subgroup.topEquiv.symm
  let eL := normalizerTopEquiv P V
  have hsquare : eG.toMonoidHom.comp L.subtype =
      (localIntersection L (⊤ : Subgroup P.H)).subtype.comp eL.toMonoidHom := by
    ext n
    rfl
  refine {
    globalRoot := P.iota.alongMulEquiv eG
    globalBrauer := IrreducibleBrauerCharacter.alongMulEquiv P.iota eG phi
    globalRestriction := ?_
    localRoot := rootN.alongMulEquiv eL
    localBrauer := IrreducibleBrauerCharacter.alongMulEquiv rootN eL phiN
    localRestriction := ?_
    GlobalBlock := P.Block
    LocalBlock := InflatedNormalizerBlock (k := P.k) V.subgroup
    globalBlockIdempotent := fun b => MonoidAlgebra.domCongr P.k P.k eG (O.ambientBlockData.blockIdempotent b)
    localBlockIdempotent := fun b => MonoidAlgebra.domCongr P.k P.k eL (inflatedNormalizerBlockIdempotent V.subgroup b)
    globalBlocks := O.ambientBlockData.blocks.alongMulEquiv eG
    localBlocks := localData.blocks.alongMulEquiv eL
    globalBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    localBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    globalCentralCharacters := O.ambientBlockData.catalogue.alongMulEquiv eG
    localCentralCharacters := localData.catalogue.alongMulEquiv eL
    globalCentralCharactersNavarro311 := ⟨fieldSource⟩
    localCentralCharactersNavarro311 := ⟨fieldSource⟩
    inductionEquality := transportedInduction L _ eG eL hsquare P.iota rootN
      P.irreducibleBrauerInjective injN O.ambientBlockData.blocks localData.blocks
      O.ambientBlockData.catalogue localData.catalogue phi phiN hbase }
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl

def allIntermediateBlockData (P : Definition35Problem.{u})
    (phi : IBr P.iota) (V : CharacterWeight P.p P.K P.H)
    (rootN : PrimeRegularRootEmbedding P.p P.k P.K (Subgroup.normalizer (V.subgroup : Set P.H)))
    (phiN : IBr rootN)
    (hReduction : NormalizerInflatedReduction V.subgroup V.localCharacter rootN phiN)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source P.blockSource.operations)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (hrawBlock :
      letI := P.blockSource.operations.ambientBlockData.fintypeBlock
      P.blockSource.operations.rawWeightBlock V =
        irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
          P.blockSource.operations.ambientBlockData.blocks phi)
    (J : Subgroup P.H) (hJ : (⊤ : Subgroup P.H) ≤ J) :
    ActualIntermediateBlockData P (Subgroup.normalizer (V.subgroup : Set P.H)) phi.1 phiN.1 J := by
  have hJtop : J = ⊤ := top_unique hJ
  subst J
  exact topBlockData P phi V rootN phiN hReduction compatibility fieldSource hrawBlock

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIdentityBlocks




/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
