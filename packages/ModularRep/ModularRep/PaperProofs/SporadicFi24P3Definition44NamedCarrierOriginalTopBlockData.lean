import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket
import ModularRep.IBrBlockEquivTransport
import ModularRep.CentralCharacterCovering

/-! Generic internal transport of an already derived block relation to
the top subgroup. The original-quotient constructor supplies that relation
from its specified quotient block images, not from an external packet. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopBlockData

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

def localTopEquiv {G : Type u} [Group G] (N : Subgroup G) :
    N ≃* localIntersection N (⊤ : Subgroup G) where
  toFun n := ⟨⟨n.1, Subgroup.mem_top _⟩, n.2⟩
  invFun n := ⟨n.1.1, n.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def topBlockData (P : Definition35Problem.{u})
    {A : Type u} [Group A] [Fintype A] (N : Subgroup A)
    (rG : PrimeRegularRootEmbedding P.p P.k P.K A)
    (rN : PrimeRegularRootEmbedding P.p P.k P.K N)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injN : IrreducibleBrauerCharacterInjectivity rN)
    {BG BN : Type u} [Fintype BG] [Fintype BN]
    {bG : BG → P.k[A]} {bN : BN → P.k[N]}
    (DG : BlockIdempotentDecomposition bG) (DN : BlockIdempotentDecomposition bN)
    (CG : BlockCentralCharacterCatalogue DG) (CN : BlockCentralCharacterCatalogue DN)
    (phiG : IBr rG) (phiN : IBr rN)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (hInd : BlockInducesTo N CN CG
      (irreducibleBrauerCharacterBlock rN injN DN phiN)
      (irreducibleBrauerCharacterBlock rG injG DG phiG)) :
    ActualIntermediateBlockData P N phiG.1 phiN.1 (⊤ : Subgroup A) := by
  let eG : A ≃* (⊤ : Subgroup A) := Subgroup.topEquiv.symm
  let eN := localTopEquiv N
  have hsquare : eG.toMonoidHom.comp N.subtype =
      (localIntersection N (⊤ : Subgroup A)).subtype.comp eN.toMonoidHom := by
    ext n
    rfl
  refine {
    globalRoot := rG.alongMulEquiv eG
    globalBrauer := IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG
    globalRestriction := ?_
    localRoot := rN.alongMulEquiv eN
    localBrauer := IrreducibleBrauerCharacter.alongMulEquiv rN eN phiN
    localRestriction := ?_
    GlobalBlock := BG
    LocalBlock := BN
    globalBlockIdempotent := fun b => MonoidAlgebra.domCongr P.k P.k eG (bG b)
    localBlockIdempotent := fun b => MonoidAlgebra.domCongr P.k P.k eN (bN b)
    globalBlocks := DG.alongMulEquiv eG
    localBlocks := DN.alongMulEquiv eN
    globalBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    localBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    globalCentralCharacters := CG.alongMulEquiv eG
    localCentralCharacters := CN.alongMulEquiv eN
    globalCentralCharactersNavarro311 := ⟨fieldSource⟩
    localCentralCharactersNavarro311 := ⟨fieldSource⟩
    inductionEquality := ?_ }
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · rw [irreducibleBrauerCharacterBlock_alongMulEquiv rN injN eN
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DN phiN,
      irreducibleBrauerCharacterBlock_alongMulEquiv rG injG eG
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DG phiG]
    exact blockInducesTo_alongMulEquiv N (localIntersection N (⊤ : Subgroup A))
      eG eN hsquare CN CG (CN.alongMulEquiv eN) (CG.alongMulEquiv eG) rfl rfl hInd

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopBlockData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
