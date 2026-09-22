import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopBlockData

/-! Internal transport of the own-quotient base induction relation into an
actual ambient. The two extension witnesses are independent; no relation
between their ambient blocks or all-intermediate condition is assumed. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalBaseBlockData

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket
open Representation.Extension

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

theorem baseSquare_of_localEmbedding
    {G A : Type u} [Group G] [Group A]
    (N : Subgroup G) (base D : Subgroup A)
    (eG : G ≃* base) (eM : N ≃* base.comap D.subtype)
    (hM : ∀ n : N, (eM n).1.1 = (eG n.1 : A)) :
    eG.toMonoidHom.comp N.subtype =
      (localIntersection D base).subtype.comp
        (eM.trans (subgroupIntersectionEquiv D base)).toMonoidHom := by
  apply MonoidHom.ext
  intro n
  apply Subtype.ext
  exact (hM n).symm

def baseBlockDataOfExtensions
    (P : Definition35Problem.{u})
    {G A : Type u} [Group G] [Fintype G] [Group A] [Fintype A]
    (N : Subgroup G) (base D : Subgroup A)
    (eG : G ≃* base) (eM : N ≃* base.comap D.subtype)
    (square : eG.toMonoidHom.comp N.subtype =
      (localIntersection D base).subtype.comp
        (eM.trans (subgroupIntersectionEquiv D base)).toMonoidHom)
    (rG : PrimeRegularRootEmbedding P.p P.k P.K G)
    (rN : PrimeRegularRootEmbedding P.p P.k P.K N)
    (rA : PrimeRegularRootEmbedding P.p P.k P.K A)
    (rD : PrimeRegularRootEmbedding P.p P.k P.K D)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injN : IrreducibleBrauerCharacterInjectivity rN)
    {BG BN : Type u} [Fintype BG] [Fintype BN]
    {bG : BG → P.k[G]} {bN : BN → P.k[N]}
    (DG : BlockIdempotentDecomposition bG) (DN : BlockIdempotentDecomposition bN)
    (CG : BlockCentralCharacterCatalogue DG) (CN : BlockCentralCharacterCatalogue DN)
    (phiG : IBr rG) (phiN : IBr rN)
    (globalExt : BrauerCharacterExtensionWitness rA (rG.alongMulEquiv eG)
      (IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG))
    (localExt : BrauerCharacterExtensionWitness rD (rN.alongMulEquiv eM)
      (IrreducibleBrauerCharacter.alongMulEquiv rN eM phiN))
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (hInd : BlockInducesTo N CN CG
      (irreducibleBrauerCharacterBlock rN injN DN phiN)
      (irreducibleBrauerCharacterBlock rG injG DG phiG)) :
    ActualIntermediateBlockData P D globalExt.1.1 localExt.1.1 base := by
  let d := subgroupIntersectionEquiv D base
  let eN : N ≃* localIntersection D base := eM.trans d
  refine {
    globalRoot := rG.alongMulEquiv eG
    globalBrauer := IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG
    globalRestriction := globalExt.2
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
    exact congrArg
      (fun chi : PrimeRegularClassFunction P.K (base.comap D.subtype) P.p =>
        chi (PrimeRegularElement.map d.symm.toMonoidHom x)) localExt.2
  · rw [irreducibleBrauerCharacterBlock_alongMulEquiv rN injN eN
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DN phiN,
      irreducibleBrauerCharacterBlock_alongMulEquiv rG injG eG
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DG phiG]
    exact blockInducesTo_alongMulEquiv N (localIntersection D base) eG eN square
      CN CG (CN.alongMulEquiv eN) (CG.alongMulEquiv eG) rfl rfl hInd

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalBaseBlockData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
