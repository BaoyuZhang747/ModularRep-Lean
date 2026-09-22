import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualIntermediateAssembly
import ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport

/-! Q=1 block data from specified self-transport of one global catalogue.
The existing local group and the same global extension are retained. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneBlocks

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

def intersectionEquivOfEquivSubtype
    {A : Type u} [Group A] (D J : Subgroup A)
    (eD : D ≃* A) (heD : eD.toMonoidHom = D.subtype) :
    localIntersection D J ≃* J where
  toFun x := x.1
  invFun x := ⟨x, by
    have hval : ((eD.symm (x : A) : D) : A) = (x : A) := by
      have h := congrArg (fun f : D →* A => f (eD.symm (x : A))) heD
      exact h.symm.trans (eD.apply_symm_apply (x : A))
    change (x : A) ∈ D
    exact hval ▸ (eD.symm (x : A)).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem intersectionEquivOfEquivSubtype_toMonoidHom
    {A : Type u} [Group A] (D J : Subgroup A)
    (eD : D ≃* A) (heD : eD.toMonoidHom = D.subtype) :
    (intersectionEquivOfEquivSubtype D J eD heD).toMonoidHom =
      (localIntersection D J).subtype := by
  ext x
  rfl

def qOneActualIntermediate
    (P : Definition35Problem.{u}) {A : Type u} [Group A] [Fintype A]
    (D : Subgroup A) (eD : D ≃* A) (heD : eD.toMonoidHom = D.subtype)
    (rA : PrimeRegularRootEmbedding P.p P.k P.K A) (phiA : IBr rA)
    (J : Subgroup A) (rJ : PrimeRegularRootEmbedding P.p P.k P.K J) (phiJ : IBr rJ)
    (restriction : PrimeRegularClassFunction.pullback J.subtype phiA.1 = phiJ.1)
    {Block : Type u} [Fintype Block] {blockIdempotent : Block → P.k[J]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime) :
    ActualIntermediateBlockData P D phiA.1
      (IrreducibleBrauerCharacter.alongMulEquiv rA eD.symm phiA).1 J := by
  let eJ := intersectionEquivOfEquivSubtype D J eD heD
  have heJ : eJ.toMonoidHom = (localIntersection D J).subtype :=
    intersectionEquivOfEquivSubtype_toMonoidHom D J eD heD
  let injJ := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rJ
  let rL := rJ.alongMulEquiv eJ.symm
  let phiL := IrreducibleBrauerCharacter.alongMulEquiv rJ eJ.symm phiJ
  let injL := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rL
  have hselected : irreducibleBrauerCharacterBlock rL injL (blocks.alongMulEquiv eJ.symm) phiL =
      irreducibleBrauerCharacterBlock rJ injJ blocks phiJ :=
    irreducibleBrauerCharacterBlock_alongMulEquiv rJ injJ eJ.symm injL blocks phiJ
  have hInd := blockInducesTo_self_of_equiv_subtype (k := P.k) (H := localIntersection D J)
    blocks catalogue eJ heJ (irreducibleBrauerCharacterBlock rJ injJ blocks phiJ)
  refine {
    globalRoot := rJ
    globalBrauer := phiJ
    globalRestriction := restriction
    localRoot := rL
    localBrauer := phiL
    localRestriction := ?_
    GlobalBlock := Block
    LocalBlock := Block
    globalBlockIdempotent := blockIdempotent
    localBlockIdempotent := fun b => MonoidAlgebra.domCongr P.k P.k eJ.symm (blockIdempotent b)
    globalBlocks := blocks
    localBlocks := blocks.alongMulEquiv eJ.symm
    globalBrauerInjective := injJ
    localBrauerInjective := injL
    globalCentralCharacters := catalogue
    localCentralCharacters := catalogue.alongMulEquiv eJ.symm
    globalCentralCharactersNavarro311 := ⟨fieldSource⟩
    localCentralCharactersNavarro311 := ⟨fieldSource⟩
    inductionEquality := ?_ }
  · apply PrimeRegularClassFunction.ext
    intro x
    change phiA.1 (PrimeRegularElement.map eD.toMonoidHom
      (PrimeRegularElement.map (localInclusion D J) x)) =
        phiJ.1 (PrimeRegularElement.map eJ.toMonoidHom x)
    rw [heD]
    exact congrArg (fun chi : PrimeRegularClassFunction P.K J P.p =>
      chi (PrimeRegularElement.map eJ.toMonoidHom x)) restriction
  · simpa only [hselected] using hInd

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
