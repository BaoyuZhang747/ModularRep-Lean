import ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport

/-! Literal intermediate restrictions and block induction for one common
Q=1 pair, using a single global catalogue and its transported local data. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks

open ModularRep ModularRep.FDRepSimpleClassKZero

universe u

section Groups
variable {A : Type u} [Group A]

abbrev localIntersection (D J : Subgroup A) : Subgroup J :=
  D.comap J.subtype

def localInclusion (D J : Subgroup A) : localIntersection D J →* D where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def intersectionEquiv (D J : Subgroup A) (hD : D = ⊤) :
    localIntersection D J ≃* J where
  toFun x := x.val
  invFun x := ⟨x, by
    change (x : A) ∈ D
    rw [hD]
    exact Subgroup.mem_top _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem intersectionEquiv_toMonoidHom (D J : Subgroup A) (hD : D = ⊤) :
    (intersectionEquiv D J hD).toMonoidHom = (localIntersection D J).subtype := by
  ext x
  rfl

end Groups

variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Finite A]
local instance subgroupFintype (H : Subgroup A) : Fintype H := Fintype.ofFinite H
local instance intersectionFintype (D J : Subgroup A) :
    Fintype (localIntersection D J) := Fintype.ofFinite _

variable (D : Subgroup A) (hD : D = ⊤)
variable (globalCharacter : PrimeRegularClassFunction K A p)
variable (localCharacter : PrimeRegularClassFunction K D p)
variable (J : Subgroup A)
variable (rJ : PrimeRegularRootEmbedding p k K J) (phiJ : IBr rJ)
variable {Block : Type u} [Fintype Block]
variable {blockIdempotent : Block → k[J]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (catalogue : BlockCentralCharacterCatalogue blocks)

def QOneIntermediateBlockOutput : Prop :=
  let eJ := intersectionEquiv D J hD
  let rH := rJ.alongMulEquiv eJ.symm
  let phiH := IrreducibleBrauerCharacter.alongMulEquiv rJ eJ.symm phiJ
  let injJ := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rJ
  let injH := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rH
  let bJ := irreducibleBrauerCharacterBlock rJ injJ blocks phiJ
  let bH := irreducibleBrauerCharacterBlock rH injH (blocks.alongMulEquiv eJ.symm) phiH
  PrimeRegularClassFunction.pullback J.subtype globalCharacter = phiJ.val ∧
  PrimeRegularClassFunction.pullback (localInclusion D J) localCharacter = phiH.val ∧
  bH = bJ ∧
  BlockInducesTo (localIntersection D J) (catalogue.alongMulEquiv eJ.symm) catalogue bH bJ

theorem qOne_intermediate_block_output
    (hcommon : PrimeRegularClassFunction.pullback D.subtype globalCharacter = localCharacter)
    (restriction : PrimeRegularClassFunction.pullback J.subtype globalCharacter = phiJ.val) :
    QOneIntermediateBlockOutput D hD globalCharacter localCharacter J rJ phiJ blocks catalogue := by
  let eJ := intersectionEquiv D J hD
  let injJ := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rJ
  let rH := rJ.alongMulEquiv eJ.symm
  let phiH := IrreducibleBrauerCharacter.alongMulEquiv rJ eJ.symm phiJ
  let injH := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rH
  have hselected :
      irreducibleBrauerCharacterBlock rH injH (blocks.alongMulEquiv eJ.symm) phiH =
        irreducibleBrauerCharacterBlock rJ injJ blocks phiJ :=
    irreducibleBrauerCharacterBlock_alongMulEquiv rJ injJ eJ.symm injH blocks phiJ
  have hInd := blockInducesTo_self_of_equiv_subtype
    (k := k) (H := localIntersection D J) blocks catalogue eJ
    (intersectionEquiv_toMonoidHom D J hD)
    (irreducibleBrauerCharacterBlock rJ injJ blocks phiJ)
  dsimp only [QOneIntermediateBlockOutput]
  refine ⟨restriction, ?_, hselected, ?_⟩
  · apply PrimeRegularClassFunction.ext
    intro x
    change localCharacter (PrimeRegularElement.map (localInclusion D J) x) =
      phiJ.val (PrimeRegularElement.map eJ.toMonoidHom x)
    have hc := congrArg (fun chi : PrimeRegularClassFunction K D p =>
      chi (PrimeRegularElement.map (localInclusion D J) x)) hcommon
    have hr := congrArg (fun chi : PrimeRegularClassFunction K J p =>
      chi (PrimeRegularElement.map eJ.toMonoidHom x)) restriction
    exact hc.symm.trans hr
  · change BlockInducesTo (localIntersection D J) (catalogue.alongMulEquiv eJ.symm) catalogue
      (irreducibleBrauerCharacterBlock rH injH (blocks.alongMulEquiv eJ.symm) phiH)
      (irreducibleBrauerCharacterBlock rJ injJ blocks phiJ)
    rw [hselected]
    exact hInd

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
