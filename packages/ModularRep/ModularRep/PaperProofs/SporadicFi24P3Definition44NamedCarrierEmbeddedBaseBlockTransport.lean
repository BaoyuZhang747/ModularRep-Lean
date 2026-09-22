import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues
import ModularRep.IBrBlockEquivTransport
import ModularRep.CentralCharacterCovering

/-! Transport the specified base induction through the actual embedding
square. The nested local catalogue identity follows from its idempotents. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedBaseBlockTransport

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (catalogueAlong)

universe u

theorem embedded_base_square
    {G A : Type u} [Group G] [Group A]
    (N : Subgroup G) (B D : Subgroup A)
    (eG : G ≃* B) (eM : N ≃* B.comap D.subtype)
    (hM : ∀ n : N, (eM n).val.val = (eG n.val : A)) :
    eG.toMonoidHom.comp N.subtype =
      (localIntersection D B).subtype.comp
        (eM.trans (subgroupIntersectionEquiv D B)).toMonoidHom := by
  ext n
  exact (hM n).symm

variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Fintype A]

local instance subgroupFintype
    {H : Type u} [Group H] [Finite H] (S : Subgroup H) :
    Fintype S := Fintype.ofFinite S

theorem embedded_base_block_induction
    (N : Subgroup G) (B D : Subgroup A)
    (eG : G ≃* B) (eM : N ≃* B.comap D.subtype)
    (square : eG.toMonoidHom.comp N.subtype =
      (localIntersection D B).subtype.comp
        (eM.trans (subgroupIntersectionEquiv D B)).toMonoidHom)
    (rG : PrimeRegularRootEmbedding p k K G)
    (rN : PrimeRegularRootEmbedding p k K N)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injN : IrreducibleBrauerCharacterInjectivity rN)
    (phiG : IBr rG) (phiN : IBr rN)
    {BG BN : Type u}
    (dataG : AmbientBlockCatalogueData (k := k) (G := G) (Block := BG))
    (dataN : AmbientBlockCatalogueData (k := k) (G := N) (Block := BN))
    (hInd : letI : Fintype BG := dataG.fintypeBlock
      letI : Fintype BN := dataN.fintypeBlock
      BlockInducesTo N dataN.catalogue dataG.catalogue
        (irreducibleBrauerCharacterBlock rN injN dataN.blocks phiN)
        (irreducibleBrauerCharacterBlock rG injG dataG.blocks phiG)) :
    letI : Fintype BG := dataG.fintypeBlock
    letI : Fintype BN := dataN.fintypeBlock
    let dataB := catalogueAlong dataG eG
    let dataM := catalogueAlong dataN eM
    BlockInducesTo (localIntersection D B)
      (dataM.catalogue.alongMulEquiv (subgroupIntersectionEquiv D B)) dataB.catalogue
      (irreducibleBrauerCharacterBlock (rN.alongMulEquiv eM)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataM.blocks
        (IrreducibleBrauerCharacter.alongMulEquiv rN eM phiN))
      (irreducibleBrauerCharacterBlock (rG.alongMulEquiv eG)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataB.blocks
        (IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG)) := by
  let : Fintype BG := dataG.fintypeBlock
  let : Fintype BN := dataN.fintypeBlock
  let d := subgroupIntersectionEquiv D B
  let eH : N ≃* localIntersection D B := eM.trans d
  have hlocal (b : BN) :
      centralCharacterAlongMulEquiv eH (dataN.catalogue.centralCharacter b) =
        ((dataN.catalogue.alongMulEquiv eM).alongMulEquiv d).centralCharacter b := by
    apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
      eH dataN.catalogue ((dataN.catalogue.alongMulEquiv eM).alongMulEquiv d)
    apply Subtype.ext
    change MonoidAlgebra.domCongr k k eH (dataN.blockIdempotent b) =
      MonoidAlgebra.domCongr k k d (MonoidAlgebra.domCongr k k eM (dataN.blockIdempotent b))
    ext x
    simp only [MonoidAlgebra.coeff_domCongr]
    rfl
  change BlockInducesTo (localIntersection D B)
    ((dataN.catalogue.alongMulEquiv eM).alongMulEquiv d)
    (dataG.catalogue.alongMulEquiv eG)
    (irreducibleBrauerCharacterBlock (rN.alongMulEquiv eM)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      (dataN.blocks.alongMulEquiv eM) (IrreducibleBrauerCharacter.alongMulEquiv rN eM phiN))
    (irreducibleBrauerCharacterBlock (rG.alongMulEquiv eG)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      (dataG.blocks.alongMulEquiv eG) (IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG))
  rw [irreducibleBrauerCharacterBlock_alongMulEquiv rN injN eM
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataN.blocks phiN,
      irreducibleBrauerCharacterBlock_alongMulEquiv rG injG eG
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataG.blocks phiG]
  exact blockInducesTo_alongMulEquiv N (localIntersection D B) eG eH square
    dataN.catalogue dataG.catalogue
    ((dataN.catalogue.alongMulEquiv eM).alongMulEquiv d)
    (dataG.catalogue.alongMulEquiv eG) (hlocal _) rfl hInd

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedBaseBlockTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
