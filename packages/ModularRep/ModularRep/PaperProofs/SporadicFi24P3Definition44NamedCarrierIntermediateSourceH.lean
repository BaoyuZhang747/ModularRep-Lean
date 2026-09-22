import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
import ModularRep.CentralCharacterCovering
import ModularRep.IBrBlockEquivTransport

/-! The all-intermediate-global law gives the literal local-H law.
The roots, characters and catalogues are transported from the same BH row. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateSourceH

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (catalogueAlong)
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions

universe u
local instance subgroupFintype {G : Type u} [Group G] [Finite G] (S : Subgroup G) :
    Fintype S := Fintype.ofFinite S

theorem join_inf_eq_of_normal {A : Type u} [Group A]
    (B H D : Subgroup A) [B.Normal]
    (hHD : H ≤ D) (hBD : B ⊓ D ≤ H) : (B ⊔ H) ⊓ D = H := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx.1
    have hbD : b ∈ D := by
      have hproduct := D.mul_mem hx.2 (D.inv_mem (hHD hh))
      simpa only [mul_inv_cancel_right] using hproduct
    exact H.mul_mem (hBD ⟨hb, hbD⟩) hh
  · exact le_inf le_sup_right hHD

theorem comap_join_eq_of_normal {A : Type u} [Group A]
    (B H D : Subgroup A) [B.Normal]
    (hHD : H ≤ D) (hBD : B ⊓ D ≤ H) :
    localIntersection D (B ⊔ H) = localIntersection H (B ⊔ H) := by
  ext x
  change x.1 ∈ D ↔ x.1 ∈ H
  constructor
  · intro hx
    exact (join_inf_eq_of_normal B H D hHD hBD).le ⟨x.2, hx⟩
  · exact fun hx => hHD hx

def insideJoinEquiv {A : Type u} [Group A] (B H : Subgroup A) :
    localIntersection H (B ⊔ H) ≃* H where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, (show H ≤ B ⊔ H from le_sup_right) x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem insideJoinEquiv_toMonoidHom {A : Type u} [Group A] (B H : Subgroup A) :
    (insideJoinEquiv B H).toMonoidHom = localInclusion H (B ⊔ H) := by
  ext x
  rfl

theorem blockInductionAlong
    {p : ℕ} {k K G G' BG BH : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G] [Group G'] [Fintype G'] [Fintype BG] [Fintype BH]
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (square : eG.toMonoidHom.comp H.subtype = H'.subtype.comp eH.toMonoidHom)
    (rG : PrimeRegularRootEmbedding p k K G) (rH : PrimeRegularRootEmbedding p k K H)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injH : IrreducibleBrauerCharacterInjectivity rH)
    {bG : BG → k[G]} {bH : BH → k[H]}
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

variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A]

def AllSourceHBlocks (B D : Subgroup A)
    (globalCharacter : PrimeRegularClassFunction K A p)
    (localCharacter : PrimeRegularClassFunction K D p) : Prop :=
  ∀ (H : Subgroup A) (hHD : H ≤ D), B ⊓ D ≤ H →
    ExistsIntermediateBlocks (k := k) H globalCharacter
      (PrimeRegularClassFunction.pullback (Subgroup.inclusion hHD) localCharacter) (B ⊔ H)

theorem allSourceHBlocks_of_allIntermediateBlocks
    (B D : Subgroup A) [B.Normal]
    (globalCharacter : PrimeRegularClassFunction K A p)
    (localCharacter : PrimeRegularClassFunction K D p)
    (hall : AllIntermediateBlocks (k := k) D globalCharacter localCharacter B) :
    AllSourceHBlocks (k := k) B D globalCharacter localCharacter := by
  intro H hHD hBD
  let J := B ⊔ H
  obtain ⟨rJ, phiJ, rI, phiI, BJ, BI, dataJ, dataI, hOutput⟩ := hall J le_sup_left
  let _ : Fintype BJ := dataJ.fintypeBlock
  let _ : Fintype BI := dataI.fintypeBlock
  obtain ⟨hglobal, hlocal, hInd⟩ := hOutput
  let eG := MulEquiv.refl J
  let eI := MulEquiv.subgroupCongr (comap_join_eq_of_normal B H D hHD hBD)
  have square : eG.toMonoidHom.comp (localIntersection D J).subtype =
      (localIntersection H J).subtype.comp eI.toMonoidHom := by
    ext x
    rfl
  refine ⟨rJ.alongMulEquiv eG, IrreducibleBrauerCharacter.alongMulEquiv rJ eG phiJ,
    rI.alongMulEquiv eI, IrreducibleBrauerCharacter.alongMulEquiv rI eI phiI,
    BJ, BI, catalogueAlong dataJ eG, catalogueAlong dataI eI, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hglobal
  · apply PrimeRegularClassFunction.ext
    intro x
    exact congrArg (fun chi : PrimeRegularClassFunction K (localIntersection D J) p =>
      chi (PrimeRegularElement.map eI.symm.toMonoidHom x)) hlocal
  · exact blockInductionAlong (localIntersection D J) (localIntersection H J)
      eG eI square rJ rI
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding rJ)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding rI)
      dataJ.blocks dataI.blocks dataJ.catalogue dataI.catalogue phiJ phiI hInd

theorem allIntermediateBlocks_of_qOne
    (B D : Subgroup A) (hD : D = ⊤)
    (globalCharacter : PrimeRegularClassFunction K A p)
    (localCharacter : PrimeRegularClassFunction K D p)
    (hall : SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues.AllIntermediateBlocks
      (k := k) D hD globalCharacter localCharacter B) :
    AllIntermediateBlocks (k := k) D globalCharacter localCharacter B := by
  intro J hJ
  obtain ⟨rJ, phiJ, BJ, dataJ, hOutput⟩ := hall J hJ
  let _ : Fintype BJ := dataJ.fintypeBlock
  let eJ := intersectionEquiv D J hD
  refine ⟨rJ, phiJ, rJ.alongMulEquiv eJ.symm,
    IrreducibleBrauerCharacter.alongMulEquiv rJ eJ.symm phiJ,
    BJ, BJ, dataJ, catalogueAlong dataJ eJ.symm, ?_⟩
  exact ⟨hOutput.1, hOutput.2.1, hOutput.2.2.2⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateSourceH


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
