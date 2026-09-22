import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
import ModularRep.CentralCharacterCovering

/-! The published local H range follows from the intermediate J range by
normality and the literal equality (B H) intersect D = H. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedSourceHBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (catalogueAlong)
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions

universe u

theorem join_intersection_eq_of_normal {A : Type u} [Group A]
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

theorem local_intersection_join_eq {A : Type u} [Group A]
    (B H D : Subgroup A) [B.Normal]
    (hHD : H ≤ D) (hBD : B ⊓ D ≤ H) :
    localIntersection D (B ⊔ H) = localIntersection H (B ⊔ H) := by
  ext x
  change x.val ∈ D ↔ x.val ∈ H
  exact ⟨fun hx => (join_intersection_eq_of_normal B H D hHD hBD).le ⟨x.property, hx⟩,
    fun hx => hHD hx⟩

variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A]
local instance subgroupFintype (J : Subgroup A) : Fintype J := Fintype.ofFinite _
local instance intersectionFintype (D J : Subgroup A) : Fintype (localIntersection D J) := Fintype.ofFinite _

def AllSourceHBlocks (B D : Subgroup A)
    (globalCharacter : PrimeRegularClassFunction K A p)
    (localCharacter : PrimeRegularClassFunction K D p) : Prop :=
  ∀ (H : Subgroup A) (hHD : H ≤ D), B ⊓ D ≤ H →
    ExistsIntermediateBlocks (k := k) H globalCharacter
      (PrimeRegularClassFunction.pullback (Subgroup.inclusion hHD) localCharacter) (B ⊔ H)

theorem all_source_h_blocks_of_all_intermediate
    (B D : Subgroup A) [B.Normal]
    (globalCharacter : PrimeRegularClassFunction K A p)
    (localCharacter : PrimeRegularClassFunction K D p)
    (hall : AllIntermediateBlocks (k := k) D globalCharacter localCharacter B) :
    AllSourceHBlocks (k := k) B D globalCharacter localCharacter := by
  intro H hHD hBD
  let J := B ⊔ H
  let eL : localIntersection D J ≃* localIntersection H J :=
    MulEquiv.subgroupCongr (local_intersection_join_eq B H D hHD hBD)
  obtain ⟨rJ, phiJ, rL, phiL, BJ, BL, dataJ, dataL, hglobal, hlocal, hInd⟩ := hall J le_sup_left
  let : Fintype BJ := dataJ.fintypeBlock
  let : Fintype BL := dataL.fintypeBlock
  refine ⟨rJ, phiJ, rL.alongMulEquiv eL,
    IrreducibleBrauerCharacter.alongMulEquiv rL eL phiL,
    BJ, BL, dataJ, catalogueAlong dataL eL, hglobal, ?_, ?_⟩
  · apply PrimeRegularClassFunction.ext
    intro x
    exact congrArg
      (fun chi : PrimeRegularClassFunction K (localIntersection D J) p =>
        chi (PrimeRegularElement.map eL.symm.toMonoidHom x)) hlocal
  · change BlockInducesTo (localIntersection H J)
      (dataL.catalogue.alongMulEquiv eL) dataJ.catalogue
      (irreducibleBrauerCharacterBlock (rL.alongMulEquiv eL)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        (dataL.blocks.alongMulEquiv eL) (IrreducibleBrauerCharacter.alongMulEquiv rL eL phiL))
      (irreducibleBrauerCharacterBlock rJ
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataJ.blocks phiJ)
    rw [irreducibleBrauerCharacterBlock_alongMulEquiv rL
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) eL
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataL.blocks phiL]
    exact blockInducesTo_alongMulEquiv (localIntersection D J) (localIntersection H J)
      (MulEquiv.refl J) eL (by ext x; rfl)
      dataL.catalogue dataJ.catalogue (dataL.catalogue.alongMulEquiv eL) dataJ.catalogue
      rfl (by
        apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
          (MulEquiv.refl J) dataJ.catalogue dataJ.catalogue
        apply Subtype.ext
        change MonoidAlgebra.domCongr k k (MulEquiv.refl J) _ = _
        rw [MonoidAlgebra.domCongr_refl]
        rfl) hInd

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedSourceHBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
