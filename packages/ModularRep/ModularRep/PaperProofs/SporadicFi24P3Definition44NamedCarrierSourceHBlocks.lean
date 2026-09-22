import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket
import ModularRep.CentralCharacterCovering
import ModularRep.IBrBlockEquivTransport

/-!
# The literal H interval in Spath Definition 4.1(iii)(4)

For base intersect D <= H <= D, normality gives (base H) intersect D = H.
Transport the already selected restriction characters and their complete
block catalogues through this equality. No product decomposition of A or
new induction assertion is assumed.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSourceHBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

theorem join_inf_eq_of_normal {A : Type u} [Group A]
    (base H D : Subgroup A) [base.Normal]
    (hHD : H ≤ D) (hbaseD : base ⊓ D ≤ H) : (base ⊔ H) ⊓ D = H := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx.1
    have hbD : b ∈ D := by
      have hproduct := D.mul_mem hx.2 (D.inv_mem (hHD hh))
      simpa only [mul_inv_cancel_right] using hproduct
    exact H.mul_mem (hbaseD ⟨hb, hbD⟩) hh
  · exact le_inf le_sup_right hHD

theorem comap_join_eq_of_normal {A : Type u} [Group A]
    (base H D : Subgroup A) [base.Normal]
    (hHD : H ≤ D) (hbaseD : base ⊓ D ≤ H) :
    localIntersection D (base ⊔ H) = localIntersection H (base ⊔ H) := by
  ext x
  change x.1 ∈ D ↔ x.1 ∈ H
  constructor
  · intro hx
    exact (join_inf_eq_of_normal base H D hHD hbaseD).le ⟨x.2, hx⟩
  · intro hx
    exact hHD hx

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

def sourceHBlockData {P : Definition35Problem.{u}} {psi : Definition35Brauer P}
    {V : CharacterWeight P.p P.K P.H} (packet : ActualWeightPacket P psi V)
    (H : Subgroup packet.ambient.A) (hHD : H ≤ packet.localGroup)
    (hbaseD : packet.ambient.base ⊓ packet.localGroup ≤ H) :
    ActualIntermediateBlockData P H packet.globalCharacter.1
      (PrimeRegularClassFunction.pullback (Subgroup.inclusion hHD) packet.localCharacter.1)
      (packet.ambient.base ⊔ H) := by
  let J := packet.ambient.base ⊔ H
  let B := packet.intermediateBlocks J le_sup_left
  let eG := MulEquiv.refl J
  let eH := MulEquiv.subgroupCongr
    (comap_join_eq_of_normal packet.ambient.base H packet.localGroup hHD hbaseD)
  have hsquare : eG.toMonoidHom.comp (localIntersection packet.localGroup J).subtype =
      (localIntersection H J).subtype.comp eH.toMonoidHom := by
    ext x
    rfl
  refine {
    globalRoot := B.globalRoot.alongMulEquiv eG
    globalBrauer := IrreducibleBrauerCharacter.alongMulEquiv B.globalRoot eG B.globalBrauer
    globalRestriction := ?_
    localRoot := B.localRoot.alongMulEquiv eH
    localBrauer := IrreducibleBrauerCharacter.alongMulEquiv B.localRoot eH B.localBrauer
    localRestriction := ?_
    GlobalBlock := B.GlobalBlock
    LocalBlock := B.LocalBlock
    globalBlockIdempotent := fun b => MonoidAlgebra.domCongr P.k P.k eG (B.globalBlockIdempotent b)
    localBlockIdempotent := fun b => MonoidAlgebra.domCongr P.k P.k eH (B.localBlockIdempotent b)
    globalBlocks := B.globalBlocks.alongMulEquiv eG
    localBlocks := B.localBlocks.alongMulEquiv eH
    globalBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    localBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    globalCentralCharacters := B.globalCentralCharacters.alongMulEquiv eG
    localCentralCharacters := B.localCentralCharacters.alongMulEquiv eH
    globalCentralCharactersNavarro311 := ⟨B.globalCentralCharactersNavarro311.fieldSource⟩
    localCentralCharactersNavarro311 := ⟨B.localCentralCharactersNavarro311.fieldSource⟩
    inductionEquality := transportedInduction _ _ eG eH hsquare B.globalRoot B.localRoot
      B.globalBrauerInjective B.localBrauerInjective B.globalBlocks B.localBlocks
      B.globalCentralCharacters B.localCentralCharacters B.globalBrauer B.localBrauer B.inductionEquality }
  · exact B.globalRestriction
  · apply PrimeRegularClassFunction.ext
    intro x
    exact congrArg (fun chi => chi (PrimeRegularElement.map eH.symm.toMonoidHom x)) B.localRestriction

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSourceHBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
