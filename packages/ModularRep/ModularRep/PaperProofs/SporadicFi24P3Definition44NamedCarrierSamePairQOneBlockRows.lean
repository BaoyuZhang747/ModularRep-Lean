import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCommonExtension

/-! All intermediate block laws for every actual common extension pair.
Only the proper-base case needs an unselected ambient catalogue. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows

open ModularRep ModularRep.CharacterWeight
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups
open SporadicFi24P3Definition44NamedCarrierQOneCommonExtension
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension

universe u
variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Fintype A]
local instance subgroupFintype (H : Subgroup A) : Fintype H := Fintype.ofFinite H
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
variable (B : Subgroup A) (eG : G ≃* B)
variable (D : Subgroup A) (hD : D = ⊤) (L : Subgroup D)
variable (eN : Subgroup.normalizer (V.subgroup : Set G) ≃* L)
local notation "rB" => iota.alongMulEquiv eG
local notation "phiB" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer

def CommonPairIntermediateBlocks : Prop :=
  ∀ (rA : PrimeRegularRootEmbedding p k K A)
    (globalW : BrauerCharacterExtensionWitness rA rB phiB)
    (localW : BrauerCharacterExtensionWitness
      (rA.alongMulEquiv (ambientEquivOfEqTop D hD).symm) rL phiL),
    PrimeRegularClassFunction.pullback D.subtype globalW.val.val = localW.val.val →
    AllIntermediateBlocks (k := k) D hD globalW.val.val localW.val.val B

theorem common_pair_intermediate_blocks
    {Block : Type u}
    (baseData : AmbientBlockCatalogueData (k := k) (G := G) (Block := Block))
    (interval : ∀ J : Subgroup A, B ≤ J → J = B ∨ J = ⊤)
    (ambient : B ≠ ⊤ → UnselectedCatalogue (k := k) (A := A)) :
    CommonPairIntermediateBlocks iota phi V source B eG D hD L eN := by
  intro rA globalW localW hcommon J hJ
  by_cases hbase : J = B
  · subst J
    exact exists_intermediate_blocks_of_catalogue D hD globalW.val.val localW.val.val
      B rB phiB (catalogueAlong baseData eG) hcommon globalW.property
  · have htop := (interval J hJ).resolve_left hbase
    have hB : B ≠ ⊤ := by
      intro hB
      exact hbase (htop.trans hB.symm)
    subst J
    obtain ⟨BlockA, ⟨dataA⟩⟩ := ambient hB
    let eTop : A ≃* (⊤ : Subgroup A) := Subgroup.topEquiv.symm
    let rTop := rA.alongMulEquiv eTop
    let phiTop := IrreducibleBrauerCharacter.alongMulEquiv rA eTop globalW.val
    apply exists_intermediate_blocks_of_catalogue D hD globalW.val.val localW.val.val
      (⊤ : Subgroup A) rTop phiTop (catalogueAlong dataA eTop) hcommon
    apply PrimeRegularClassFunction.ext
    intro x
    rfl

variable {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable [B.Normal] (rho : Representation k B W)

/-- Open the old common pair once and attach the block law to those exact witnesses. -/
theorem common_extension_with_intermediate_blocks
    (M : AssociatedProjectiveModel B rho) (hM : M.factorSet = ScalarFactorSet.trivial)
    (rA : PrimeRegularRootEmbedding p k K A)
    (hBlocks : CommonPairIntermediateBlocks iota phi V source B eG D hD L eN)
    (hCommon : CommonExtensionFromModel iota phi V source B eG D hD L eN rho M hM rA) :
    ∃ globalW : BrauerCharacterExtensionWitness rA rB phiB,
      globalW.val.val = (representationOfFactorOne M hM).brauerCharacterOfRootEmbedding rA ∧
      ∃ localW : BrauerCharacterExtensionWitness
        (rA.alongMulEquiv (ambientEquivOfEqTop D hD).symm) rL phiL,
        PrimeRegularClassFunction.pullback D.subtype globalW.val.val = localW.val.val ∧
        AllIntermediateBlocks (k := k) D hD globalW.val.val localW.val.val B := by
  obtain ⟨globalW, hoperator, localW, hcommon⟩ := hCommon
  exact ⟨globalW, hoperator, localW, hcommon, hBlocks rA globalW localW hcommon⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
