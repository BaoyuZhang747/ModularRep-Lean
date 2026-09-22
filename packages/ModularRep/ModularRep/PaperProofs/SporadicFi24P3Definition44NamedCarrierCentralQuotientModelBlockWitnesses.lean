import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateSourceH
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFactorOneExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs

/-! Retain the initial global and fixed local model characters, then select
the global extension with every intermediate block law and its explicit twist. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientModelBlockWitnesses

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension
open SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (UnselectedCatalogue)
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
open SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs

open SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
open SporadicFi24P3Definition44NamedCarrierIntermediateSourceH

universe u
section Pair
variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A]
local instance subgroupFintype (B : Subgroup A) : Fintype B := Fintype.ofFinite _
local instance comapFintype (B D : Subgroup A) : Fintype (B.comap D.subtype) := Fintype.ofFinite _
variable (B : Subgroup A) [B.Normal] (D : Subgroup A)
variable (rB : PrimeRegularRootEmbedding p k K B)
variable (rM : PrimeRegularRootEmbedding p k K (B.comap D.subtype))
variable (phiB : IBr rB) (phiM : IBr rM)
variable {UG UL : Type u}
variable [AddCommGroup UG] [Module k UG] [FiniteDimensional k UG]
variable [AddCommGroup UL] [Module k UL] [FiniteDimensional k UL]
variable (rhoG : Representation k B UG) (rhoL : Representation k (B.comap D.subtype) UL)
variable (MG : AssociatedProjectiveModel B rhoG)
variable (ML : AssociatedProjectiveModel (B.comap D.subtype) rhoL)
variable (hMG : MG.factorSet = ScalarFactorSet.trivial) (hML : ML.factorSet = ScalarFactorSet.trivial)

def ModelPairSourceHBlocks : Prop :=
  ∃ (rA : PrimeRegularRootEmbedding p k K A) (rD : PrimeRegularRootEmbedding p k K D),
    (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
    (∀ zeta : rootsOfUnity (primeRegularExponent p (B.comap D.subtype)) k,
      rM.lift (((zeta : kˣ) : k)) = rD.lift (((zeta : kˣ) : k))) ∧
    ∃ (initialGlobal : BrauerCharacterExtensionWitness rA rB phiB)
      (fixedLocal : BrauerCharacterExtensionWitness rD rM phiM),
      initialGlobal.val.val = (representationOfFactorOne MG hMG).brauerCharacterOfRootEmbedding rA ∧
      fixedLocal.val.val = (representationOfFactorOne ML hML).brauerCharacterOfRootEmbedding rD ∧
      ∃ (selectedGlobal : BrauerCharacterExtensionWitness rA rB phiB) (lambda : (A ⧸ B) →* Kˣ),
        (∀ x : PrimeRegularElement (G := A) p,
          selectedGlobal.val.val x =
            (lambda (QuotientGroup.mk' B x.val) : K) * initialGlobal.val.val x) ∧
        AllIntermediateBlocks (k := k) D selectedGlobal.val.val fixedLocal.val.val B ∧
        AllSourceHBlocks (k := k) B D selectedGlobal.val.val fixedLocal.val.val

theorem modelPairSourceHBlocks_of_blockRows
    (h : EmbeddedModelPairBlocks B D rB rM phiB phiM rhoG rhoL MG ML hMG hML) :
    ModelPairSourceHBlocks B D rB rM phiB phiM rhoG rhoL MG ML hMG hML := by
  obtain ⟨rA, rD, hRG, hRL, initialGlobal, fixedLocal, hIG, hIL,
    selectedGlobal, lambda, htwist, hall⟩ := h
  exact ⟨rA, rD, hRG, hRL, initialGlobal, fixedLocal, hIG, hIL,
    selectedGlobal, lambda, htwist, hall,
    allSourceHBlocks_of_allIntermediateBlocks B D selectedGlobal.val.val fixedLocal.val.val hall⟩

end Pair

section Common
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups
open SporadicFi24P3Definition44NamedCarrierQOneCommonExtension
open SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows

variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Fintype A]
local instance commonSubgroupFintype (H : Subgroup A) : Fintype H := Fintype.ofFinite H
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
variable (B : Subgroup A) [B.Normal] (eG : G ≃* B)
variable (D : Subgroup A) (hD : D = ⊤) (L : Subgroup D)
variable (eN : Subgroup.normalizer (V.subgroup : Set G) ≃* L)
variable {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable (rho : Representation k B W) (M : AssociatedProjectiveModel B rho)
variable (hM : M.factorSet = ScalarFactorSet.trivial)
local notation "rB" => iota.alongMulEquiv eG
local notation "phiB" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer

def CommonModelSourceHBlocks : Prop :=
  ∃ rA : PrimeRegularRootEmbedding p k K A,
    (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      (rB).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
    ∃ globalW : BrauerCharacterExtensionWitness rA rB phiB,
      globalW.val.val = (representationOfFactorOne M hM).brauerCharacterOfRootEmbedding rA ∧
      ∃ localW : BrauerCharacterExtensionWitness
        (rA.alongMulEquiv (ambientEquivOfEqTop D hD).symm) rL phiL,
        PrimeRegularClassFunction.pullback D.subtype globalW.val.val = localW.val.val ∧
        AllIntermediateBlocks (k := k) D globalW.val.val localW.val.val B ∧
        AllSourceHBlocks (k := k) B D globalW.val.val localW.val.val

theorem commonModelSourceHBlocks_of_common
    (hBlocks : CommonPairIntermediateBlocks iota phi V source B eG D hD L eN)
    (hCommon : ∃ rA : PrimeRegularRootEmbedding p k K A,
      (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
        (rB).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
      CommonExtensionFromModel iota phi V source B eG D hD L eN rho M hM rA) :
    CommonModelSourceHBlocks iota phi V source B eG D hD L eN rho M hM := by
  obtain ⟨rA, hroots, hCommon⟩ := hCommon
  obtain ⟨globalW, hoperator, localW, hcommon, hall⟩ :=
    common_extension_with_intermediate_blocks iota phi V source B eG D hD L eN
      rho M hM rA hBlocks hCommon
  have hallJ := allIntermediateBlocks_of_qOne B D hD globalW.val.val localW.val.val hall
  exact ⟨rA, hroots, globalW, hoperator, localW, hcommon, hallJ,
    allSourceHBlocks_of_allIntermediateBlocks B D globalW.val.val localW.val.val hallJ⟩

end Common
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientModelBlockWitnesses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
