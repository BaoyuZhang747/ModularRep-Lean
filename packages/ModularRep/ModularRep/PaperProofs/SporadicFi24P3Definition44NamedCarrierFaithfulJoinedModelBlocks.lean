import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalModelBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralProductComparisons
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateSourceH

/-! One faithful comparison retains its models, all-H blocks and Q1 common characters. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulJoinedModelBlocks

universe u
section Models
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension
open SporadicFi24P3Definition44NamedCarrierOriginalTopExtensions
open SporadicFi24P3Definition44NamedCarrierOriginalTopIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
local notation "N" => Subgroup.normalizer (V.subgroup : Set G)
local instance normalizerFintype : Fintype N := Fintype.ofFinite _
local notation "B" => (⊤ : Subgroup G)
local notation "L" => (⊤ : Subgroup N)
local notation "eG" => (Subgroup.topEquiv.symm : G ≃* B)
local notation "eN" => (Subgroup.topEquiv.symm : N ≃* L)
local notation "rB" => iota.alongMulEquiv eG
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiB" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer

variable {UG UL : Type u}
variable [AddCommGroup UG] [Module k UG] [FiniteDimensional k UG]
variable [AddCommGroup UL] [Module k UL] [FiniteDimensional k UL]
variable (rhoG : Representation k (⊤ : Subgroup G) UG)
variable (rhoL : Representation k (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G))) UL)
variable (MG : AssociatedProjectiveModel (⊤ : Subgroup G) rhoG)
variable (ML : AssociatedProjectiveModel (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G))) rhoL)
variable (hMG : MG.factorSet = ScalarFactorSet.trivial)
variable (hML : ML.factorSet = ScalarFactorSet.trivial)


open SporadicFi24P3Definition44NamedCarrierOriginalModelBlockRows
open SporadicFi24P3Definition44NamedCarrierIntermediateSourceH

def OriginalModelSourceHBlocks : Prop :=
  ∃ globalW : BrauerCharacterExtensionWitness iota rB phiB,
    globalW.val = phi ∧
    globalW.val.val = (representationOfFactorOne MG hMG).brauerCharacterOfRootEmbedding iota ∧
    ∃ localW : BrauerCharacterExtensionWitness source.normalizerRoot rL phiL,
      localW.val = source.localBrauer ∧
      localW.val.val = (representationOfFactorOne ML hML).brauerCharacterOfRootEmbedding source.normalizerRoot ∧
      AllIntermediateBlocks (k := k) N globalW.val.val localW.val.val B ∧
      AllSourceHBlocks (k := k) B N globalW.val.val localW.val.val ∧
      (V.subgroup = ⊥ → PrimeRegularClassFunction.pullback (N).subtype globalW.val.val = localW.val.val)

theorem originalModelSourceHBlocks_of_blockRows
    (h : OriginalModelPairBlocks iota phi V source rhoG rhoL MG ML hMG hML)
    (hOne : V.subgroup = ⊥ → PrimeRegularClassFunction.pullback (N).subtype phi.val = source.localBrauer.val) :
    OriginalModelSourceHBlocks iota phi V source rhoG rhoL MG ML hMG hML := by
  obtain ⟨globalW, hglobal, hopG, localW, hlocal, hopL, hall⟩ := h
  refine ⟨globalW, hglobal, hopG, localW, hlocal, hopL, hall,
    allSourceHBlocks_of_allIntermediateBlocks B N globalW.val.val localW.val.val hall, ?_⟩
  intro hV
  rw [hglobal, hlocal]
  exact hOne hV

end Models
section Comparison
open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierProductModelTransport
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
open SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
open SporadicFi24P3Definition44NamedCarrierOriginalPairComparison


open SporadicFi24P3Definition44NamedCarrierCentralProductComparisons
open SporadicFi24P3Definition44NamedCarrierOriginalModelBlockRows
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)


open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierFaithfulCenterEquivariantReplacement

variable (nu : Subgroup.center G →* kˣ) (phi : ScalarBrauerSector iota nu)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)

local notation "B" => (⊤ : Subgroup G)
local notation "Z" => Subgroup.center G
local notation "N" => Subgroup.normalizer (V.subgroup : Set G)
local notation "L" => (⊤ : Subgroup N)
local notation "ZL" => Subgroup.comap (Subgroup.subtype N) Z
local notation "eG" => (Subgroup.topEquiv.symm : G ≃* B)
local notation "eN" => (Subgroup.topEquiv.symm : N ≃* L)
local notation "rG" => PrimeRegularRootEmbedding.alongMulEquiv iota eG
local notation "rL" => PrimeRegularRootEmbedding.alongMulEquiv source.normalizerRoot eN
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG (Subtype.val phi)
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer
local notation "rhoG" => globalRepresentation iota nu phi
local notation "rhoL" => localRepresentation iota V source
local notation "qE" => topQuotientEquiv (Subgroup.subtype N)

local notation "hBG" => top_sup_eq Z
local notation "hBL" => top_sup_eq ZL

def OriginalProductBlocksComparison : Prop :=
  Function.Surjective (innerEmbedding iota phi.1) ∧
  Subgroup.centralizer (B : Set G) = Z ∧
  B ⊔ Z = B ∧ L ⊔ ZL = L ∧
  (∀ a : G, IrreducibleBrauerCharacter.twist (gammaRoot iota)
    (gamma iota nu) (MulAut.conjNormal a) = gamma iota nu) ∧
  (∀ c : PrimeRegularElement (G := Z) p,
    (gamma iota nu).1 c = (gammaRoot iota).lift (nu c.1 : k)) ∧
  Function.Injective (ordinaryCentralLambda iota nu) ∧
  (∀ c d : Z, c * d = d * c) ∧
  (∀ z : PrimeRegularElement (G := Z) p,
    (gamma iota nu).val z = ordinaryCentralLambda iota nu z.val) ∧
  (∀ z : PrimeRegularElement (G := Z) p,
    phi.val.val (PrimeRegularElement.map (Subgroup.center G).subtype z) =
      phi.val.val ⟨1, isPrimeRegular_one⟩ * ordinaryCentralLambda iota nu z.val) ∧
  (L ⊔ ZL).map (Subgroup.subtype N) = (L).map (Subgroup.subtype N) ⊔ Z ∧
  ∃ (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL)
    (hMG : MG.factorSet = ScalarFactorSet.trivial)
    (hML : ML.factorSet = ScalarFactorSet.trivial),
    GlobalGammaProduct iota nu phi MG ∧
    LocalGammaProduct iota nu V source ML ∧
    (∀ n : N, qE (QuotientGroup.mk' L n) = QuotientGroup.mk' B n.1) ∧
    ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
    ScalarFactorSet.Cohomologous ML.factorSet (ScalarFactorSet.pullback qE MG.factorSet) ∧
    ProductModelOutput B (B ⊔ Z) L (L ⊔ ZL) hBG hBL rhoG rhoL MG ML qE (Subgroup.subtype N) ∧
    OriginalModelSourceHBlocks iota phi.val V source rhoG rhoL MG ML hMG hML

theorem original_product_blocks_of_comparison
    (hComparison : OriginalProductComparison iota nu phi V source)
    (hEvery : EveryOriginalModelPairBlocks iota phi.val V source)
    (hOne : V.subgroup = ⊥ → PrimeRegularClassFunction.pullback (N).subtype phi.val.val = source.localBrauer.val) :
    OriginalProductBlocksComparison iota nu phi V source := by
  obtain ⟨hsurj, hcentralizer, hBG0, hBL0, hfixed, hval,
    hlambda, hcomm, hgammaLambda, hlying, himage,
    MG, ML, hG, hL, hMG, hML, hq, hf, hc, hProduct⟩ := hComparison
  have hPair := every_original_model_pair_blocks_apply iota phi.val V source
    hEvery rhoG rhoL MG ML hMG hML hG.1 hG.2.1 hL.1 hL.2.1
  exact ⟨hsurj, hcentralizer, hBG0, hBL0, hfixed, hval,
    hlambda, hcomm, hgammaLambda, hlying, himage,
    MG, ML, hMG, hML, hG, hL, hq, hf, hc, hProduct,
    originalModelSourceHBlocks_of_blockRows iota phi.val V source
      rhoG rhoL MG ML hMG hML hPair hOne⟩

end Comparison
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulJoinedModelBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
