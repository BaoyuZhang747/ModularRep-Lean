import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedModels
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientModelBlockWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneModelRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFactorOneExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement

/-! The same centreless matched models give actual representation extensions.
The local pair and factor-set comparison are retained literally. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauerBlocks

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

open SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension

open ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicCompleteCollapseLemma52Actual (GlobalDefectZeroCharacter)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedModels
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBlockRows
open SporadicFi24P3Definition44NamedCarrierCentralQuotientModelBlockWitnesses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction
open SporadicFi24P3Definition44NamedCarrierSamePairQOneModelRows
open SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows
open SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (UnselectedCatalogue)
open SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)

section Centerless
open SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
variable (phi : IBr iota) (V : CharacterWeight p K G)
variable (Omega : IBr iota → ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (chi : IBr iota),
  Omega (a • chi) = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := p) (K := K) (G := G)) = Omega phi)
variable (source : CanonicalRawReduction iota V)
variable (hcenter : Subgroup.center G = ⊥)
local notation "AM" => ActualAutAmbient iota phi
local notation "B" => actualBase iota phi
local notation "D" => embeddedNormalizer (innerEmbedding iota phi) V.subgroup
local notation "L" => embeddedLocalBase (innerEmbedding iota phi) V.subgroup
local notation "eG" => actualBaseEquiv iota phi hcenter
local notation "eN" => normalizerBaseEquiv (innerEmbedding iota phi)
  (innerEmbedding_injective iota phi hcenter) V.subgroup
local notation "rG" => iota.alongMulEquiv eG
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv
  source.normalizerRoot eN source.localBrauer
local notation "qE" => matchedLocalQuotientEquiv iota phi V Omega hOmega hclass

local notation "C" => Subgroup.centralizer (B : Set AM)
local notation "CL" => Subgroup.comap (Subgroup.subtype D) C

local instance ambientFintype : Fintype AM := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup AM) : Fintype H := Fintype.ofFinite _
local instance localBaseFintype : Fintype L := Fintype.ofFinite _

def ReducedPairBrauerBlocksOutput : Prop :=
  C = ⊥ ∧
  ∃ (WG : FDRep k B) (WL : FDRep k L)
    (MG : AssociatedProjectiveModel B WG.ρ)
    (ML : AssociatedProjectiveModel L WL.ρ)
    (hMG : MG.factorSet = ScalarFactorSet.trivial)
    (hML : ML.factorSet = ScalarFactorSet.trivial),
    Representation.IsIrreducible WG.ρ ∧
    (phiG).val = Representation.brauerCharacterOfRootEmbedding WG.ρ rG ∧
    Representation.IsIrreducible WL.ρ ∧
    (phiL).val = Representation.brauerCharacterOfRootEmbedding WL.ρ rL ∧
    ((∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.val) ∧
    ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
    ScalarFactorSet.Cohomologous ML.factorSet (ScalarFactorSet.pullback qE MG.factorSet) ∧
    (∀ (b : B) (c : C), MG.operator (b.val * c.val) = WG.ρ b) ∧
    (∀ (l : L) (c : CL), ML.operator (l.val * c.val) = WL.ρ l) ∧
    (∀ a : AM, (extensionOfFactorOne MG hMG).representation a = MG.operator a) ∧
    (∀ d : D, (extensionOfFactorOne ML hML).representation d = ML.operator d) ∧
    (∀ b : B, (extensionOfFactorOne MG hMG).representation b = WG.ρ b) ∧
    (∀ l : L, (extensionOfFactorOne ML hML).representation l = WL.ρ l) ∧
    Representation.IsIrreducible (extensionOfFactorOne MG hMG).representation ∧
    Representation.IsIrreducible (extensionOfFactorOne ML hML).representation) ∧
    (V.subgroup ≠ ⊥ → ModelPairSourceHBlocks B D rG rL phiG phiL
      WG.ρ WL.ρ MG ML hMG hML) ∧
    (∀ hV : V.subgroup = ⊥,
      (∃ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G),
        IsBrauerReduction iota d.val phi ∧
        ∀ n : Subgroup.normalizer (V.subgroup : Set G),
          V.localCharacter (QuotientGroup.mk n) = d.val n.val) ∧
      PrimeRegularClassFunction.pullback (Subgroup.normalizer (V.subgroup : Set G)).subtype
        phi.val = source.localBrauer.val ∧
      CommonModelSourceHBlocks iota phi V source B eG D
        (embeddedNormalizer_eq_top (innerEmbedding iota phi) V.subgroup hV)
        L eN WG.ρ MG hMG)

variable {Block : Type u} [MulAction (MulAut G)ᵐᵒᵖ Block]

theorem reduced_pair_brauer_blocks
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (compatibility : CanonicalLocalBlockCompatibility iota O)
    (hblock : letI : Fintype Block := O.ambientBlockData.fintypeBlock
      irreducibleBrauerCharacterBlock iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        O.ambientBlockData.blocks phi = O.rawWeightBlock V)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (singleton : DefectZeroReductionBlockSingleton iota O)
    (seedProper : B ≠ ⊤ → Nonempty (PrimeRegularRootEmbedding p k K AM))
    (ambient : B ≠ ⊤ → UnselectedCatalogue (k := k) (A := AM))
    (localInputs : letI : Fact p.Prime := ⟨iota.prime⟩
      B ≠ ⊤ → PositiveLocalCatalogueInput (p := p) (k := k) (innerEmbedding iota phi)) :
    ReducedPairBrauerBlocksOutput iota phi V Omega hOmega hclass source hcenter := by
  have seed : Nonempty (PrimeRegularRootEmbedding p k K AM) := by
    by_cases hB : B = ⊤
    · exact ⟨(rG).alongMulEquiv ((MulEquiv.subgroupCongr hB).trans Subgroup.topEquiv)⟩
    · exact seedProper hB
  obtain ⟨hC, WG, WL, MG, ML, hMG, hML, hIG, hAG, hIL, hAL, hRest⟩ :=
    reduced_pair_models iota phi V Omega hOmega hclass source hcenter hOuter principle
  refine ⟨hC, WG, WL, MG, ML, hMG, hML, hIG, hAG, hIL, hAL, hRest, ?_, ?_⟩
  · intro hV
    have hEvery := reduced_every_model_pair_blocks iota phi V source O compatibility hblock
      hcenter hOuter hV S9295 S9495 S820 fieldSource seed ambient localInputs
    exact modelPairSourceHBlocks_of_blockRows B D rG rL phiG phiL WG.ρ WL.ρ MG ML hMG hML
      (hEvery WG WL MG ML hMG hML hIG hAG hIL hAL)
  · intro hV
    have hnorm := qOne_localBrauer_of_block_singleton iota O compatibility singleton
      phi V source hV hblock
    have hDtop := embeddedNormalizer_eq_top (innerEmbedding iota phi) V.subgroup hV
    have hSquare : (D).subtype.comp ((L).subtype.comp (eN).toMonoidHom) =
        (B).subtype.comp ((eG).toMonoidHom.comp
          (Subgroup.normalizer (V.subgroup : Set G)).subtype) := by
      ext n
      rfl
    have hEvery := every_model_common iota phi V source B eG D hDtop L eN hSquare hnorm.2 seed
    have hAll := common_pair_intermediate_blocks iota phi V source B eG D hDtop L eN
      O.ambientBlockData (actual_intermediate_eq_base_or_top iota phi hOuter) ambient
    exact ⟨hnorm.1, hnorm.2,
      commonModelSourceHBlocks_of_common iota phi V source B eG D hDtop L eN WG.ρ MG hMG
        hAll (hEvery WG MG hMG hIG hAG)⟩

end Centerless
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauerBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
