import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDerivedCoveringModelRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedBaseBlockTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-! The original matched base induction and literal model restriction supply every embedded model pair.
All root and catalogue transports use the literal specified square. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDerivedCoveringPhysicalRows

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (catalogueAlong UnselectedCatalogue)
open SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs
open SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
open SporadicFi24P3Definition44NamedCarrierDerivedCoveringModelRows
open SporadicFi24P3Definition44NamedCarrierEmbeddedBaseBlockTransport

universe u
variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Fintype A]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
local notation "N" => Subgroup.normalizer (V.subgroup : Set G)
local instance normalizerFintype : Fintype N := Fintype.ofFinite _
local instance subgroupFintype (B : Subgroup A) : Fintype B := Fintype.ofFinite _
local instance comapFintype (B D : Subgroup A) : Fintype (B.comap D.subtype) := Fintype.ofFinite _
variable (B : Subgroup A) [B.Normal] (D : Subgroup A)

theorem every_embedded_physical_model_pair_blocks_of_literal_restriction
    (eG : G ≃* B)
    (eN : Subgroup.normalizer (V.subgroup : Set G) ≃* B.comap D.subtype)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (hSquare : ∀ n : N, (eN n).val.val = (eG n.val : A))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {BG BN : Type u}
    (dataG : AmbientBlockCatalogueData (k := k) (G := G) (Block := BG))
    (dataN : AmbientBlockCatalogueData (k := k) (G := N) (Block := BN))
    (hInd : letI : Fintype BG := dataG.fintypeBlock
      letI : Fintype BN := dataN.fintypeBlock
      BlockInducesTo N dataN.catalogue dataG.catalogue
        (irreducibleBrauerCharacterBlock source.normalizerRoot
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataN.blocks source.localBrauer)
        (irreducibleBrauerCharacterBlock iota hinj dataG.blocks phi))
    (seed : Nonempty (PrimeRegularRootEmbedding p k K A))
    (fieldSource : SpathCoefficientField p k iota.prime)
    (hcyclic : IsCyclic (A ⧸ B))
    (cases : ∀ J : Subgroup A, B ≤ J → J = B ∨ J = ⊤)
    (Q : Subgroup A) (interval : CentralBrauerInterval (p := p) Q D)
    (ambient : B ≠ ⊤ → UnselectedCatalogue (k := k) (A := A))
    (localInput : letI : Fact p.Prime := ⟨iota.prime⟩
      B ≠ ⊤ → UnselectedIntervalCatalogue (k := k) Q D interval) :
    EveryEmbeddedModelPairBlocks B D (iota.alongMulEquiv eG) (source.normalizerRoot.alongMulEquiv eN) (IrreducibleBrauerCharacter.alongMulEquiv iota eG phi) (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer) := by
  let : Fact p.Prime := ⟨iota.prime⟩
  intro WG WL MG ML hMG hML hirrG haffordsG hirrL haffordsL
  exact embedded_model_pair_blocks_of_literal_restriction B D (iota.alongMulEquiv eG) (source.normalizerRoot.alongMulEquiv eN) (IrreducibleBrauerCharacter.alongMulEquiv iota eG phi) (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer) WG.ρ WL.ρ MG ML hMG hML
    S9495 S820 hirrG haffordsG hirrL haffordsL seed fieldSource hcyclic
    (catalogueAlong dataG eG) (catalogueAlong dataN eN) cases Q interval ambient localInput
    (embedded_base_block_induction N B D eG eN
      (embedded_base_square N B D eG eN hSquare)
      iota source.normalizerRoot hinj (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      phi source.localBrauer dataG dataN hInd)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDerivedCoveringPhysicalRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
