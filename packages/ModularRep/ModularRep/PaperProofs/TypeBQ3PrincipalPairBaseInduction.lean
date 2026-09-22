import ModularRep.PaperProofs.TypeBQ3PrincipalMatchedPairInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
import ModularRep.DefectNormalizerCarrier

/-!
# Base block induction and the actual embedded radical interval

The matched raw weight has the same specified principal block as the Brauer
character. The selected canonical reduction and its guarded local block
equality therefore give induction between their actual character blocks.
The embedded radical supplies its central Brauer interval inside the actual
normalizer. Neither induction nor the interval is an additional source.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3PrincipalPairBaseInduction

open ModularRep CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelBrauerBlocks
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

private theorem characterBlock_eq_of_idempotents
    [Fintype (LiteralPrimitiveBlock k (G (ZMod 3)))]
    (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
    {c d : LiteralPrimitiveBlock k (G (ZMod 3)) → k[G (ZMod 3)]}
    (Dc : BlockIdempotentDecomposition c) (Dd : BlockIdempotentDecomposition d)
    (same : c = d) (phi : IBr root) :
    irreducibleBrauerCharacterBlock root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) Dc phi =
      irreducibleBrauerCharacterBlock root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) Dd phi := by
  cases same
  rfl

/-- Literal support computes the block in the original operations catalogue. -/
theorem principalCharacter_block
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
    (b : LiteralPrimitiveBlock k (G (ZMod 3)))
    (phi : OmegaBrauer (ZMod 3) root b) :
    letI := S.operations.ambientBlockData.fintypeBlock
    irreducibleBrauerCharacterBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      S.operations.ambientBlockData.blocks phi.val = b := by
  letI := S.operations.ambientBlockData.fintypeBlock
  have physical : irreducibleBrauerCharacterBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      (omegaDecomposition (ZMod 3) S literal) phi.val = b :=
    (supported_iff_block root (omegaDecomposition (ZMod 3) S literal) b phi.val).mp
      phi.property
  exact (characterBlock_eq_of_idempotents root S.operations.ambientBlockData.blocks
    (omegaDecomposition (ZMod 3) S literal) (funext literal) phi.val).trans physical

/-- The same local reduction induces to the block of the same matched character. -/
theorem baseBlockInducesTo
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
    (b : LiteralPrimitiveBlock k (G (ZMod 3)))
    (seed : OmegaBrauer (ZMod 3) root b ≃ OmegaWeight (ZMod 3) S b)
    (phi : OmegaBrauer (ZMod 3) root b)
    (W : CharacterWeight 2 K (G (ZMod 3)))
    (matched : classOf W = (seed phi).val)
    (reduction : CanonicalRawReduction root W)
    (compatibility :
      NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          S.operations W.subgroup reduction.normalizerRoot reduction.localBrauer =
        S.operations.inflateToNormalizer W.subgroup
          (S.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)) :
    letI := S.operations.ambientBlockData.fintypeBlock
    letI := (S.operations.inflatedNormalizerBlockData W.subgroup).fintypeBlock
    BlockInducesTo (Subgroup.normalizer (W.subgroup : Set (G (ZMod 3))))
      (S.operations.inflatedNormalizerBlockData W.subgroup).catalogue
      S.operations.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock reduction.normalizerRoot
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding reduction.normalizerRoot)
        (S.operations.inflatedNormalizerBlockData W.subgroup).blocks reduction.localBrauer)
      (irreducibleBrauerCharacterBlock root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
        S.operations.ambientBlockData.blocks phi.val) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := (S.operations.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  rw [principalCharacter_block S literal root b phi]
  change BlockInducesTo (Subgroup.normalizer (W.subgroup : Set (G (ZMod 3))))
    (S.operations.inflatedNormalizerBlockData W.subgroup).catalogue
    S.operations.ambientBlockData.catalogue
    (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
      S.operations W.subgroup reduction.normalizerRoot reduction.localBrauer) b
  rw [compatibility]
  have supported : S.operations.induceToAmbient W = b :=
    TypeBQ3PrincipalMatchedPairInvariance.matched_rawWeightBlock S root b seed phi W matched
  rw [← supported]
  exact inducedBlock_spec (Subgroup.normalizer (W.subgroup : Set (G (ZMod 3))))
    (S.operations.inflatedNormalizerBlockData W.subgroup).catalogue
    S.operations.ambientBlockData.catalogue _ (S.operations.blockInductionDefined W)

/-- The image of the actual radical is a two-group inside its actual normalizer. -/
def embeddedRadicalInterval
    (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3))) (phi : IBr root)
    (W : CharacterWeight 2 K (G (ZMod 3))) :
    CentralBrauerInterval (p := 2)
      (W.subgroup.map (innerEmbedding root phi))
      (embeddedNormalizer (innerEmbedding root phi) W.subgroup) :=
  normalizerCentralBrauerInterval (W.radical.isPGroup.map (innerEmbedding root phi))

end ModularRep.PaperProofs.TypeBQ3PrincipalPairBaseInduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
