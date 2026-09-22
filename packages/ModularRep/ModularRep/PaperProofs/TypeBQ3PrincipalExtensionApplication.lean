import ModularRep.PaperProofs.TypeBQ3PrincipalPairExtensions
import ModularRep.PaperProofs.TypeBQ3PrincipalPairBlockChoice
import ModularRep.PaperProofs.TypeBQ3PrincipalPairBaseInduction
import ModularRep.PaperProofs.TypeBQ3PrincipalInertiaQuotient
import ModularRep.PaperProofs.TypeBCentralKernelTripleCertificate

/-!
# Principal matched extensions and every intermediate block at q = 3

The same principal correspondence fixes the local character in the actual
automorphism inertia. Both cyclic extensions are constructed before their
blocks are compared. Covering uniqueness over the quotient of order at most
two proves the top equality, and every intermediate group is base or top.
The record below is an output, never a source premise.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalExtensionApplication

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open TypeBQ3PrincipalPairBlockChoice
open TypeBQ3PrincipalPairBaseInduction
open Representation.Extension
open NavarroBrauerRestrictionCovering

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Both actual extensions and their block equations on every intermediate. -/
structure MatchedExtensionData
    {Y : Type} [Group Y] [Finite Y]
    (root : PrimeRegularRootEmbedding 2 k K Y) (phi : IBr root)
    (W : CharacterWeight 2 K Y) (reduction : CanonicalRawReduction root W)
    (hcenter : Subgroup.center Y = ⊥) where
  globalRoot : PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi)
  localRoot : PrimeRegularRootEmbedding 2 k K
    (embeddedNormalizer (innerEmbedding root phi) W.subgroup)
  globalExtension : BrauerCharacterExtensionWitness globalRoot
    (root.alongMulEquiv (actualBaseEquiv root phi hcenter))
    (IrreducibleBrauerCharacter.alongMulEquiv root
      (actualBaseEquiv root phi hcenter) phi)
  localExtension : BrauerCharacterExtensionWitness localRoot
    (reduction.normalizerRoot.alongMulEquiv
      (normalizerBaseEquiv (innerEmbedding root phi)
        (innerEmbedding_injective root phi hcenter) W.subgroup))
    (IrreducibleBrauerCharacter.alongMulEquiv reduction.normalizerRoot
      (normalizerBaseEquiv (innerEmbedding root phi)
        (innerEmbedding_injective root phi hcenter) W.subgroup) reduction.localBrauer)
  globalAgreement : ∀ zeta : rootsOfUnity
      (primeRegularExponent 2 (actualBase root phi)) k,
    (root.alongMulEquiv (actualBaseEquiv root phi hcenter)).lift ((zeta : kˣ) : k) =
      globalRoot.lift ((zeta : kˣ) : k)
  localAgreement : ∀ zeta : rootsOfUnity
      (primeRegularExponent 2 (embeddedLocalBase (innerEmbedding root phi) W.subgroup)) k,
    (reduction.normalizerRoot.alongMulEquiv
      (normalizerBaseEquiv (innerEmbedding root phi)
        (innerEmbedding_injective root phi hcenter) W.subgroup)).lift ((zeta : kˣ) : k) =
      localRoot.lift ((zeta : kˣ) : k)
  intermediate : ∀ J : Subgroup (ActualAutAmbient root phi), actualBase root phi ≤ J →
    IntermediateBlockData 2 k K
      (embeddedNormalizer (innerEmbedding root phi) W.subgroup)
      globalExtension.val.val localExtension.val.val J

/-- The explicit bound includes the trivial quotient. -/
theorem inertia_isTwoGroup
    (root : PrimeRegularRootEmbedding 2 k K G3) (phi : IBr root)
    (bound : Nat.card (ActualAutAmbient root phi ⧸ actualBase root phi) ≤ 2) :
    IsPGroup 2 (ActualAutAmbient root phi ⧸ actualBase root phi) := by
  have positive : 0 < Nat.card (ActualAutAmbient root phi ⧸ actualBase root phi) :=
    Nat.card_pos
  have casesCard : Nat.card (ActualAutAmbient root phi ⧸ actualBase root phi) = 1 ∨
      Nat.card (ActualAutAmbient root phi ⧸ actualBase root phi) = 2 := by omega
  rcases casesCard with one | two
  · exact IsPGroup.of_card (p := 2) (n := 0) (by simpa only [pow_zero] using one)
  · exact IsPGroup.of_card (p := 2) (n := 1) (by simpa only [pow_one] using two)

/-- The actual matched pair supplies the base induction and local invariance.
Only routine extension and covering statements remain external inputs. -/
theorem exists_matched_extensions_all_intermediate
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (root : PrimeRegularRootEmbedding 2 k K G3)
    (b : LiteralPrimitiveBlock k G3) (hb : IsPrincipal b)
    (seed : OmegaBrauer (ZMod 3) root b ≃ OmegaWeight (ZMod 3) S b)
    (seedSO : ∀ (h : H (ZMod 3)) (theta : OmegaBrauer (ZMod 3) root b),
      seed (brauerStep (ZMod 3) S literal root b hb h theta) =
        weightStep (ZMod 3) S literal b hb h (seed theta))
    (phi : OmegaBrauer (ZMod 3) root b) (W : CharacterWeight 2 K G3)
    (matched : TypeBQ3PrincipalPairExtensions.rawClass W = (seed phi).val)
    (reduction : CanonicalRawReduction root W)
    (compatibility :
      NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        S.operations W.subgroup reduction.normalizerRoot reduction.localBrauer =
      S.operations.inflateToNormalizer W.subgroup
        (S.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
    (ambientBlocks : PhysicalBlocks k (ActualAutAmbient root phi.val))
    (localBlocks : PhysicalBlocks k
      (embeddedNormalizer (innerEmbedding root phi.val) W.subgroup))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (ambientSeed : PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi.val))
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
    (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k)
    (S414 : letI := localBlocks.blockFintype
      Navarro414IntervalCentralCharacterSource (embeddedRadicalInterval root phi.val W)
        localBlocks.decomposition localBlocks.catalogue) :
    Nonempty (MatchedExtensionData root phi.val W reduction
      (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource)) := by
  let hcenter := TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource
  let A := ActualAutAmbient root phi.val
  let B := actualBase root phi.val
  let D := embeddedNormalizer (innerEmbedding root phi.val) W.subgroup
  let eG := actualBaseEquiv root phi.val hcenter
  let eN := normalizerBaseEquiv (innerEmbedding root phi.val)
    (innerEmbedding_injective root phi.val hcenter) W.subgroup
  have bound : Nat.card (A ⧸ B) ≤ 2 :=
    TypeBQ3PrincipalInertiaQuotient.actual_quotient_card_le_two
      automorphisms indexTwo root phi.val
  obtain ⟨rA, rD, globalExt, localExt, globalAgreement, localAgreement⟩ :=
    TypeBQ3PrincipalPairExtensions.exists_pair_extensions root phi.val W
      (TypeBQ3PrincipalMatchedPairInvariance.pairClassFixed
        S literal root b hb seed seedSO automorphisms phi W matched)
      reduction hcenter bound principle ambientSeed
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := (S.operations.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI := ambientBlocks.blockFintype
  letI := localBlocks.blockFintype
  have square := baseSquare_of_localEmbedding
    (Subgroup.normalizer (W.subgroup : Set G3)) B D eG eN (fun _ => rfl)
  have baseInduction := baseBlockInducesTo S literal root b seed phi W matched
    reduction compatibility
  let intermediate := allIntermediateBlockData
    (Subgroup.normalizer (W.subgroup : Set G3)) B D eG eN square
    root reduction.normalizerRoot rA rD
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding reduction.normalizerRoot)
    S.operations.ambientBlockData.blocks
    (S.operations.inflatedNormalizerBlockData W.subgroup).blocks
    ambientBlocks.decomposition localBlocks.decomposition
    S.operations.ambientBlockData.catalogue
    (S.operations.inflatedNormalizerBlockData W.subgroup).catalogue
    ambientBlocks.catalogue localBlocks.catalogue
    phi.val reduction.localBrauer globalExt localExt globalAgreement localAgreement
    fieldSource (inertia_isTwoGroup root phi.val bound) bound
    (W.subgroup.map (innerEmbedding root phi.val)) (embeddedRadicalInterval root phi.val W)
    S414 S9295 S96 baseInduction
  exact ⟨⟨rA, rD, globalExt, localExt, globalAgreement, localAgreement, intermediate⟩⟩

end ModularRep.PaperProofs.TypeBQ3PrincipalExtensionApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
