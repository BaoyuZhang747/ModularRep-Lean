import ModularRep.PaperProofs.TypeBQ3PrincipalLocalApplication
import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionAnchors
import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionCentralQuotient
import ModularRep.PaperProofs.TypeBModularGroupRootBinding

/-!
# Extension data for one character and its retained inflation graph

The given graph supplies one actual raw pair. The selected lower reduction,
both extensions, every intermediate block equation, and the two value
identities refer to that pair and the original principal character.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalExtensionPointwise

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding
open TypeBQ3TripleCoverCarrier
open TypeBQ3PrincipalWeightInflation
open TypeBQ3PrincipalTripleCoverApplication
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open TypeBQ3PrincipalExtensionApplication TypeBQ3PrincipalExtensionAnchors
open TypeBQ3PrincipalPairBlockChoice
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open NavarroBrauerRestrictionCovering

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  TypeBQ3PrincipalLocalApplication.groupFintype Y

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

attribute [-instance]
  TypeBQ3PrincipalPairBlockChoice.IntermediateBlockData.fintypeGlobalBlock
  TypeBQ3PrincipalPairBlockChoice.IntermediateBlockData.fintypeLocalBlock
  SporadicFi24P3Definition44NamedCarrierOriginalAmbient.OriginalSpathAmbient.groupA
  SporadicFi24P3Definition44NamedCarrierOriginalAmbient.OriginalSpathAmbient.fintypeA
  SporadicFi24P3Definition44NamedCarrierOriginalAmbient.OriginalSpathAmbient.baseNormal in
/-- The same pointwise graph has the actual matched-pair extension data. -/
theorem exists_pointwise_extensionTail
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (Msys : ModularSystem 2 K O k) :
  letI : Finite X := finite_X matrixSource
  ∀ (rootX : PrimeRegularRootEmbedding 2 k K X)
    (SX : CoverWeightSource (k := k) (K := K) X)
    (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val),
  letI : Fintype (LiteralPrimitiveBlock k X) := SX.operations.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k (G (ZMod 3))) :=
    S.operations.ambientBlockData.fintypeBlock
  ∀ (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX)
    (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
    (primitive : CentralPrimeToPrimitiveImageSource (k := k)
      (q matrixSource freeSource) (q_surjective matrixSource freeSource) rootX.prime
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))
    (weightSource : FLZ23Source
      (q matrixSource freeSource) (q_surjective matrixSource freeSource)
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
      SX literalX S literal rootX bX hbX b hb
      (TypeBQ3PrincipalBrauerInflation.principal_image
        (q matrixSource freeSource) (q_surjective matrixSource freeSource)
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
        rootX (omegaDecomposition (ZMod 3) S literal) bX hbX b hb primitive))
    (seed : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b ≃
      OmegaWeight (ZMod 3) S b)
    (seedSO : ∀ (h : H (ZMod 3))
        (theta : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b),
      seed (brauerStep (ZMod 3) S literal (rootDown matrixSource freeSource rootX)
        b hb h theta) = weightStep (ZMod 3) S literal b hb h (seed theta))
    (phiX : BrauerFibre rootX bX)
    (wX : CoverWeight SX bX)
    (graph : ClassInflates (q matrixSource freeSource) wX.val
      (seed (brauerDeflation matrixSource freeSource rootX SX literalX S literal
        bX hbX b hb primitive phiX)).val),
    let r := rootDown matrixSource freeSource rootX
    let phiDown := brauerDeflation matrixSource freeSource rootX SX literalX S literal
      bX hbX b hb primitive phiX
    ∃ U : CharacterWeight 2 K X,
    ∃ V : CharacterWeight 2 K G3,
    ∃ support : S.operations.rawWeightBlock V = b,
    ∃ hQ : U.subgroup.map (q matrixSource freeSource) = V.subgroup,
      TypeBQ3PrincipalWeightInflation.classOf U = wX.val ∧
      TypeBQ3PrincipalWeightInflation.classOf V = (seed phiDown).val ∧
      (∀ n : Subgroup.normalizer (U.subgroup : Set X),
        U.localCharacter (QuotientGroup.mk n) =
          V.localCharacter (QuotientGroup.mk
            (normalizerImage (q matrixSource freeSource) hQ n))) ∧
      (∃ e : TypeBQ3PrincipalExtensionCentralQuotient.CentralQuotient rootX bX phiX ≃* G3,
        (∀ x : X, e (QuotientGroup.mk'
          (TypeBQ3PrincipalExtensionCentralQuotient.centralSubgroup rootX bX phiX) x) =
            q matrixSource freeSource x) ∧
        (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer rootX bX phiX).val =
          PrimeRegularClassFunction.pullback e.toMonoidHom phiDown.val.val) ∧
      ∀ (ambientBlocks : PhysicalBlocks k (ActualAutAmbient r phiDown.val))
        (localBlocks : PhysicalBlocks k
          (embeddedNormalizer (innerEmbedding r phiDown.val) V.subgroup))
        (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
        (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
        (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
        (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k)
        (S414 : letI := localBlocks.blockFintype
          Navarro414IntervalCentralCharacterSource
            (TypeBQ3PrincipalPairBaseInduction.embeddedRadicalInterval r phiDown.val V)
            localBlocks.decomposition localBlocks.catalogue),
        ∃ packet : MatchedExtensionData r phiDown.val V
            (weightSource.lowerReduction V support)
            (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource),
          (∀ x : PrimeRegularElement (G := X) 2,
            packet.globalExtension.val.val
              (PrimeRegularElement.map
                ((innerEmbedding r phiDown.val).comp (q matrixSource freeSource)) x) =
                  phiX.val.val x) ∧
          (∀ n : PrimeRegularElement (G := Subgroup.normalizer (U.subgroup : Set X)) 2,
            packet.localExtension.val.val
              (PrimeRegularElement.map
                (inflatedLocalMap (q matrixSource freeSource) r phiDown.val U V hQ) n) =
                  U.localCharacter (QuotientGroup.mk n.val)) := by
  letI : Finite X := finite_X matrixSource
  intro rootX SX literalX S literal
  letI : Fintype (LiteralPrimitiveBlock k X) := SX.operations.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k G3) := S.operations.ambientBlockData.fintypeBlock
  intro bX hbX b hb primitive weightSource seed seedSO phiX wX graph
  let r := rootDown matrixSource freeSource rootX
  let phiDown := brauerDeflation matrixSource freeSource rootX SX literalX S literal
    bX hbX b hb primitive phiX
  refine Exists.elim graph ?_
  intro U upper
  refine Exists.elim upper ?_
  intro V raw
  have upperClass := raw.1
  have lowerClass := raw.2.1
  refine Exists.elim raw.2.2 ?_
  intro hQ values
  have support : S.operations.rawWeightBlock V = b :=
    TypeBQ3PrincipalMatchedPairInvariance.matched_rawWeightBlock S r b seed phiDown V lowerClass
  refine ⟨U, V, support, hQ, upperClass, lowerClass, values, ?_, ?_⟩
  · refine ⟨TypeBQ3PrincipalExtensionCentralQuotient.centralQuotientEquiv
        matrixSource freeSource rootX bX phiX (coverDecomposition SX literalX) hbX,
      ?_, ?_⟩
    · exact TypeBQ3PrincipalExtensionCentralQuotient.centralQuotientEquiv_mk
        matrixSource freeSource rootX bX phiX (coverDecomposition SX literalX) hbX
    · exact TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer_eq_pullback_deflation
        matrixSource freeSource rootX bX phiX (coverDecomposition SX literalX) hbX
        (omegaDecomposition (ZMod 3) S literal) b hb primitive
  · intro ambientBlocks localBlocks principle fieldSource S9295 S96 S414
    have packets := exists_matched_extensions_all_intermediate
      matrixSource automorphisms indexTwo S literal r b hb seed seedSO phiDown V lowerClass
      (weightSource.lowerReduction V support) (weightSource.lowerCompatibility V support)
      ambientBlocks localBlocks principle
      (TypeBModularGroupRootBinding.groupRoot Msys (ActualAutAmbient r phiDown.val))
      fieldSource S9295 S96 S414
    refine Nonempty.elim packets ?_
    intro packet
    refine ⟨packet, ?_, ?_⟩
    · intro x
      have original := TypeBQ3PrincipalBrauerInflation.principalBrauerDeflation_pullback
        (q matrixSource freeSource) (q_surjective matrixSource freeSource)
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
        rootX (coverDecomposition SX literalX) (omegaDecomposition (ZMod 3) S literal)
        bX hbX b hb primitive phiX
      exact (global_value packet (PrimeRegularElement.map (q matrixSource freeSource) x)).trans
        (congrArg (fun f : PrimeRegularClassFunction K X 2 => f x) original)
    · exact local_value_inflated (q matrixSource freeSource) r phiDown.val U V hQ values
        (weightSource.lowerReduction V support)
        (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource) packet

end ModularRep.PaperProofs.TypeBQ3PrincipalExtensionPointwise


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
