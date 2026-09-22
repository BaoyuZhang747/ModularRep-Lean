import ModularRep.PaperProofs.TypeBQ3PrincipalLocalApplication
import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionPointwise
import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionRetainedConjunction

/-!
# The principal extension tail for the same actual triple-cover matching

The accepted principal correspondence is used once. Its existing inflation
graph supplies an actual raw pair. Their global and local extensions satisfy
every intermediate block equality, with values traced back to the original
principal character and the same upstairs ordinary weight. The final ambient
stabilizer and prescribed-representative identifications remain separate.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalExtensionTail

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding
open TypeBQ3TripleCoverCarrier
open TypeBQ3PrincipalWeightInflation
open TypeBQ3PrincipalTripleCoverApplication
open TypeBQ3PrincipalRadicalDecoding
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
/-- The same correspondence has the actual matched-pair extension tail. -/
theorem exists_principalTripleCover_extensionTail
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource) :
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
  [HasEnoughRootsOfUnity K (Nat.card (H (ZMod 3)))]
  (delta : H (ZMod 3)) (indexTwo : (G (ZMod 3)).index = 2)
  (outside : delta ∉ G (ZMod 3))
  (SH : SOWeightSource (k := k) (K := K) (ZMod 3))
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (bH : LiteralPrimitiveBlock k (H (ZMod 3))) (hbH : IsPrincipal bH)
  [Fintype (OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b)]
  [DecidableEq (OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b)]
  [Fintype (OmegaWeight (ZMod 3) S b)]
  [DecidableEq (OmegaWeight (ZMod 3) S b)]
  [Fintype (SOWeight (ZMod 3) SH bH)]
  [DecidableEq (SOWeight (ZMod 3) SH bH)]
  (Msys : ModularSystem 2 K O k)
  (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G (ZMod 3)) Msys)
  (brauerSource : TypeBQ3PrincipalBrauerBinding.LiteralSource
    S literal (rootDown matrixSource freeSource rootX) b hb delta indexTwo outside)
  (covering : TypeBQ3PrincipalWeightBinding.PublishedWeightCovering
    S literal b hb delta indexTwo outside SH literalH bH hbH Msys dgn),
    ∃ seed : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b ≃
        OmegaWeight (ZMod 3) S b,
    ∃ lifted : BrauerFibre rootX bX ≃ CoverWeight SX bX,
      (∀ (h : H (ZMod 3))
          (theta : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b),
        seed (brauerStep (ZMod 3) S literal (rootDown matrixSource freeSource rootX)
          b hb h theta) = weightStep (ZMod 3) S literal b hb h (seed theta)) ∧
      (∀ phi : BrauerFibre rootX bX,
        principalWeightEquiv weightSource (lifted phi) =
          seed (brauerDeflation matrixSource freeSource rootX SX literalX S literal
            bX hbX b hb primitive phi)) ∧
      (∀ phi : BrauerFibre rootX bX,
        ClassInflates (q matrixSource freeSource) (lifted phi).val
          (seed (brauerDeflation matrixSource freeSource rootX SX literalX S literal
            bX hbX b hb primitive phi)).val) ∧
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : BrauerFibre rootX bX),
        lifted (TypeBQ3PrincipalBrauerInflation.principalStep rootX
          (coverDecomposition SX literalX) bX hbX alpha phi) =
        coverWeightStep SX literalX bX hbX alpha (lifted phi)) ∧
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : BrauerFibre rootX bX),
        part lifted (TypeBQ3PrincipalBrauerInflation.principalStep rootX
          (coverDecomposition SX literalX) bX hbX alpha phi) =
          alpha • part lifted phi) ∧
      (∃ partition : BrauerFibre rootX bX ≃
          Σ c : RadicalConjugacyClass (p := 2) (G := X),
            {phi : BrauerFibre rootX bX // part lifted phi = c},
        (∀ phi, (partition phi).1 = part lifted phi) ∧
        (∀ phi, (partition phi).2.val = phi)) ∧
      (∃ localEquiv : ∀ Q : RadicalSubgroup (p := 2) (G := X),
          BrauerAtRadical lifted Q ≃ RepresentativeDZ Nat.prime_two SX Q bX,
        (∀ (Q : RadicalSubgroup (p := 2) (G := X))
            (phi : BrauerAtRadical lifted Q),
          (Quotient.mk'' (Quotient.mk''
            (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val)) :
              CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := X)) =
            (lifted phi.val).val) ∧
        (∀ (alpha : (MulAut X)ᵐᵒᵖ)
            (Q : RadicalSubgroup (p := 2) (G := X))
            (phi : BrauerAtRadical lifted Q)
            (psi : BrauerAtRadical lifted (Q.rightTwist alpha.unop)),
          psi.val = TypeBQ3PrincipalBrauerInflation.principalStep rootX
            (coverDecomposition SX literalX) bX hbX alpha phi.val →
          (localEquiv (Q.rightTwist alpha.unop) psi).val =
            localCharacterTwist Q alpha (localEquiv Q phi).val ∧
          CharacterWeight.Isomorphic
            ((characterWeightAt Nat.prime_two Q (localEquiv Q phi).val).rightTwist
              alpha.unop)
            (characterWeightAt Nat.prime_two (Q.rightTwist alpha.unop)
              (localEquiv (Q.rightTwist alpha.unop) psi).val))) ∧
      (∀ phiX : BrauerFibre rootX bX,
        let r := rootDown matrixSource freeSource rootX
        let phiDown := brauerDeflation matrixSource freeSource rootX SX literalX S literal
          bX hbX b hb primitive phiX
        ∃ U : CharacterWeight 2 K X,
        ∃ V : CharacterWeight 2 K G3,
        ∃ support : S.operations.rawWeightBlock V = b,
        ∃ hQ : U.subgroup.map (q matrixSource freeSource) = V.subgroup,
          TypeBQ3PrincipalWeightInflation.classOf U = (lifted phiX).val ∧
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
                      U.localCharacter (QuotientGroup.mk n.val))) := by
  letI : Finite X := finite_X matrixSource
  intro rootX SX literalX S literal
  letI : Fintype (LiteralPrimitiveBlock k X) := SX.operations.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k G3) := S.operations.ambientBlockData.fintypeBlock
  intro bX hbX b hb primitive weightSource ordinaryRootsH delta indexTwo outside
    SH literalH bH hbH fintypeBrauer decidableBrauer fintypeOmegaWeight decidableOmegaWeight
    fintypeSOWeight decidableSOWeight Msys dgn brauerSource covering
  have previous :=
    @TypeBQ3PrincipalLocalApplication.exists_principalTripleCover_radicalLocalData
      matrixSource freeSource k K O
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      automorphisms rootX SX literalX S literal bX hbX b hb primitive weightSource
      ordinaryRootsH delta indexTwo outside SH literalH bH hbH
      fintypeBrauer decidableBrauer fintypeOmegaWeight decidableOmegaWeight
      fintypeSOWeight decidableSOWeight Msys dgn brauerSource covering
  refine TypeBQ3PrincipalExtensionRetainedConjunction.append previous ?_
  intro seed lifted seedSO graph
  intro phiX
  exact TypeBQ3PrincipalExtensionPointwise.exists_pointwise_extensionTail
    matrixSource freeSource automorphisms indexTwo Msys rootX SX literalX S literal
    bX hbX b hb primitive weightSource seed seedSO phiX (lifted phiX) (graph phiX)

end ModularRep.PaperProofs.TypeBQ3PrincipalExtensionTail


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
