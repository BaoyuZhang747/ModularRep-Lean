import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionTail
import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionPointwise
import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionSeedCovariance
import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionDominatedBlock

/-! The same principal matching satisfies the criterion on its actual dominated
block, conditional on the specified catalogues and interval sources for one
selected raw pair per principal character. Both extensions are selected once
for that character and reused for all its prescribed radical representatives. -/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionApplication

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding
open TypeBQ3TripleCoverCarrier TypeBQ3PrincipalWeightInflation
open TypeBQ3PrincipalTripleCoverApplication TypeBQ3PrincipalRadicalDecoding
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open TypeBQ3PrincipalExtensionApplication TypeBQ3PrincipalExtensionAnchors
open TypeBQ3PrincipalPairBlockChoice TypeBQ3PrincipalCriterionData
open TypeBQ3PrincipalCriterionDominatedBlock
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open NavarroBrauerRestrictionCovering

universe u v

private theorem appendEight
    {A : Sort u} {B : Sort v}
    {P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ T : A → B → Prop}
    (previous : ∃ a b, P₁ a b ∧ P₂ a b ∧ P₃ a b ∧ P₄ a b ∧
      P₅ a b ∧ P₆ a b ∧ P₇ a b ∧ P₈ a b)
    (step : ∀ a b, P₁ a b → P₈ a b → T a b) :
    ∃ a b, P₁ a b ∧ P₂ a b ∧ P₃ a b ∧ P₄ a b ∧
      P₅ a b ∧ P₆ a b ∧ P₇ a b ∧ P₈ a b ∧ T a b :=
  Exists.elim previous fun a ha =>
    Exists.elim ha fun b h =>
      ⟨a, b, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
        step a b h.1 h.2.2.2.2.2.2.2⟩

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
/-- The retained matching yields the dominated principal criterion after the
specified catalogue and interval sources for its selected pairs are supplied. -/
theorem exists_principalTripleCover_dominatedPrincipalCriterion
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
                      U.localCharacter (QuotientGroup.mk n.val))) ∧
      (centralSector matrixSource freeSource bX = 1) ∧
      (letI := centralOrderInvertible matrixSource freeSource (k := k);
        IsCentralCharacterSector (Subgroup.center X) bX.val 1) ∧
      ((centralSector matrixSource freeSource bX).ker.map (Subgroup.center X).subtype =
        (q matrixSource freeSource).ker) ∧
      (∀ phiX : BrauerFibre rootX bX,
        TypeBQ3PrincipalExtensionCentralQuotient.centralSubgroup rootX bX phiX =
          (q matrixSource freeSource).ker) ∧
      (SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra.algebraMapOf
        (q matrixSource freeSource) bX.val = b.val) ∧
      ∃ selected : (phi : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b) →
          {V : CharacterWeight 2 K G3 // S.operations.rawWeightBlock V = b},
        (∀ phi, TypeBQ3PrincipalWeightInflation.classOf (selected phi).val = (seed phi).val) ∧
        ∀ (ambientBlocks : ∀ phi : OmegaBrauer (ZMod 3)
              (rootDown matrixSource freeSource rootX) b,
            PhysicalBlocks k (ActualAutAmbient (rootDown matrixSource freeSource rootX) phi.val))
          (localBlocks : ∀ phi : OmegaBrauer (ZMod 3)
              (rootDown matrixSource freeSource rootX) b,
            PhysicalBlocks k (embeddedNormalizer
              (innerEmbedding (rootDown matrixSource freeSource rootX) phi.val)
              (selected phi).val.subgroup))
          (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
          (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
          (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
          (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k)
          (S414 : ∀ phi : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b,
            letI := (localBlocks phi).blockFintype
            Navarro414IntervalCentralCharacterSource
              (TypeBQ3PrincipalPairBaseInduction.embeddedRadicalInterval
                (rootDown matrixSource freeSource rootX) phi.val (selected phi).val)
              (localBlocks phi).decomposition (localBlocks phi).catalogue),
          (∀ phi : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b,
            Subgroup.center G3 ⊓
              (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation
                (rootDown matrixSource freeSource rootX) phi.val).ρ.ker = ⊥) ∧
          (∀ (alpha : (MulAut G3)ᵐᵒᵖ)
              (phi : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b),
            seed (TypeBQ3PrincipalBrauerInflation.principalStep
              (rootDown matrixSource freeSource rootX)
              (coverDecomposition S literal) b hb alpha phi) =
                coverWeightStep S literal b hb alpha (seed phi)) ∧
          (∀ (alpha : (MulAut G3)ᵐᵒᵖ)
              (phi : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b),
            part seed (TypeBQ3PrincipalBrauerInflation.principalStep
              (rootDown matrixSource freeSource rootX)
              (coverDecomposition S literal) b hb alpha phi) = alpha • part seed phi) ∧
          (∃ partition : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b ≃
              Σ c : RadicalConjugacyClass (p := 2) (G := G3),
                {phi : OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b //
                  part seed phi = c},
            (∀ phi, (partition phi).1 = part seed phi) ∧
            (∀ phi, (partition phi).2.val = phi)) ∧
          ∃ localEquiv : ∀ Q : RadicalSubgroup (p := 2) (G := G3),
              BrauerAtRadical seed Q ≃ RepresentativeDZ Nat.prime_two S Q b,
            (∀ (Q : RadicalSubgroup (p := 2) (G := G3)) (phi : BrauerAtRadical seed Q),
              TypeBQ3PrincipalWeightInflation.classOf
                (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val) =
                (seed phi.val).val) ∧
            (∀ (alpha : (MulAut G3)ᵐᵒᵖ) (Q : RadicalSubgroup (p := 2) (G := G3))
                (phi : BrauerAtRadical seed Q)
                (psi : BrauerAtRadical seed (Q.rightTwist alpha.unop)),
              psi.val = TypeBQ3PrincipalBrauerInflation.principalStep
                (rootDown matrixSource freeSource rootX)
                (coverDecomposition S literal) b hb alpha phi.val →
              (localEquiv (Q.rightTwist alpha.unop) psi).val =
                localCharacterTwist Q alpha (localEquiv Q phi).val ∧
              CharacterWeight.Isomorphic
                ((characterWeightAt Nat.prime_two Q (localEquiv Q phi).val).rightTwist alpha.unop)
                (characterWeightAt Nat.prime_two (Q.rightTwist alpha.unop)
                  (localEquiv (Q.rightTwist alpha.unop) psi).val)) ∧
            (∀ (Q : RadicalSubgroup (p := 2) (G := G3)) (phi : BrauerAtRadical seed Q),
              Nonempty (PrincipalClauseIII (rootDown matrixSource freeSource rootX) phi.val.val
                (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val))) := by
  letI : Finite X := finite_X matrixSource
  intro rootX SX literalX S literal
  letI : Fintype (LiteralPrimitiveBlock k X) := SX.operations.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k G3) := S.operations.ambientBlockData.fintypeBlock
  intro bX hbX b hb primitive weightSource ordinaryRootsH delta indexTwo outside
    SH literalH bH hbH fintypeBrauer decidableBrauer fintypeOmegaWeight decidableOmegaWeight
    fintypeSOWeight decidableSOWeight Msys dgn brauerSource covering
  classical
  letI : Fintype G3 := TypeBRankThreePrincipalCountBinding.groupFintype G3
  have previous :=
    @TypeBQ3PrincipalExtensionTail.exists_principalTripleCover_extensionTail
      matrixSource freeSource k K O
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      automorphisms rootX SX literalX S literal bX hbX b hb primitive weightSource
      ordinaryRootsH delta indexTwo outside SH literalH bH hbH
      fintypeBrauer decidableBrauer fintypeOmegaWeight decidableOmegaWeight
      fintypeSOWeight decidableSOWeight Msys dgn brauerSource covering
  refine appendEight previous ?_
  intro seed lifted seedSO tail
  refine ⟨principal_centralSector_eq_one matrixSource freeSource bX hbX,
    principal_isTrivialSector matrixSource freeSource bX hbX,
    principal_sectorKernel_eq_qker matrixSource freeSource bX hbX, ?_, ?_, ?_⟩
  · intro phiX
    exact TypeBQ3PrincipalExtensionCentralQuotient.centralKernel_eq_qker
      matrixSource freeSource rootX bX phiX (coverDecomposition SX literalX) hbX
  · exact TypeBQ3PrincipalBrauerInflation.principal_image
      (q matrixSource freeSource) (q_surjective matrixSource freeSource)
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
      rootX (omegaDecomposition (ZMod 3) S literal) bX hbX b hb primitive
  · let r := rootDown matrixSource freeSource rootX
    let deflation := brauerDeflation matrixSource freeSource rootX SX literalX S literal
      bX hbX b hb primitive
    have selectedExists : ∀ phi : OmegaBrauer (ZMod 3) r b,
        ∃ w : {V : CharacterWeight 2 K G3 // S.operations.rawWeightBlock V = b},
          TypeBQ3PrincipalWeightInflation.classOf w.val = (seed phi).val ∧
          ∀ (ambientBlocks : PhysicalBlocks k (ActualAutAmbient r phi.val))
            (localBlocks : PhysicalBlocks k
              (embeddedNormalizer (innerEmbedding r phi.val) w.val.subgroup))
            (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
            (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
            (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
            (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k)
            (S414 : letI := localBlocks.blockFintype
              Navarro414IntervalCentralCharacterSource
                (TypeBQ3PrincipalPairBaseInduction.embeddedRadicalInterval r phi.val w.val)
                localBlocks.decomposition localBlocks.catalogue),
            Nonempty (MatchedExtensionData r phi.val w.val
              (weightSource.lowerReduction w.val w.property)
              (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource)) := by
      refine deflation.forall_congr_right.mp ?_
      intro phiX
      have fromTail := tail phiX
      refine Exists.elim fromTail ?_
      intro U upper
      refine Exists.elim upper ?_
      intro V lower
      refine Exists.elim lower ?_
      intro support supported
      refine Exists.elim supported ?_
      intro hQ raw
      refine ⟨⟨V, support⟩, raw.2.1, ?_⟩
      intro ambientBlocks localBlocks principle fieldSource S9295 S96 S414
      have packetExists := raw.2.2.2.2
        ambientBlocks localBlocks principle fieldSource S9295 S96 S414
      refine Exists.elim packetExists ?_
      intro packet anchors
      exact ⟨packet⟩
    let selected : (phi : OmegaBrauer (ZMod 3) r b) →
        {V : CharacterWeight 2 K G3 // S.operations.rawWeightBlock V = b} :=
      fun phi => Classical.choose (selectedExists phi)
    have selectedClass : ∀ phi : OmegaBrauer (ZMod 3) r b,
        TypeBQ3PrincipalWeightInflation.classOf (selected phi).val = (seed phi).val :=
      fun phi => (Classical.choose_spec (selectedExists phi)).1
    refine ⟨selected, selectedClass, ?_⟩
    intro ambientBlocks localBlocks principle fieldSource S9295 S96 S414
    let packets : ∀ phi : OmegaBrauer (ZMod 3) r b,
        MatchedExtensionData r phi.val (selected phi).val
          (weightSource.lowerReduction (selected phi).val (selected phi).property)
          (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource) :=
      fun phi => Classical.choice
        ((Classical.choose_spec (selectedExists phi)).2
          (ambientBlocks phi) (localBlocks phi) principle fieldSource S9295 S96 (S414 phi))
    have fullAut := TypeBQ3PrincipalCriterionSeedCovariance.seed_equivariant
      S literal r b hb seed seedSO automorphisms
    refine ⟨?_, fullAut, part_equivariant seed literal hb fullAut,
      ⟨partitionEquiv seed, partitionEquiv_part seed, partitionEquiv_character seed⟩,
      (fun Q => localMap seed Q), ?_, ?_, ?_⟩
    · intro phi
      rw [TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource]
      exact bot_inf_eq _
    · exact localMap_class seed
    · intro alpha Q phi psi hpsi
      have same : psi = brauerTransport seed literal hb fullAut alpha Q phi := Subtype.ext hpsi
      subst psi
      exact ⟨localMap_covariance seed literal hb fullAut alpha Q phi,
        localMap_raw_transport seed literal hb fullAut alpha Q phi⟩
    · intro Q phi
      exact TypeBQ3PrincipalCriterionPointwise.exists_for_prescribed
        r phi.val.val (selected phi.val).val
        (weightSource.lowerReduction (selected phi.val).val (selected phi.val).property)
        (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource) (packets phi.val)
        (characterWeightAt Nat.prime_two Q (localMap seed Q phi).val)
        ((selectedClass phi.val).trans (localMap_class seed Q phi).symm)

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
