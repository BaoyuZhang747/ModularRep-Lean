import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectEvaluation

/-! The full prime-three manuscript conclusion with the four local interval
evaluations derived from actual normalizer block defects and the uniform First
Main upper witness. All previous result text and specified objects are retained. -/

noncomputable section
set_option maxHeartbeats 4000000
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectDefinition41

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
open SporadicFi24P3Definition44NamedCarrierOuterRepresentativeDecomposition
open SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature
open SporadicFi24P3Definition44NamedCarrierSingleRadicalBlockCounts
open SporadicFi24P3Definition44NamedCarrierSelectedDefectZeroCounts
open SporadicFi24P3Definition44NamedCarrierActualComplementCancellation
open SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization
open SporadicFi24P3AnDietrichSourceCertificate
open SporadicFi24P3V3RawRankCertificate
open SporadicFi24P3PlusRankReplayContract
open TypeBCentralKernelNormalizerInertia (localAut)

open scoped MonoidAlgebra
open ModularRep ModularRep.CharacterWeight Formalisation
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierCenterlessEmbeddedBlockRows
open TypeBCentralKernelNormalizerInertia (localAut)
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryTransport
open CyclicOuterLemma37Concrete
open TypeBCentralKernelWeightTransport (localMk)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
open SporadicFi24P3Definition44NamedCarrierCenterlessNormalizerAction
open SporadicFi24P3Definition44NamedCarrierCenterlessOrdinaryAssembly
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
open SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData
open SporadicFi24P3Definition44NamedCarrierCenterlessCentralProduct
open SporadicFi24P3Definition44NamedCarrierCentralProductComparisons
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings
open SporadicFi24P3Definition44NamedCarrierCenterlessAD3Assembly
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierPhysicalQOneExtensionRows
open SporadicFi24P3Definition44NamedCarrierPhysicalQOneBlockRows
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues

open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierCenterlessReferenceMap
open SporadicFi24P3Definition44NamedCarrierCenterlessIntermediateBlockAssembly
open SporadicFi24P3Definition44NamedCarrierP3DefectSupportCorrespondence

open SporadicFi24P3Definition44NamedCarrierP3DefectSupportManuscript
open SporadicFi24P3Definition44NamedCarrierCenterlessOriginalRows
open SporadicFi24P3Definition44NamedCarrierCenterlessDefinition41Data

open SporadicFi24P3Definition44NamedCarrierRawWeightDefectZeroSupport
open SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
open SporadicFi24P3Definition44NamedCarrierNontrivialOuterOfV3

open SporadicFi24P3Definition44NamedCarrierRadicalNormalizerInductionSources

open SporadicFi24P3Definition44NamedCarrierSignedBrauerCenterlessRows
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryBlocks

open SporadicFi24P3Definition44NamedCarrierP3LocalProbeAction

open SporadicFi24P3Definition44NamedCarrierP3IdempotentData
open SporadicFi24P3Definition44NamedCarrierP3IdempotentDefect
open SporadicFi24P3Definition44NamedCarrierP3ClassCentre

open SporadicFi24P3Definition44NamedCarrierP3ProjectorCoefficients
open SporadicFi24P3Definition44NamedCarrierP3LocalDefectEvaluation

universe u
variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction] [MulAction SourceAction SourceBrauer] [MulAction SourceAction SourceWeight]
variable {k K G : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding 3 k K G)
variable (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
variable (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
variable (AD : AnDietrichFi24P3SourceCertificate
  (SourceAction := SourceAction) (SourceBrauer := SourceBrauer) (SourceWeight := SourceWeight))
variable (Bridge : AnDietrichFi24P3LiteralCarrierBridge
  (SourceAction := SourceAction) (SourceBrauer := SourceBrauer) (SourceWeight := SourceWeight) iota)
variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2) (tau : MulAut G)
variable (Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
  ActualOrdinaryDecomposition iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks))
variable (selected : Fin 6 → OrdinaryIrreducibleCharacter.Irr K G)
variable (ordinaryComplete : let _ := R.1.operations.ambientBlockData.fintypeBlock
  ∀ chi, Dordinary.ordinaryBlock chi = roles 1 ↔ ∃ r, selected r = chi)
variable (representatives : PrimeRegularRepresentativeCover 3 G (Fin 30))
variable (encoding : PrimitiveTwentyNineEncoding K)
variable (ordinaryValues : ∀ r c,
  (selected r).1 (representatives.representative c).1 = literalV3Rows encoding r c)
variable (fusion : ∀ c : Fin 30, ∃ x : G, tau (representatives.representative c).1 =
  x * (representatives.representative (regularOuterPermutation c)).1 * x⁻¹)
variable (Q : RadicalSubgroup (p := 3) (G := G))
variable (support : ∀ w : ConjugacyClass (p := 3) (K := K) (G := G),
  R.1.weightBlock w = roles 1 → radicalClass w =
    (Quotient.mk'' Q : RadicalConjugacyClass (p := 3) (G := G)))
variable (rows : Fin 4 → LocalDefectZeroCharacter (K := K) Q)
variable (rowSurjective : Function.Surjective rows)
variable (g : G) (stable : Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1)
variable (probe imageProbe : NormalizerQuotient Q.1) (z : K) (hz : z * z = -1)
variable (probeValues : ∀ r, (rows r).1 probe = (![-1, 1, z, -z] : Fin 4 → K) r)
variable (imageProbeValues : ∀ r, (rows r).1 imageProbe = (![-1, 1, -z, z] : Fin 4 → K) r)
variable (localFusion : ∃ a : NormalizerQuotient Q.1,
  localAut Q.1 (tau * MulAut.conj g) stable probe = a * imageProbe * a⁻¹)
variable (availability : LocalCanonicalAvailability iota)
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (C : FullOrdinaryDegreeTable K G)
variable (allocation : let _ := R.1.operations.ambientBlockData.fintypeBlock
  ∀ r, Dordinary.ordinaryBlock (C.character r) = roles (blockLabels r))
variable (classRepresentatives : Fin 108 → G)
variable (classCover : ∀ x : G, ∃ c a, x = a * classRepresentatives c * a⁻¹)
variable (classCentralizers : ∀ c,
  Nat.card (Subgroup.centralizer ({classRepresentatives c} : Set G)) = centralizerOrders c)
variable (selectedForwardValues : ∀ c : Fin 108,
  (C.character 93).val (classRepresentatives c) = (inverseCharacterValues c : K))
variable (selectedInverseValues : ∀ c : Fin 108,
  (C.character 93).val ((classRepresentatives c)⁻¹) = (inverseCharacterValues c : K))
variable (scalarDescent : let _ := R.1.operations.ambientBlockData.fintypeBlock
  IntegralScalarDescent R.1.operations.ambientBlockData.blocks
    R.1.operations.ambientBlockData.catalogue Dordinary.ordinaryBlock)

variable (hQcard : Nat.card Q.1 = 9)
variable (localDefectExponent : InflatedNormalizerBlock (k := k) Q.1 → ℕ)
variable (localDefectOrder : let D := R.1.operations.inflatedNormalizerBlockData Q.1
  letI := D.fintypeBlock
  ∀ b Dsub, navarro417LocalHasDefect (p := 3) D.blocks b Dsub →
    Nat.card Dsub = 3 ^ localDefectExponent b)
variable (localRowDefects : ∀ r, localDefectExponent
  (R.1.operations.inflateToNormalizer Q.1
    (R.1.operations.localCharacterBlock Q.1 (rows r).1 (rows r).2)) = 2)
variable (localExistence : let D := R.1.operations.inflatedNormalizerBlockData Q.1
  letI := D.fintypeBlock
  Navarro417LocalDefectExistenceSource Q.1 D.blocks)
variable (localUpper : let D := R.1.operations.inflatedNormalizerBlockData Q.1
  letI := R.1.operations.ambientBlockData.fintypeBlock
  letI := D.fintypeBlock
  Navarro417FirstParagraphUpperDefectSource Q.1 Q.2.isPGroup
    D.blocks R.1.operations.ambientBlockData.blocks
    D.catalogue (derivedInterval R Q) R.1.operations.ambientBlockData.catalogue)

include AD Bridge hOuter ordinaryComplete ordinaryValues
  fusion support rowSurjective stable hz probeValues imageProbeValues localFusion
  availability compatibility C allocation classCover classCentralizers
  selectedForwardValues selectedInverseValues scalarDescent
  hQcard localDefectOrder localRowDefects localExistence localUpper

theorem p3_definition41_from_local_defect :
    let blockCoefficients : letI := R.1.operations.ambientBlockData.fintypeBlock
  ∀ c, (R.1.operations.ambientBlockData.blockIdempotent (roles 2)).coeff (classRepresentatives c) =
    (inverseCharacterValues c : k) / (7031383654400 : k) := by
      let := R.1.operations.ambientBlockData.fintypeBlock
      exact block_coefficients_of_selected_values R.1.operations.ambientBlockData.blocks
        R.1.operations.ambientBlockData.catalogue Dordinary.ordinaryBlock roles C allocation
        classRepresentatives classCover classCentralizers
        selectedForwardValues selectedInverseValues scalarDescent
    let hcenter : Subgroup.center G = ⊥ :=
      center_eq_bot_of_full_centralizer_table classRepresentatives classCover
        classCentralizers C.groupOrder
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let hDefect : IsMaximalCentralBrauerDefect (p := 3)
        R.1.operations.ambientBlockData.blocks (roles 2) (⊥ : Subgroup G) :=
      defect_bot_of_full_coefficient_table R.1.operations.ambientBlockData.blocks (roles 2)
        classRepresentatives classCover classCentralizers blockCoefficients
    let Tzero : TrivialWeightSource (p := 3) (X := G) :=
      SporadicFi24P3Definition44NamedCarrierTrivialRadicalOfDefectZero.trivialWeightSourceOfDefectBot
        R.1.operations.ambientBlockData.blocks (roles 2) hDefect
    let Dzero : DefectZeroReductionSource iota :=
      SporadicFi24P3Definition44NamedCarrierCanonicalGlobalDefectZeroReduction.defectZeroReductionSourceOfAvailability
        iota availability Tzero (regularRestriction_injective C)
    letI : Invertible (Fintype.card (Subgroup.center G) : k) :=
      centerlessCardInvertible hcenter
    let routine : RoutineTransportInput iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R := ⟨⟩
    let nu0 := centerlessReferenceSector (k := k) hcenter
    ∀ (_ : ∀ phi : FaithfulIBr iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine,
      letI : Fintype (ActualAutAmbient iota phi.val) := Fintype.ofFinite _
      actualBase iota phi.val ≠ ⊤ → UnselectedCatalogue (k := k) («A» := ActualAutAmbient iota phi.val))
      (_ : ∀ phi : FaithfulIBr iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine,
      Nonempty (PrimeRegularRootEmbedding 3 k K (ActualAutAmbient iota phi.val)))
      (_ : CenterlessPositiveLocalInputs iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks) routine),
      ∃ (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := G))
        (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi),
        (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi) ∧
        GlobalQOneOutput iota Omega Dzero Tzero ∧
        let e0 := centerlessReferenceEquiv iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine hcenter nu0 Omega
        ∃ (e : FaithfulIBr iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine ≃ FaithfulWeight iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine)
          (hFamily : FamilyProperties iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine e),
          (∀ phi : FaithfulIBr iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine, (e phi).val = Omega phi.val) ∧
          (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
            (ht : ∀ nu, t nu • nu0 = nu),
            e = transportedEquivalence iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine nu0 t ht e0) ∧
          StableMatchedOrdinaryFixed iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine e ∧
          CenterlessAD3Output iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine hcenter e hFamily.1 ∧
          MatchedBlockOutput iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks) routine e ∧
          SameMapQOneOutput iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks) routine e Dzero Tzero ∧
          CenterlessCommonOutput iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks) routine hcenter e ∧
          CenterlessCommonBlockOutput iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks) routine hcenter ∧
          CenterlessPositiveBlockOutput iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks) routine hcenter e ∧
          CenterlessDefinition41Data iota
            (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
            R hcenter Omega hOmega Dzero Tzero := by
  let blockCoefficients : letI := R.1.operations.ambientBlockData.fintypeBlock
  ∀ c, (R.1.operations.ambientBlockData.blockIdempotent (roles 2)).coeff (classRepresentatives c) =
    (inverseCharacterValues c : k) / (7031383654400 : k) := by
      let := R.1.operations.ambientBlockData.fintypeBlock
      exact block_coefficients_of_selected_values R.1.operations.ambientBlockData.blocks
        R.1.operations.ambientBlockData.catalogue Dordinary.ordinaryBlock roles C allocation
        classRepresentatives classCover classCentralizers
        selectedForwardValues selectedInverseValues scalarDescent
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  have hZero : IsMaximalCentralBrauerDefect (p := 3)
      R.1.operations.ambientBlockData.blocks (roles 2) (⊥ : Subgroup G) :=
    defect_bot_of_full_coefficient_table R.1.operations.ambientBlockData.blocks (roles 2)
      classRepresentatives classCover classCentralizers blockCoefficients
  have evaluation : ∀ r : Fin 4,
  intervalEvaluation R.1.operations Q
    (R.1.operations.inflateToNormalizer Q.1
      (R.1.operations.localCharacterBlock Q.1 (rows r).1 (rows r).2)) (roles 1) = 1 := by
    intro r
    exact local_evaluation_from_defect_order iota R roles Dordinary C allocation hZero
      Q hQcard localDefectExponent localDefectOrder localExistence localUpper
      (rows r) (localRowDefects r)
  exact SporadicFi24P3Definition44NamedCarrierP3ProjectorDefinition41.p3_definition41_from_ordinary_projector
    (iota := iota) (R := R) (roles := roles) (AD := AD) (Bridge := Bridge)
    (hOuter := hOuter) (tau := tau) (Dordinary := Dordinary)
    (selected := selected) (ordinaryComplete := ordinaryComplete)
    (representatives := representatives) (encoding := encoding) (ordinaryValues := ordinaryValues)
    (fusion := fusion) (Q := Q) (support := support) (rows := rows) (rowSurjective := rowSurjective)
    (evaluation := evaluation) (g := g) (stable := stable)
    (probe := probe) (imageProbe := imageProbe) (z := z) (hz := hz)
    (probeValues := probeValues) (imageProbeValues := imageProbeValues) (localFusion := localFusion)
    (availability := availability) (compatibility := compatibility)
    (C := C) (allocation := allocation)
    (classRepresentatives := classRepresentatives) (classCover := classCover)
    (classCentralizers := classCentralizers)
    (selectedForwardValues := selectedForwardValues) (selectedInverseValues := selectedInverseValues)
    (scalarDescent := scalarDescent)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectDefinition41


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
