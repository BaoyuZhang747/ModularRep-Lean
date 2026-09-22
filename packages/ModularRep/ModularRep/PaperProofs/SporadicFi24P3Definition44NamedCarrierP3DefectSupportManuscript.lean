import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNontrivialOuterOfV3
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessReferenceMap
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessIntermediateBlockAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectSupportCorrespondence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterRepresentativeDecomposition
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingleRadicalBlockCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelectedDefectZeroCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualComplementCancellation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization
import ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate

/-! The complete centreless manuscript deduction from the prime-three
ordinary rows, local sources and published unblocked correspondence.
The uniform Zzero, non-innerness and finite V3 witness premises are removed.
The reference map is constructed internally and all retained models and
intermediate block outputs use the same resulting global map. -/

noncomputable section
set_option maxHeartbeats 4000000
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectSupportManuscript

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

open SporadicFi24P3Definition44NamedCarrierRawWeightDefectZeroSupport
open SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
open SporadicFi24P3Definition44NamedCarrierNontrivialOuterOfV3

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
variable (fixedNonprincipal : MulOpposite.op tau • roles 1 = roles 1)
variable (fixedDefectZero : MulOpposite.op tau • roles 2 = roles 2)
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
variable (rowBijective : Function.Bijective rows)
variable (S414 : NormalizerIntervalSource R.1.operations Q)
variable (evaluation : ∀ r : Fin 4,
  intervalEvaluation R.1.operations Q
    (R.1.operations.inflateToNormalizer Q.1
      (R.1.operations.localCharacterBlock Q.1 (rows r).1 (rows r).2)) (roles 1) = 1)
variable (g : G) (stable : Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1)
variable (localFixed : Nat.card {theta : LocalDefectZeroCharacter (K := K) Q //
  OrdinaryIrreducibleCharacter.twist K _ theta.1
    (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1} = 2)
variable (availability : LocalCanonicalAvailability iota)
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (Dzero : DefectZeroReductionSource iota) (Tzero : TrivialWeightSource (p := 3) (X := G))
variable (Bzero : let _ := R.1.operations.ambientBlockData.fintypeBlock
  DefectZeroOrdinaryBlockSource iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) Dzero)
variable (SDefects : RadicalNormalizerDefectSources R)
variable (hDefect : letI := R.1.operations.ambientBlockData.fintypeBlock
  IsMaximalCentralBrauerDefect (p := 3) R.1.operations.ambientBlockData.blocks (roles 2)
    (⊥ : Subgroup G))
variable (dz : GlobalDefectZeroCharacter (p := 3) (K := K) (X := G))
variable (hdz : operationsBlock iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (Dzero.reduce (iota := iota) dz) = roles 2)

include AD Bridge hOuter fixedNonprincipal fixedDefectZero ordinaryComplete ordinaryValues
  fusion support rowBijective S414 evaluation stable localFixed availability compatibility Bzero SDefects hDefect hdz

theorem p3_manuscript_from_defect_support
    (hcenter : Subgroup.center G = ⊥)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 3 k)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 3 k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple 3 k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple 3 k K)
    (fieldSource : SpathCoefficientField 3 k iota.prime) :
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
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
      ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := G),
        (∀ (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
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
          CenterlessPositiveBlockOutput iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks) routine hcenter e := by
  let _ : Fintype (ActualBlock (k := k) (X := G)) := R.1.operations.ambientBlockData.fintypeBlock
  let _ : Invertible (Fintype.card (Subgroup.center G) : k) := centerlessCardInvertible hcenter
  dsimp only
  intro ambient seed localInputs
  obtain ⟨Omega, hOmega, hblock, hOne⟩ :=
    exists_normalized_correspondence_from_defect_support
      (iota := iota) (R := R) (roles := roles) (AD := AD) (Bridge := Bridge)
      (hOuter := hOuter) (tau := tau)
      (fixedNonprincipal := fixedNonprincipal) (fixedDefectZero := fixedDefectZero)
      (Dordinary := Dordinary) (selected := selected) (ordinaryComplete := ordinaryComplete)
      (representatives := representatives) (encoding := encoding)
      (ordinaryValues := ordinaryValues) (fusion := fusion)
      (Q := Q) (support := support) (rows := rows) (rowBijective := rowBijective)
      (S414 := S414) (evaluation := evaluation) (g := g) (stable := stable) (localFixed := localFixed)
      (availability := availability) (compatibility := compatibility)
      (Dzero := Dzero) (Tzero := Tzero) (Bzero := Bzero) (SDefects := SDefects) (hDefect := hDefect) (dz := dz) (hdz := hdz)
  refine ⟨Omega, hOmega, hblock, hOne, ?_⟩
  let routine : RoutineTransportInput iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R := ⟨⟩
  let nu0 := centerlessReferenceSector (k := k) hcenter
  let e0 := centerlessReferenceEquiv iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine hcenter nu0 Omega
  obtain ⟨e, hFamily, hIndependent, hFixed, hAD3, hBlocks, hQOne, hCommon, hCommonBlocks, hPositive⟩ :=
    centerless_manuscript_intermediate_block_assembly iota R compatibility availability
      Dzero Tzero nu0 hcenter hOuter principle S9295 S9495 S820 fieldSource
      ambient seed localInputs Bzero e0
      (centerlessReferenceEquiv_block iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine hcenter nu0 Omega hblock)
      (centerlessReferenceEquiv_equivariant iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine hcenter nu0 Omega hOmega)
  refine ⟨e, hFamily, ?_, hIndependent, hFixed, hAD3, hBlocks, hQOne, hCommon, hCommonBlocks, hPositive⟩
  intro phi
  let t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ := fun _ => 1
  have ht : ∀ nu, t nu • nu0 = nu := by
    intro nu
    change (1 : (MulAut G)ᵐᵒᵖ) • nu0 = nu
    rw [one_smul]
    exact centerlessSector_unique hcenter _ _
  rw [hIndependent t ht]
  exact centerlessTransportedEquiv_val iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) R routine hcenter nu0 Omega hOmega t ht phi

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectSupportManuscript


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
