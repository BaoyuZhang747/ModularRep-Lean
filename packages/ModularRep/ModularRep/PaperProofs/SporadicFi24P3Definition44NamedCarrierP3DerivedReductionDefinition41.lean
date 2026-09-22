import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DerivedTrivialRadicalDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalGlobalDefectZeroReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DerivedBlockStabilityDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRadicalOfDefectZero
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DerivedPCoreDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierV3BlockStability
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectSupportDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalNormalizerInductionSources
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNontrivialOuterOfV3
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectSupportManuscript
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessDefinition41Data
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
Global reduction existence is derived from canonical local availability.
Only the old regular-restriction injectivity field remains explicit; the
trivial-weight source remains derived from the retained defect-zero block.
Both selected block-stability premises remain internally derived.
The uniform Zzero, non-innerness and finite V3 witness premises remain removed.
The reference map is constructed internally and all retained models and
intermediate block outputs use the same resulting global map. -/

noncomputable section
set_option maxHeartbeats 4000000
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DerivedReductionDefinition41

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
variable (hregular :
  ∀ d d' : GlobalDefectZeroCharacter (p := 3) (K := K) (X := G),
    (∀ g : PrimeRegularElement (G := G) 3, d.val g.val = d'.val g.val) → d = d')
variable (SDefects : RadicalNormalizerInductionSources R)
variable (hDefect : letI := R.1.operations.ambientBlockData.fintypeBlock
  IsMaximalCentralBrauerDefect (p := 3) R.1.operations.ambientBlockData.blocks (roles 2)
    (⊥ : Subgroup G))
variable (dz : GlobalDefectZeroCharacter (p := 3) (K := K) (X := G))

include AD Bridge hOuter ordinaryComplete ordinaryValues
  fusion support rowBijective S414 evaluation stable localFixed availability compatibility SDefects hDefect

theorem p3_definition41_from_derived_reduction
    (hcenter : Subgroup.center G = ⊥)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 3 k)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 3 k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple 3 k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple 3 k K)
    (fieldSource : SpathCoefficientField 3 k iota.prime) :
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let Tzero : TrivialWeightSource (p := 3) (X := G) :=
      SporadicFi24P3Definition44NamedCarrierTrivialRadicalOfDefectZero.trivialWeightSourceOfDefectBot
        R.1.operations.ambientBlockData.blocks (roles 2) hDefect
    let Dzero : DefectZeroReductionSource iota :=
      SporadicFi24P3Definition44NamedCarrierCanonicalGlobalDefectZeroReduction.defectZeroReductionSourceOfAvailability
        iota availability Tzero hregular
    ∀ (_ : DefectZeroOrdinaryBlockSource iota
        (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks Dzero)
      (_ : operationsBlock iota
        (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R
        (Dzero.reduce (iota := iota) dz) = roles 2),
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
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  let Tzero : TrivialWeightSource (p := 3) (X := G) :=
    SporadicFi24P3Definition44NamedCarrierTrivialRadicalOfDefectZero.trivialWeightSourceOfDefectBot
      R.1.operations.ambientBlockData.blocks (roles 2) hDefect
  let Dzero : DefectZeroReductionSource iota :=
    SporadicFi24P3Definition44NamedCarrierCanonicalGlobalDefectZeroReduction.defectZeroReductionSourceOfAvailability
      iota availability Tzero hregular
  dsimp only
  intro Bzero hdz
  exact SporadicFi24P3Definition44NamedCarrierP3DerivedTrivialRadicalDefinition41.p3_definition41_from_derived_trivial_radical
      (iota := iota) (R := R) (roles := roles) (AD := AD) (Bridge := Bridge)
      (hOuter := hOuter) (tau := tau)
      (Dordinary := Dordinary) (selected := selected) (ordinaryComplete := ordinaryComplete)
      (representatives := representatives) (encoding := encoding)
      (ordinaryValues := ordinaryValues) (fusion := fusion)
      (Q := Q) (support := support) (rows := rows) (rowBijective := rowBijective)
      (S414 := S414) (evaluation := evaluation) (g := g) (stable := stable) (localFixed := localFixed)
      (availability := availability) (compatibility := compatibility)
      (Dzero := Dzero) (Bzero := Bzero) (SDefects := SDefects) (hDefect := hDefect) (dz := dz) (hdz := hdz)
      hcenter principle S9295 S9495 S820 fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DerivedReductionDefinition41


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
