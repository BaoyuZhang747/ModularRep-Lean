import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoQOneBlockAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEmbeddedBlockRows

/-! Retain the common Q=1 pair and append every positive-radical
intermediate block law on the same specified family and model carriers. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoIntermediateBlockAssembly

open ModularRep ModularRep.CharacterWeight Formalisation
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierCentralTwoEmbeddedBlockRows
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

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "A" => (MulAut G)ᵐᵒᵖ
local notation "S" => FaithfulSector (k := k) (X := G)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "pX" => faithfulBrauerSector iota hinj blocks R E1
local notation "pY" => faithfulWeightSector iota hinj blocks R E1

local notation "hpX" => brauerProjection_equivariant iota hinj blocks R E1
local notation "hpY" => weightProjection_equivariant iota hinj blocks R E1

open CyclicOuterLemma37Concrete
open TypeBCentralKernelWeightTransport (localMk)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
open SporadicFi24P3Definition44NamedCarrierCentralTwoNormalizerAction

open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

variable {T C : Type u} [Group T] [Group C]
variable (E : GroupExtension G T C)

open SporadicFi24P3Definition44NamedCarrierCentralTwoOrdinaryAssembly
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
open SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData
open SporadicFi24P3Definition44NamedCarrierCenterlessCentralProduct
open SporadicFi24P3Definition44NamedCarrierCentralProductComparisons
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

variable (hC : Nat.card C = 2)
variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
variable (hAut : Function.Surjective E.conjAct)
variable (hZ : Nat.card (Subgroup.center G) = 2)

open SporadicFi24P3Definition44NamedCarrierCentralTwoAD3Assembly
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierPhysicalQOneExtensionRows
open SporadicFi24P3Definition44NamedCarrierPhysicalQOneBlockRows
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues

open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)

/-- Complete the embedded intermediate block deduction over every raw match,
retaining the original family, comparison, and common Q=1 pair. -/
theorem central_two_manuscript_intermediate_block_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (Dzero : DefectZeroReductionSource iota)
    (Tzero : TrivialWeightSource (p := p) (X := G))
    (nu0 : FaithfulSector (k := k) (X := G))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    letI : Finite T := extension_finite E hC
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (_ : ∀ phi : FaithfulIBr iota inj bs R routine,
      letI : Fintype (brauerAmbient E iota phi.val) := Fintype.ofFinite _
      (brauerEmbedding E iota phi.val).range ≠ ⊤ → UnselectedCatalogue (k := k) («A» := brauerAmbient E iota phi.val))
      (_ : ∀ phi : FaithfulIBr iota inj bs R routine,
      Nonempty (PrimeRegularRootEmbedding p k K (brauerAmbient E iota phi.val)))
      (_ : CentralTwoPositiveLocalInputs iota inj R bs routine E hC)
      (_ : DefectZeroOrdinaryBlockSource iota inj bs Dzero)
      (e0 : Fibre bP nu0 ≃ Fibre wP nu0),
      BaseBlockPreserving iota inj R bs routine nu0 e0 →
      (∀ (a : (MulAut G)ᵐᵒᵖ) (ha : a • nu0 = nu0) (x : Fibre bP nu0),
        e0 (stabilizerFibreEquiv bP
          (brauerProjection_equivariant iota inj bs R routine) nu0 a ha x) =
          stabilizerFibreEquiv wP
            (weightProjection_equivariant iota inj bs R routine) nu0 a ha (e0 x)) →
      ∃ (e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
        (hFamily : FamilyProperties iota inj bs R routine e),
        (∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        StableMatchedOrdinaryFixed iota inj bs R routine e ∧
        CentralTwoAD3Output iota inj bs R routine E hC hOuter hAut hZ e hFamily.1 ∧
        MatchedBlockOutput iota inj R bs routine e ∧
        SameMapQOneOutput iota inj R bs routine e Dzero Tzero ∧
        CentralTwoCommonOutput iota inj R bs routine E hC e ∧
        CentralTwoCommonBlockOutput iota inj R bs routine E hC ∧
        CentralTwoPositiveBlockOutput iota inj R bs routine E hC e := by
  let : Finite T := extension_finite E hC
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro ambient seed localInputs Bzero e0 hblock he0
  obtain ⟨e, hFamily, hIndependent, hFixed, hAD3, hBlocks, hQOne, hCommon, hCommonBlocks⟩ :=
    SporadicFi24P3Definition44NamedCarrierCentralTwoQOneBlockAssembly.central_two_manuscript_qOne_intermediate_assembly iota R E hC hOuter hAut hZ compatibility availability Dzero Tzero nu0 principle ambient seed Bzero e0 hblock he0
  exact ⟨e, hFamily, hIndependent, hFixed, hAD3, hBlocks, hQOne, hCommon, hCommonBlocks,
    central_two_positive_block_output iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R R.1.operations.ambientBlockData.blocks ⟨⟩ E hC e hBlocks
      S9295 S9495 S820 fieldSource ambient seed localInputs⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoIntermediateBlockAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
