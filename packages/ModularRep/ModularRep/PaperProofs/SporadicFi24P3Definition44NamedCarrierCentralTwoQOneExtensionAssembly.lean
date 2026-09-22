import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoQOneAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalQOneExtensionRows

/-! Common Q=1 extensions from every SAME retained global model on the completed family. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoQOneExtensionAssembly

open ModularRep ModularRep.CharacterWeight Formalisation
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

open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)

/-- Retain every completed witness and derive common extensions from each retained Q=1 model. -/
theorem central_two_manuscript_qOne_extension_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (Dzero : DefectZeroReductionSource iota)
    (Tzero : TrivialWeightSource (p := p) (X := G))
    (nu0 : FaithfulSector (k := k) (X := G))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    letI : Finite T := extension_finite E hC
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (_ : ∀ phi : FaithfulIBr iota inj bs R routine,
      Nonempty (PrimeRegularRootEmbedding p k K (brauerAmbient E iota phi.val)))
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
        CentralTwoCommonOutput iota inj R bs routine E hC e := by
  let : Finite T := extension_finite E hC
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro seed Bzero e0 hblock he0
  obtain ⟨e, hFamily, hIndependent, hFixed, hAD3, hBlocks, hQOne⟩ :=
    SporadicFi24P3Definition44NamedCarrierCentralTwoQOneAssembly.central_two_manuscript_qOne_assembly iota R E hC hOuter hAut hZ compatibility availability Dzero Tzero nu0 principle Bzero e0 hblock he0
  exact ⟨e, hFamily, hIndependent, hFixed, hAD3, hBlocks, hQOne,
    central_two_common_output iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R R.1.operations.ambientBlockData.blocks ⟨⟩ E hC e availability compatibility
      Dzero Tzero hQOne seed⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoQOneExtensionAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
