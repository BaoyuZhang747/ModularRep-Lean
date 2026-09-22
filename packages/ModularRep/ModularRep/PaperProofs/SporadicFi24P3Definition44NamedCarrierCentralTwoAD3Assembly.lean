import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoOrdinaryAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoNormalizerAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessCentralProduct
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralProductComparisons

/-! Full AD(3) on the SAME ordinary family, enriched without new witnesses. -/


noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoAD3Assembly

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

def CentralTwoProductMatchedPair
    (e : FB ≃ FW) (he : ∀ (a : A) (x : FB), e (a • x) = a • e x)
    (phi : FB) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) =
      (e phi).val) (source : CanonicalRawReduction iota V) : Prop :=
  CentralTwoProductComparison iota (brauerSector iota hinj blocks phi.val)
    (scalarBrauer iota hinj blocks phi.val) E hC hOuter hAut hZ V source
    (scalarOmega iota hinj blocks R E1 _ phi.faithful e)
    (scalarOmega_equivariant iota hinj blocks R E1 _ phi.faithful e he)
    (hmatch.trans (scalarOmega_at_original iota hinj blocks R E1 e phi).symm)

def CentralTwoAD3Output
    (e : FB ≃ FW) (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi) : Prop :=
  letI : Finite T := extension_finite E hC
  ∃ (Omega : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q)
    (hclass : ∀ nu Q phi, classAt iota.prime Q (Omega nu Q phi).val = (e phi.val).val),
    (∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) (a : A)
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q),
      (Omega (a • nu) (Q.rightTwist a.unop)
        (brauerTransport iota hinj blocks R E1 e he nu Q a phi)).val =
        SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localCharacterTwist
          iota.prime Q a (Omega nu Q phi).val) ∧
    (∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q)
      (alpha : MulAut G) (stable : Q.val.comap alpha.toMonoidHom = Q.val),
      MulOpposite.op alpha • phi.val.val = phi.val.val ↔
        OrdinaryIrreducibleCharacter.twist K _ (Omega nu Q phi).val.val
          (localAut Q.val alpha stable) = (Omega nu Q phi).val.val) ∧
    ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
      (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q),
      let V := characterWeightAt iota.prime Q (Omega nu Q phi).val
      ∃ source : CanonicalRawReduction iota V,
        OrdinaryRowData iota nu.val (brauerSector iota hinj blocks phi.val.val) V ∧
        CentralTwoActionOutput iota E phi.val.val V ∧
        LocalOrdinaryRealization iota V source (normalizerBaseEquiv (brauerEmbedding E iota phi.val.val)
            (brauerEmbedding_injective E iota phi.val.val) V.subgroup) ∧
        CentralTwoProductMatchedPair iota hinj blocks R E1 E hC hOuter hAut hZ e he phi.val V (hclass nu Q phi) source

theorem central_two_ad3_output_of_ordinary
    (e : FB ≃ FW) (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi)
    (hOld : CentralTwoOrdinaryOutput iota hinj blocks R E1 E hC hOuter hAut hZ e he) :
    CentralTwoAD3Output iota hinj blocks R E1 E hC hOuter hAut hZ e he := by
  let : Finite T := extension_finite E hC
  rcases hOld with ⟨Omega, hclass, hcovariance, hfixed, hrows⟩
  refine ⟨Omega, hclass, hcovariance, hfixed, ?_⟩
  intro nu Q phi
  obtain ⟨source, hAction, hComparison⟩ := hrows nu Q phi
  let V := characterWeightAt iota.prime Q (Omega nu Q phi).val
  refine ⟨source,
    ordinary_row_data iota nu.val (brauerSector iota hinj blocks phi.val.val)
      nu.property (congrArg Subtype.val phi.property.1) Q (Omega nu Q phi), hAction,
    local_ordinary_realization iota V source (normalizerBaseEquiv (brauerEmbedding E iota phi.val.val)
            (brauerEmbedding_injective E iota phi.val.val) V.subgroup), ?_⟩
  apply central_two_product_comparison
  · exact phi.val.faithful
  · exact hComparison

/-- Full AD(3a-d), derived for every row of the same ordinary family. -/
theorem central_two_manuscript_ad3_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (nu0 : FaithfulSector (k := k) (X := G))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (e0 : Fibre bP nu0 ≃ Fibre wP nu0),
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
        CentralTwoAD3Output iota inj bs R routine E hC hOuter hAut hZ e hFamily.1 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro e0 he0
  obtain ⟨e, hFamily, hIndependent, hFixed, hOld⟩ :=
    SporadicFi24P3Definition44NamedCarrierCentralTwoOrdinaryAssembly.central_two_manuscript_ordinary_assembly iota R E hC hOuter hAut hZ compatibility availability nu0 principle e0 he0
  exact ⟨e, hFamily, hIndependent, hFixed,
    central_two_ad3_output_of_ordinary iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks R ⟨⟩ E hC hOuter hAut hZ e hFamily.1 hOld⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoAD3Assembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
