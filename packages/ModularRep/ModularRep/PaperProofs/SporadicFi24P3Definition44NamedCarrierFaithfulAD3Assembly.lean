import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessCentralProduct
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralProductComparisons

/-! Full AD(3) on the SAME ordinary family, enriched without new witnesses. -/


noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulAD3Assembly

open ModularRep ModularRep.CharacterWeight Formalisation
open TypeBCentralKernelNormalizerInertia (localAut rightTwist_eq_iff_local_fixed)
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
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
open SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings
open SporadicFi24P3Definition44NamedCarrierOriginalPairComparison
open SporadicFi24P3Definition44NamedCarrierFaithfulFamilyComparison

open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryAssembly
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
open SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData
open SporadicFi24P3Definition44NamedCarrierCenterlessCentralProduct
open SporadicFi24P3Definition44NamedCarrierCentralProductComparisons
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2) (tau : MulAut G)
variable (hcard : Nat.card (Subgroup.center G) = 3 ∨
  Nat.card (Subgroup.center G) = 4 ∨ Nat.card (Subgroup.center G) = 6)
variable (hinverts : ∀ z : Subgroup.center G, tau z.val = z.val⁻¹)

def PhysicalProductComparison (phi : IBr iota) (V : CharacterWeight p K G)
    (source : CanonicalRawReduction iota V) : Prop :=
  OriginalProductComparison iota (brauerSector iota hinj blocks phi)
    (scalarBrauer iota hinj blocks phi) V source


def FaithfulAD3Output
    (e : FB ≃ FW) (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi) : Prop :=
  ∃ (Omega : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q)
    (_hclass : ∀ nu Q phi, classAt iota.prime Q (Omega nu Q phi).val = (e phi.val).val),
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
        FaithfulActionOutput iota phi.val.val V ∧
        LocalOrdinaryRealization iota V source ((Subgroup.topEquiv.symm : Subgroup.normalizer (V.subgroup : Set G) ≃*
            ↥(⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G))))) ∧
        PhysicalProductComparison iota hinj blocks phi.val.val V source

theorem faithful_ad3_output_of_ordinary
    (e : FB ≃ FW) (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi)
    (hOld : FaithfulOrdinaryOutput iota hinj blocks R E1 e he) :
    FaithfulAD3Output iota hinj blocks R E1 e he := by
  rcases hOld with ⟨Omega, hclass, hcovariance, hfixed, hrows⟩
  refine ⟨Omega, hclass, hcovariance, hfixed, ?_⟩
  intro nu Q phi
  obtain ⟨source, hAction, hComparison⟩ := hrows nu Q phi
  let V := characterWeightAt iota.prime Q (Omega nu Q phi).val
  refine ⟨source,
    ordinary_row_data iota nu.val (brauerSector iota hinj blocks phi.val.val)
      nu.property (congrArg Subtype.val phi.property.1) Q (Omega nu Q phi), hAction,
    local_ordinary_realization iota V source ((Subgroup.topEquiv.symm : Subgroup.normalizer (V.subgroup : Set G) ≃*
            ↥(⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G))))), ?_⟩
  apply original_product_comparison
  · exact phi.val.faithful
  · exact hComparison

include hOuter tau hcard hinverts in
/-- Full AD(3a-d), derived for every row of the same ordinary family. -/
theorem faithful_manuscript_ad3_assembly
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (availability : LocalCanonicalAvailability iota)
    (nu0 : FaithfulSector (k := k) (X := G)) :
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
        FaithfulAD3Output iota inj bs R routine e hFamily.1 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro e0 he0
  obtain ⟨e, hFamily, hIndependent, hFixed, hOld⟩ :=
    SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryAssembly.faithful_manuscript_ordinary_assembly iota R hOuter tau hcard hinverts compatibility availability nu0 e0 he0
  exact ⟨e, hFamily, hIndependent, hFixed,
    faithful_ad3_output_of_ordinary iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks R ⟨⟩ e hFamily.1 hOld⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulAD3Assembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
