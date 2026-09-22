import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOriginalRows
import ModularRep.PaperProofs.CoherentCenterlessModelSourceH
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalRadicalFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessModelSourceH
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOwnKernel

/-! The character and weight construction for centreless groups, with compatible roots in every extension and block calculation. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CoherentCenterlessRows

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

open ModularRep.PaperProofs.CoherentCenterlessModelSourceH

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
open SporadicFi24P3Definition44NamedCarrierCenterlessModelSourceH
open SporadicFi24P3Definition44NamedCarrierCenterlessReferenceMap
open SporadicFi24P3Definition44NamedCarrierOriginalRadicalFibre
open SporadicFi24P3Definition44NamedCarrierCenterlessEmbeddedBlockRows
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
open SporadicFi24P3Definition44NamedCarrierPhysicalQOneExtensionRows
open SporadicFi24P3Definition44NamedCarrierPhysicalQOneBlockRows
open SporadicFi24P3Definition44NamedCarrierCentralLift

def CoherentOriginalRowOutput (hcenter : Subgroup.center G = ⊥)
    (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := G))
    (hOmega : ∀ (a : A) (chi : IBr iota), Omega (a • chi) = a • Omega chi)
    (chi : IBr iota) (V : CharacterWeight p K G)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = Omega chi) : Prop :=
  ∃ source : CanonicalRawReduction iota V,
    CenterlessActionOutput iota chi V hcenter ∧
    LocalOrdinaryRealization iota V source
      (normalizerBaseEquiv (innerEmbedding iota chi)
        (innerEmbedding_injective iota chi hcenter) V.subgroup) ∧
    RawBlockOutput iota hinj R chi V ∧
    (∃ thetaHat : OrdinaryIrreducibleCharacter.Irr K (Subgroup.normalizer (V.subgroup : Set G)),
      (∀ n, thetaHat n = V.localCharacter (QuotientGroup.mk n)) ∧
      ∀ (nu : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G)) (z : Subgroup.center G),
        thetaHat ⟨z.val, Subgroup.center_le_normalizer (V.subgroup : Set G) z.property⟩ =
          thetaHat 1 * nu z) ∧
    CoherentCenterlessProductSourceHComparison iota chi hcenter V Omega hOmega hmatch source

def CoherentOriginalRowsOutput (hcenter : Subgroup.center G = ⊥)
    (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := G))
    (hOmega : ∀ (a : A) (chi : IBr iota), Omega (a • chi) = a • Omega chi) : Prop :=
  ∀ (Q : RadicalSubgroup (p := p) (G := G))
    (psi : SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.BrauerAtRadical iota Omega Q),
    CoherentOriginalRowOutput iota hinj R hcenter Omega hOmega psi.val
      (characterWeightAt iota.prime Q
        (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap iota Omega iota.prime Q psi))
      (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap_class iota Omega iota.prime Q psi)

/-- The stronger rows change only the requirements on root choices. -/
theorem CoherentOriginalRowsOutput.forget (hcenter : Subgroup.center G = ⊥)
    (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := G))
    (hOmega : ∀ (a : A) (chi : IBr iota), Omega (a • chi) = a • Omega chi)
    (h : CoherentOriginalRowsOutput iota hinj R hcenter Omega hOmega) :
    SporadicFi24P3Definition44NamedCarrierCenterlessOriginalRows.OriginalRowsOutput
      iota hinj R hcenter Omega hOmega := by
  intro Q psi
  obtain ⟨source, hAction, hLocal, hBlock, hOrdinary, hComparison⟩ := h Q psi
  refine ⟨source, hAction, hLocal, hBlock, hOrdinary, ?_⟩
  exact hComparison.forget iota psi.val hcenter _ Omega hOmega _ source

end ModularRep.PaperProofs.CoherentCenterlessRows

/-
Part of the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
The results use the explicit assumptions described in the formalisation report.
-/
