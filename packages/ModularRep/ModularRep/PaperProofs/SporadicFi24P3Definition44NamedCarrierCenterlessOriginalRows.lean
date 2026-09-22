import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalRadicalFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessModelSourceH
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOwnKernel

/-! Literal original-carrier rows from the same retained local maps and models. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOriginalRows

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

def OriginalRowOutput (hcenter : Subgroup.center G = ⊥)
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
    CenterlessProductSourceHComparison iota chi hcenter V Omega hOmega hmatch source

def OriginalRowsOutput (hcenter : Subgroup.center G = ⊥)
    (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := G))
    (hOmega : ∀ (a : A) (chi : IBr iota), Omega (a • chi) = a • Omega chi) : Prop :=
  ∀ (Q : RadicalSubgroup (p := p) (G := G))
    (psi : SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.BrauerAtRadical iota Omega Q),
    OriginalRowOutput iota hinj R hcenter Omega hOmega psi.val
      (characterWeightAt iota.prime Q
        (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap iota Omega iota.prime Q psi))
      (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap_class iota Omega iota.prime Q psi)

theorem original_rows_of_retained_family (hcenter : Subgroup.center G = ⊥)
    (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := G))
    (hOmega : ∀ (a : A) (chi : IBr iota), Omega (a • chi) = a • Omega chi)
    (e : FB ≃ FW) (he : ∀ (a : A) (phi : FB), e (a • phi) = a • e phi)
    (hlink : ∀ phi : FB, (e phi).val = Omega phi.val)
    (hAD3 : CenterlessAD3Output iota hinj blocks R E1 hcenter e he)
    (hBlocks : MatchedBlockOutput iota hinj R blocks E1 e)
    (hCommon : CenterlessCommonOutput iota hinj R blocks E1 hcenter e)
    (hCommonBlocks : CenterlessCommonBlockOutput iota hinj R blocks E1 hcenter)
    (hPositive : CenterlessPositiveBlockOutput iota hinj R blocks E1 hcenter e) :
    OriginalRowsOutput iota hinj R hcenter Omega hOmega := by
  obtain ⟨L, hclass, hcovariance, hfixed, hrows⟩ := hAD3
  have hco : centerlessOmega iota hinj blocks R E1 hcenter e =
      (Omega : IBr iota → ConjugacyClass (p := p) (K := K) (G := G)) := by
    funext chi
    exact hlink (centerlessLift iota hinj blocks R E1 hcenter chi)
  intro Q psi
  let nu0 := centerlessReferenceSector (k := k) hcenter
  let f := originalRadicalEquiv iota Omega hinj blocks R E1 hcenter e hlink nu0 Q
  let phi := f.symm psi
  have hphi : phi.val.val = psi.val := congrArg Subtype.val (f.apply_symm_apply psi)
  have htheta := original_localMap_eq_retained iota Omega hinj blocks R E1
    hcenter e hlink L hclass nu0 Q phi
  have hf : f phi = psi := f.apply_symm_apply psi
  change SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap iota Omega iota.prime Q
    (f phi) = (L nu0 Q phi).val at htheta
  rw [hf] at htheta
  let V := characterWeightAt iota.prime Q (L nu0 Q phi).val
  obtain ⟨source, hOrd, hAction, hLocal, hGamma, hComparison⟩ := hrows nu0 Q phi
  have hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = Omega phi.val.val :=
    (hclass nu0 Q phi).trans (hlink phi.val)
  have hComparison' : CenterlessProductComparison iota phi.val.val hcenter V
      Omega hOmega hmatch source := by
    simpa only [CenterlessProductMatchedPair, hco] using hComparison
  have hrow : OriginalRowOutput iota hinj R hcenter Omega hOmega phi.val.val V hmatch := by
    refine ⟨source, hAction, hLocal, hBlocks.2 phi.val V (hclass nu0 Q phi),
      exists_ordinary_lift_over_center hcenter V.subgroup V.localCharacter, ?_⟩
    exact centerless_product_sourceH_comparison iota phi.val.val hcenter V Omega hOmega hmatch source
      hComparison' (fun hV => hPositive phi.val V (hclass nu0 Q phi) hV source)
      (fun hV => hCommon phi.val V (hclass nu0 Q phi) source hV)
      (fun hV => hCommonBlocks phi.val V source hV)
  simpa only [V, htheta, hphi] using hrow

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOriginalRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
