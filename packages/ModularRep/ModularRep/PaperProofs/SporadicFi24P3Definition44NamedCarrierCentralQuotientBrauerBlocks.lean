import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneNormalization
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAmbient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauerBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauer
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedLocal
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedModels
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
import ModularRep.BrauerCharacterHomPullback
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

/-! Actual ambient Brauer extensions and literal all-H block laws for the
retained central-kernel quotient pair, with common extensions at Q=1. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open CentralEllPrimeIBrFibreTransport CentralEllPrimeWeightLocalQuotient
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorRepresentativeQuotient
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport

open SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierFixedCentralNormalizerRoot

open EvenFieldFLZ318FixedTheoremGate
open EvenFieldFLZBAWGoodFamily
open CentralEllPrimeIBrFibreTransport
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauer
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedLocal
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedModels

open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAmbient
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauerBlocks
open SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (UnselectedCatalogue)
open SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs

open SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneNormalization
open SporadicCompleteCollapseLemma52Actual (GlobalDefectZeroCharacter)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] :
    Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

local notation "BF" => trivialBrauerFibre iota R Z hcentral

variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (CU : ∀ (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ (Q : RadicalSubgroup (p := p) (G := X ⧸ Z))
    (eta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction (quotientRoot iota Z) (characterWeightAt iota.prime Q eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : ∀ Q : RadicalSubgroup (p := p) (G := X),
  CentralPrimeToPrimitiveImageSource (k := k)
    (normalizerMap (QuotientGroup.mk' Z) Q.1)
    (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
    (fixedNormalizer_kernel_central Z Q.1 hcentral)
    (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))


variable (hfull : Z = Subgroup.center X)
variable (hq : IsUniversalCentralExtension (QuotientGroup.mk' Z))
variable (eD : IBr (quotientRoot iota Z) ≃ ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
variable (hD : ∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Z)),
  (∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) →
  ∀ psi : IBr (quotientRoot iota Z),
    eD (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) = MulOpposite.op beta • eD psi)
variable (hOuter : Nat.card (LiteralOuterQuotient (X ⧸ Z)) = 2)
variable (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)

local instance reducedAmbientFintype (psi : IBr (quotientRoot iota Z)) :
    Fintype (ActualAutAmbient (quotientRoot iota Z) psi) := Fintype.ofFinite _

variable (hBlockD : downstairsBlockProperty iota Z OD eD)
variable (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
variable (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
variable (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
variable (fieldSource : SpathCoefficientField p k iota.prime)
variable (singleton : DefectZeroReductionBlockSingleton (quotientRoot iota Z) OD)
variable (seedProper : ∀ psi : IBr (quotientRoot iota Z),
  actualBase (quotientRoot iota Z) psi ≠ ⊤ →
    Nonempty (PrimeRegularRootEmbedding p k K (ActualAutAmbient (quotientRoot iota Z) psi)))
variable (ambient : ∀ psi : IBr (quotientRoot iota Z),
  actualBase (quotientRoot iota Z) psi ≠ ⊤ →
    UnselectedCatalogue (k := k) (A := ActualAutAmbient (quotientRoot iota Z) psi))
variable (localInputs : letI : Fact p.Prime := ⟨iota.prime⟩
  ∀ psi : IBr (quotientRoot iota Z),
    actualBase (quotientRoot iota Z) psi ≠ ⊤ →
      PositiveLocalCatalogueInput (p := p) (k := k)
        (innerEmbedding (quotientRoot iota Z) psi))

local notation "EU" => transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
local notation "EB" => canonicalBrauerEquiv iota R Z hcentral
local notation "L" => localOrdinaryEquiv iota R Z hcentral EU
local notation "LD" => localQuotientOrdinaryEquiv iota R Z hcentral hprimeTo
  OD CU CD compatU compatD Sglobal Slocal EU
local notation "QD" => fixedRadicalImage iota Z hcentral hprimeTo
local notation "HD" => fullDownEquivariance iota Z hfull hq eD hD
local notation "HC" => quotientCenter_eq_bot Z hfull hq

/- The manuscript's central-kernel reduction and actual matched cohomological
comparison on the required quotient, with extensions of the same representations. -/
omit [Invertible (Fintype.card Z : k)] in
def centralQuotientBrauerBlocksOutput : Prop :=
  let _ := fixedCentralCardInvertible (k := k) Z hprimeTo
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  (∀ phi : BF,
    Subgroup.center X ⊓ (chosenIBrRepresentation iota phi.val).ρ.ker = Z ∧
    (EB).symm phi =
      deflateIBr iota (quotientRoot iota Z) R.1.operations.ambientBlockData.blocks
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral phi ∧
    (∀ chi : IBr (quotientRoot iota Z),
      PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) chi.val = phi.val.val →
        chi = (EB).symm phi) ∧
    Function.Bijective (fullCenterBrauerStabilizerEquiv iota R Z hcentral hfull hq phi) ∧
    (∀ a : ActualAutAmbient iota phi.val,
      actualConjugation (quotientRoot iota Z) ((EB).symm phi)
        (fullCenterBrauerStabilizerEquiv iota R Z hcentral hfull hq phi a) =
        fullCenterAutEquiv Z hfull hq (actualConjugation iota phi.val a))) ∧
  (∀ phi : BF,
    (actualBase (quotientRoot iota Z) ((EB).symm phi)).Normal ∧
    Subgroup.centralizer
        (actualBase (quotientRoot iota Z) ((EB).symm phi) :
          Set (ActualAutAmbient (quotientRoot iota Z) ((EB).symm phi))) =
      Subgroup.center (ActualAutAmbient (quotientRoot iota Z) ((EB).symm phi)) ∧
    (¬ p ∣ Nat.card (Subgroup.center (ActualAutAmbient (quotientRoot iota Z) ((EB).symm phi)))) ∧
    Function.Bijective (reducedCentralizerQuotientEquiv iota R Z hcentral hfull hq phi) ∧
    (∀ a : ActualAutAmbient (quotientRoot iota Z) ((EB).symm phi),
      fullCenterAutEquiv Z hfull hq
        (actualConjugation iota phi.val
          (reducedCentralizerQuotientEquiv iota R Z hcentral hfull hq phi
            (QuotientGroup.mk'
              (Subgroup.centralizer
                (actualBase (quotientRoot iota Z) ((EB).symm phi) :
                  Set (ActualAutAmbient (quotientRoot iota Z) ((EB).symm phi)))) a))) =
        actualConjugation (quotientRoot iota Z) ((EB).symm phi) a)) ∧
  (∀ (Q : RadicalSubgroup (p := p) (G := X)) (phi : brauerAtRadical iota R Z hcentral EU Q),
    (QD Q).val = Q.val.map (QuotientGroup.mk' Z) ∧
    (∀ x : NormalizerQuotient Q.val, (L Q phi).val.val x = (LD Q phi).val (qW Z Q.val x)) ∧
    (CU Q (L Q phi).val).localBrauer.val = PrimeRegularClassFunction.pullback
      (normalizerMap (QuotientGroup.mk' Z) Q.val) (CD (QD Q) (LD Q phi)).localBrauer.val ∧
    classAt iota.prime (QD Q) (LD Q phi) = eD ((EB).symm phi.val) ∧
    ReducedPairBrauerBlocksOutput (quotientRoot iota Z) ((EB).symm phi.val)
      (characterWeightAt iota.prime (QD Q) (LD Q phi)) eD HD
      (transported_local_quotient_class iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD Q phi)
      (CD (QD Q) (LD Q phi)) HC) ∧
  (∀ (Q : RadicalSubgroup (p := p) (G := X)), Q.val = ⊥ →
    ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X ⧸ Z),
      ∃! phi : brauerAtRadical iota R Z hcentral EU Q,
        IsBrauerReduction (quotientRoot iota Z) d.val ((EB).symm phi.val) ∧
        ∀ n : Subgroup.normalizer ((QD Q).val : Set (X ⧸ Z)),
          (LD Q phi).val (QuotientGroup.mk n) = d.val n.val)

include hOuter principle hBlockD S9295 S9495 S820 fieldSource singleton seedProper ambient localInputs in
omit [Invertible (Fintype.card Z : k)] in
theorem central_quotient_brauer_blocks_deduction :
    centralQuotientBrauerBlocksOutput iota R Z hcentral hprimeTo OD CU CD compatU compatD
      Sglobal Slocal hfull hq eD hD := by
  let _ := fixedCentralCardInvertible (k := k) Z hprimeTo
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro phi
    refine ⟨?_, canonicalBrauerEquiv_symm_eq_deflate iota R Z hcentral phi,
      canonicalBrauerEquiv_symm_unique iota R Z hcentral phi,
      (fullCenterBrauerStabilizerEquiv iota R Z hcentral hfull hq phi).bijective,
      fullCenterBrauerStabilizerEquiv_action iota R Z hcentral hfull hq phi⟩
    simpa only [hfull] using trivialBrauerFibre_central_kernel iota R Z hcentral phi
  · intro phi
    exact ⟨inferInstance, reduced_centralizer_eq_center iota R Z hcentral hfull hq phi,
      reduced_center_primeTo iota R Z hcentral hfull hq phi,
      (reducedCentralizerQuotientEquiv iota R Z hcentral hfull hq phi).bijective,
      reducedCentralizerQuotientEquiv_action iota R Z hcentral hfull hq phi⟩
  · intro Q phi
    refine ⟨rfl,
      localQuotientOrdinaryEquiv_factorisation iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal EU Q phi,
      transported_localBrauer_pullback iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD Q phi,
      transported_local_quotient_class iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD Q phi, ?_⟩
    exact reduced_pair_brauer_blocks (quotientRoot iota Z) ((EB).symm phi.val)
      (characterWeightAt iota.prime (QD Q) (LD Q phi)) eD HD
      (transported_local_quotient_class iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD Q phi)
      (CD (QD Q) (LD Q phi)) HC OD compatD
      (hBlockD ((EB).symm phi.val) (characterWeightAt iota.prime (QD Q) (LD Q phi))
        (transported_local_quotient_class iota R Z hcentral hprimeTo OD CU CD compatU compatD
          Sglobal Slocal eD Q phi))
      hOuter principle S9295 S9495 S820 fieldSource singleton
      (seedProper ((EB).symm phi.val)) (ambient ((EB).symm phi.val))
      (localInputs ((EB).symm phi.val))
  · intro Q hQ
    exact transported_qOne_all_defectZero iota R Z hcentral hprimeTo OD CU CD compatU compatD
      Sglobal Slocal eD singleton hBlockD Q hQ

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
