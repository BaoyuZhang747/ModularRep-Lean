import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterJointRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntermediateBlockAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSpathPartition

/-! Construct every joint row from the one retained faithful family and quotient pair. -/
noncomputable section
set_option maxHeartbeats 3000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterJointAssembly

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open CentralEllPrimeIBrFibreTransport
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] :
    Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (hprimeTo : ¬ p ∣ Nat.card (Subgroup.center X))

variable {BlockD : Type u} [MulAction (MulAut (X ⧸ (Subgroup.center X)))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ (Subgroup.center X)) (Block := BlockD))
variable (CU : ∀ (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ (Q : RadicalSubgroup (p := p) (G := X ⧸ (Subgroup.center X)))
    (eta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction (quotientRoot iota (Subgroup.center X)) (characterWeightAt iota.prime Q eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota (Subgroup.center X)) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective (Subgroup.center X)) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using (show Subgroup.center X ≤ Subgroup.center X from le_rfl))
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : ∀ Q : RadicalSubgroup (p := p) (G := X),
  CentralPrimeToPrimitiveImageSource (k := k)
    (normalizerMap (QuotientGroup.mk' (Subgroup.center X)) Q.1)
    (fixedNormalizer_surjective iota.prime (Subgroup.center X) (show Subgroup.center X ≤ Subgroup.center X from le_rfl) hprimeTo Q.1 Q.2) iota.prime
    (fixedNormalizer_kernel_central (Subgroup.center X) Q.1 (show Subgroup.center X ≤ Subgroup.center X from le_rfl))
    (fixedNormalizer_kernel_primeTo (Subgroup.center X) Q.1 (show Subgroup.center X ≤ Subgroup.center X from le_rfl) hprimeTo))



open Formalisation
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorJoin
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open EvenFieldFLZ318FixedTheoremGate
local notation "Z" => Subgroup.center X
variable (hprime : (Nat.card (Subgroup.center X)).Prime)
variable (eD : IBr (quotientRoot iota (Subgroup.center X)) ≃
  ConjugacyClass (p := p) (K := K) (G := X ⧸ Subgroup.center X))
local notation "EU" => transportedUp iota R Z le_rfl hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
local notation "BF" => trivialBrauerFibre iota R Z le_rfl

variable (hq : IsUniversalCentralExtension (QuotientGroup.mk' (Subgroup.center X)))
variable (hBlockD : downstairsBlockProperty iota (Subgroup.center X) OD eD)
variable (hD : ∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Subgroup.center X)),
  (∀ x, QuotientGroup.mk' (Subgroup.center X) (alpha x) = beta (QuotientGroup.mk' (Subgroup.center X) x)) →
  ∀ psi : IBr (quotientRoot iota (Subgroup.center X)),
    eD (IrreducibleBrauerCharacter.twist (quotientRoot iota (Subgroup.center X)) psi beta) =
      MulOpposite.op beta • eD psi)


open SporadicFi24P3Definition44NamedCarrierFaithfulJoinedModelBlocks
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
open SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData
open SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauerBlocks
open SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedLocal
open CentralEllPrimeWeightLocalQuotient
open SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel


open SporadicFi24P3Definition44NamedCarrierPrimeCenterJointRows
open SporadicFi24P3Definition44NamedCarrierPrimeCenterPhysicalJoin
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierFaithfulAD3Assembly
open SporadicFi24P3Definition44NamedCarrierFaithfulSpathPartition
open SporadicFi24P3Definition44NamedCarrierPhysicalOriginalBlockRows
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierSamePairQOneValues
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerBlocks
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauer
open SporadicFi24P3Definition44NamedCarrierFaithfulCenterAmbient
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource)

variable (Dzero : DefectZeroReductionSource iota)
variable (Tzero : TrivialWeightSource (p := p) (X := X))

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
theorem joined_pair_of_retained_rows :
    let _ := fixedCentralCardInvertible (k := k) (Subgroup.center X) hprimeTo
    let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
    let inj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    ∀ (eF : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
      (hFamily : FamilyProperties iota inj bs R routine eF),
      FaithfulAD3Output iota inj bs R routine eF hFamily.1 →
      MatchedOriginalModelBlockOutput iota inj R bs routine eF →
      SameMapQOneOutput iota inj R bs routine eF Dzero Tzero →
      centralQuotientBrauerBlocksOutput iota R Z le_rfl hprimeTo OD CU CD compatU compatD
        Sglobal Slocal rfl hq eD hD →
      OrdinaryPartitionOutput iota inj bs R routine eF hFamily.1 ∧
      ∀ phi : IBr iota,
        CentralKernelJointPair iota R hprimeTo CU CD eD hq hD phi
          (physicalJoin iota R hprimeTo OD CU CD compatU compatD Sglobal Slocal hprime eD eF phi) := by
  let _ := fixedCentralCardInvertible (k := k) (Subgroup.center X) hprimeTo
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro eF hFamily hAD3 hOriginal hQOne hReduced
  let inj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let bs := R.1.operations.ambientBlockData.blocks
  let routine : RoutineTransportInput iota inj bs R := ⟨⟩
  let E := physicalJoin iota R hprimeTo OD CU CD compatU compatD Sglobal Slocal hprime eD eF
  obtain ⟨OmegaF, hclassF, hcovF, hfixedF, hrowsF⟩ := hAD3
  refine ⟨partition_output_of_ordinary_output iota inj bs R routine eF hFamily
    ⟨OmegaF, hclassF, hcovF, hfixedF⟩, ?_⟩
  intro phi Q theta hmatch
  by_cases hT : phi ∈ BF
  · let phiT : BF := ⟨phi, hT⟩
    have hE : E phi = (EU phiT).val :=
      joined_trivial iota inj bs R routine hprime EU eF phiT
    let row : SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps.brauerAtRadical
        iota R Z le_rfl EU Q := ⟨phiT, by
      change radicalClass (EU phiT).val = _
      rw [← hE, ← hmatch]
      rfl⟩
    have htheta : theta = (localOrdinaryEquiv iota R Z le_rfl EU Q row).val := by
      apply classAt_injective iota.prime Q
      exact (hmatch.trans hE).trans (localOrdinaryEquiv_class iota R Z le_rfl EU Q row).symm
    refine Or.inl ⟨hT, ?_⟩
    change TrivialJointRow iota R hprimeTo CU CD eD hq hD phiT Q theta
    rw [htheta]
    obtain ⟨hQD, hL, hCU, hm, hPair⟩ := hReduced.2.2.1 Q row
    exact ⟨fullCenter_trivialBrauerFibre_kernel iota R phiT,
      localQuotientOrdinaryEquiv iota R Z le_rfl hprimeTo OD CU CD compatU compatD
        Sglobal Slocal EU Q row, hL, hCU, hm, hPair⟩
  · have hfaithful : Function.Injective (brauerSector iota inj bs phi) :=
      (SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorSplit.injective_iff_ne_one_of_prime_card
        hprime _).mpr hT
    let phiF : FaithfulIBr iota inj bs R routine := ⟨phi, hfaithful⟩
    let nu := faithfulBrauerSector iota inj bs R routine phiF
    have hE : E phi = (eF phiF).val := joined_faithful iota inj bs R routine hprime EU eF phiF
    let row : BrauerAtSectorRadical iota inj bs R routine eF nu Q := ⟨phiF, rfl, by
      change radicalClass (eF phiF).val = _
      rw [← hE, ← hmatch]
      rfl⟩
    have htheta : theta = (OmegaF nu Q row).val := by
      apply classAt_injective iota.prime Q
      exact (hmatch.trans hE).trans (hclassF nu Q row).symm
    apply Or.inr
    change FaithfulJointRow iota R phi Q theta
    rw [htheta]
    obtain ⟨source, hOrdinary, hAction, hLocal, hComparison⟩ := hrowsF nu Q row
    let V := characterWeightAt iota.prime Q (OmegaF nu Q row).val
    refine ⟨nu, rfl, chosen_centralKernel_eq_bot iota (brauerSector iota inj bs phi)
      (scalarBrauer iota inj bs phi) hfaithful, source, hOrdinary, hAction, hLocal, ?_⟩
    apply original_product_blocks_of_comparison iota (brauerSector iota inj bs phi)
      (scalarBrauer iota inj bs phi) V source hComparison
      (hOriginal phiF V (hclassF nu Q row) source)
    intro hV
    exact localBrauer_atOne_of_same_map iota inj R bs routine eF
      (fun Q theta => ⟨CU Q theta⟩) compatU Dzero Tzero hQOne phiF V
      (hclassF nu Q row) hV source

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterJointAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
