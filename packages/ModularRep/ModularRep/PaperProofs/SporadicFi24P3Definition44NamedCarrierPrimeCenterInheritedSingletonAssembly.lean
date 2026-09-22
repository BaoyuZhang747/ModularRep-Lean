import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientDefectZeroSingleton
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterManuscriptAssembly

/-! The same complete centre-three manuscript deduction, deriving quotient defect-zero block uniqueness from the original data. -/
noncomputable section
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterInheritedSingletonAssembly

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
variable (hthree : Nat.card (Subgroup.center X) = 3)
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


open SporadicFi24P3Definition44NamedCarrierPrimeCenterJointAssembly
open SporadicFi24P3Definition44NamedCarrierFullCoverOuterTransport
open SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization
open SporadicFi24P3Definition44NamedCarrierJointSectorAssembly
open SporadicFi24P3Definition44NamedCarrierFaithfulIntermediateBlockAssembly
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
open SporadicFi24P3Definition44NamedCarrierPhysicalQOneExtensionRows
open SporadicFi24P3Definition44NamedCarrierPhysicalQOneBlockRows
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierCentralQuotientQOneReduction
open SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (UnselectedCatalogue)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
variable (hOuter : Nat.card (LiteralOuterQuotient (X ⧸ Subgroup.center X)) = 2)
variable (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
local instance reducedAmbientFintype (psi : IBr (quotientRoot iota (Subgroup.center X))) :
    Fintype (ActualAutAmbient (quotientRoot iota (Subgroup.center X)) psi) := Fintype.ofFinite _
variable (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
variable (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
variable (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
variable (fieldSource : SpathCoefficientField p k iota.prime)
variable (seedProper : ∀ psi : IBr (quotientRoot iota (Subgroup.center X)),
  actualBase (quotientRoot iota (Subgroup.center X)) psi ≠ ⊤ →
    Nonempty (PrimeRegularRootEmbedding p k K (ActualAutAmbient (quotientRoot iota (Subgroup.center X)) psi)))
variable (ambient : ∀ psi : IBr (quotientRoot iota (Subgroup.center X)),
  actualBase (quotientRoot iota (Subgroup.center X)) psi ≠ ⊤ →
    UnselectedCatalogue (k := k) (A := ActualAutAmbient (quotientRoot iota (Subgroup.center X)) psi))
variable (localInputs : letI : Fact p.Prime := ⟨iota.prime⟩
  ∀ psi : IBr (quotientRoot iota (Subgroup.center X)),
    actualBase (quotientRoot iota (Subgroup.center X)) psi ≠ ⊤ →
      PositiveLocalCatalogueInput (p := p) (k := k)
        (innerEmbedding (quotientRoot iota (Subgroup.center X)) psi))


variable (tau : MulAut X)
variable (hinverts : ∀ z : Subgroup.center X, tau z.val = z.val⁻¹)
include hthree hq hOuter principle S9295 S9495 S820 fieldSource seedProper ambient localInputs hBlockD hD tau hinverts in
omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
theorem prime_center_manuscript_of_original_defectZero
    (Dzero : DefectZeroReductionSource iota)
    (Tzero : TrivialWeightSource (p := p) (X := X))
    (nu0 : FaithfulSector (k := k) (X := X)) :
    let _ := fixedCentralCardInvertible (k := k) (Subgroup.center X) hprimeTo
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (_ : DefectZeroOrdinaryBlockSource iota inj bs Dzero)
      (e0 : Fibre bP nu0 ≃ Fibre wP nu0),
      BaseBlockPreserving iota inj R bs routine nu0 e0 →
      (∀ (a : (MulAut X)ᵐᵒᵖ) (ha : a • nu0 = nu0) (x : Fibre bP nu0),
        e0 (stabilizerFibreEquiv bP
          (brauerProjection_equivariant iota inj bs R routine) nu0 a ha x) =
          stabilizerFibreEquiv wP
            (weightProjection_equivariant iota inj bs R routine) nu0 a ha (e0 x)) →
      ∃ (e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine)
        (hFamily : FamilyProperties iota inj bs R routine e),
        (∀ (t : FaithfulSector (k := k) (X := X) → (MulAut X)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0) ∧
        StableMatchedOrdinaryFixed iota inj bs R routine e ∧
        FaithfulAD3Output iota inj bs R routine e hFamily.1 ∧
        MatchedBlockOutput iota inj R bs routine e ∧
        SameMapQOneOutput iota inj R bs routine e Dzero Tzero ∧
        OriginalCommonOutput iota inj R bs routine e ∧
        OriginalCommonBlockOutput iota inj R bs routine ∧
        MatchedOriginalModelBlockOutput iota inj R bs routine e ∧
        OrdinaryPartitionOutput iota inj bs R routine e hFamily.1 ∧
        SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceTransport.correspondenceTransportOutput
          iota R (Subgroup.center X) le_rfl hprimeTo OD CU CD compatU compatD Sglobal Slocal eD hBlockD hD ∧
        centralQuotientBrauerBlocksOutput iota R (Subgroup.center X) le_rfl hprimeTo
          OD CU CD compatU compatD Sglobal Slocal rfl hq eD hD ∧
        let hp : (Nat.card (Subgroup.center X)).Prime := by rw [hthree]; decide
        let E := physicalJoin iota R hprimeTo OD CU CD compatU compatD Sglobal Slocal hp eD e
        (∀ phi : BF, E phi.val = (EU phi).val) ∧
        (∀ phi : FaithfulIBr iota inj bs R routine, E phi.val = (e phi).val) ∧
        ∃ hE : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), E (a • phi) = a • E phi,
          (∀ phi : IBr iota, R.1.weightBlock (E phi) = brauerBlock iota inj bs phi) ∧
          (∀ phi : IBr iota, weightSector (R := R) (E phi) = brauerSector iota inj bs phi) ∧
          Nonempty (IBr iota ≃ Sigma fun q : RadicalConjugacyClass (p := p) (G := X) =>
            {phi : IBr iota // radicalClass (E phi) = q}) ∧
          (∀ Q : RadicalSubgroup (p := p) (G := X),
            Function.Bijective (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap iota E iota.prime Q) ∧
            (∀ phi : SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.BrauerAtRadical iota E Q,
              classAt iota.prime Q
                (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap iota E iota.prime Q phi) = E phi.val) ∧
            ∀ b : ActualBlock (k := k) (X := X), Nonempty
              ({phi : SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.BrauerAtRadical iota E Q //
                  brauerBlock iota inj bs phi.val = b} ≃
                ModularRep.CharacterWeight.RepresentativeDZ iota.prime R.1 Q b)) ∧
          (∀ (a : (MulAut X)ᵐᵒᵖ) (Q : RadicalSubgroup (p := p) (G := X))
            (phi : SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.BrauerAtRadical iota E Q),
            SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap iota E iota.prime (Q.rightTwist a.unop)
              (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.brauerTransport iota E hE a Q phi) =
              SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localCharacterTwist iota.prime Q a
                (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap iota E iota.prime Q phi)) ∧
          GlobalQOneOutput iota E Dzero Tzero ∧
          (∀ phi : IBr iota, CentralKernelJointPair iota R hprimeTo CU CD eD hq hD phi (E phi)) ∧
          (let P := CentralKernelJointPair iota R hprimeTo CU CD eD hq hD
           ∃ AD : AnDietrichSectorInput iota inj bs routine P,
             (∀ phi, AnDietrichSectorInput.assemble iota inj bs routine AD phi = E phi) ∧
             Nonempty (SpathLemma61Input iota inj bs routine P P P AD) ∧
             Nonempty (Fi24AssembledClauses iota inj bs routine P P P AD)) := by
  let _ := fixedCentralCardInvertible (k := k) (Subgroup.center X) hprimeTo
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro Bzero e0 hblock he0
  have singleton :=
    SporadicFi24P3Definition44NamedCarrierQuotientDefectZeroSingleton.quotient_defectZeroReductionBlockSingleton
      iota R (Subgroup.center X) le_rfl hprimeTo OD Dzero Bzero Sglobal
  exact SporadicFi24P3Definition44NamedCarrierPrimeCenterManuscriptAssembly.prime_center_manuscript_deduction
    iota R hprimeTo OD CU CD compatU compatD Sglobal Slocal hthree eD hq hBlockD hD
    hOuter principle S9295 S9495 S820 fieldSource singleton seedProper ambient localInputs
    tau hinverts Dzero Tzero nu0 Bzero e0 hblock he0

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterInheritedSingletonAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
