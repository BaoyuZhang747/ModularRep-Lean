import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterRepresentativeDecomposition
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingleRadicalBlockCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DefectZeroCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualComplementCancellation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization
import ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate

/-! The prime-three manuscript cancellation on the specified carriers.
An--Dietrich supplies only the unblocked correspondence. Six ordinary
Brauer rows and four local ordinary rows determine the nonprincipal
signature; the defect-zero sources determine the other known fibre.
The block-preserving map and its original Q=1 normalization are outputs. -/

noncomputable section
set_option maxHeartbeats 4000000
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ReferenceCorrespondence

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource DefectZeroWeightSubgroupSource)
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
open SporadicFi24P3Definition44NamedCarrierP3DefectZeroCounts
open SporadicFi24P3Definition44NamedCarrierActualComplementCancellation
open SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization
open SporadicFi24P3AnDietrichSourceCertificate
open SporadicFi24P3V3RawRankCertificate
open SporadicFi24P3PlusRankReplayContract
open TypeBCentralKernelNormalizerInertia (localAut)

universe u
variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction] [MulAction SourceAction SourceBrauer] [MulAction SourceAction SourceWeight]
variable {k K G : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding 3 k K G)
variable (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
variable (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
variable (AD : AnDietrichFi24P3SourceCertificate
  (SourceAction := SourceAction) (SourceBrauer := SourceBrauer) (SourceWeight := SourceWeight))
variable (Bridge : AnDietrichFi24P3LiteralCarrierBridge
  (SourceAction := SourceAction) (SourceBrauer := SourceBrauer) (SourceWeight := SourceWeight) iota)
variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2) (tau : MulAut G)
variable (htau : QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range
  (MulOpposite.op tau) ≠ 1)
variable (fixedNonprincipal : MulOpposite.op tau • roles 1 = roles 1)
variable (fixedDefectZero : MulOpposite.op tau • roles 2 = roles 2)
variable (Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
  ActualOrdinaryDecomposition iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks))
variable (selected : Fin 6 → OrdinaryIrreducibleCharacter.Irr K G)
variable (ordinaryComplete : let _ := R.1.operations.ambientBlockData.fintypeBlock
  ∀ chi, Dordinary.ordinaryBlock chi = roles 1 ↔ ∃ r, selected r = chi)
variable (representatives : PrimeRegularRepresentativeCover 3 G (Fin 30))
variable (encoding : PrimitiveTwentyNineEncoding K) (V3 : CanonicalSupplementV3Binding encoding)
variable (ordinaryValues : ∀ r c,
  (selected r).1 (representatives.representative c).1 = V3.restrictionRows r c)
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
variable (Dzero : DefectZeroReductionSource iota) (Tzero : TrivialWeightSource (p := 3) (X := G))
variable (Bzero : let _ := R.1.operations.ambientBlockData.fintypeBlock
  DefectZeroOrdinaryBlockSource iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) Dzero)
variable (Zzero : let _ := R.1.operations.ambientBlockData.fintypeBlock
  DefectZeroWeightSubgroupSource iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) (R := R) Dzero)
variable (dz : GlobalDefectZeroCharacter (p := 3) (K := K) (X := G))
variable (hdz : operationsBlock iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (Dzero.reduce (iota := iota) dz) = roles 2)

include AD Bridge hOuter htau fixedNonprincipal fixedDefectZero ordinaryComplete ordinaryValues
  fusion support rowBijective S414 evaluation stable localFixed availability compatibility Bzero Zzero hdz

theorem exists_normalized_correspondence_from_p3_sources :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := G),
      (∀ (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi) ∧
      GlobalQOneOutput iota Omega Dzero Tzero := by
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  have decomposition := two_cosets_of_outer_card_two hOuter tau htau
  have hB1 : Nat.card {phi : IBr iota // operationsBlock iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi = roles 1} = 4 := by
    simpa only [operationsBlock_eq iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks)] using
      actual_b1_card_four iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) Dordinary (roles 1) selected ordinaryComplete
        representatives encoding V3 ordinaryValues
  have hB1fixed : Nat.card {phi : IBr iota // operationsBlock iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi = roles 1 ∧
      MulOpposite.op tau • phi = phi} = 2 := by
    simpa only [operationsBlock_eq iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R (R.1.operations.ambientBlockData.blocks)] using
      actual_b1_fixed_card_two iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) (R.1.operations.ambientBlockData.blocks) Dordinary (roles 1) selected ordinaryComplete
        representatives encoding V3 ordinaryValues tau fixedNonprincipal decomposition fusion
  obtain ⟨hW1, hW1fixed⟩ := weight_signature_of_four_local_rows
    R.1 Q (roles 1) support iota rows rowBijective S414 evaluation tau g stable localFixed
  obtain ⟨hBzero, hWzero, hBzeroFixed, hWzeroFixed⟩ :=
    actual_defectZero_signature iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R availability compatibility Dzero Tzero
      Bzero Zzero dz (roles 2) hdz tau fixedDefectZero
  have hother (b : ActualBlock (k := k) (X := G)) (hne : b ≠ roles 0) :
      Nat.card {phi : IBr iota // operationsBlock iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi = b} =
        Nat.card {w : WeightClass (p := 3) (K := K) (X := G) // R.1.weightBlock w = b} := by
    obtain ⟨j, rfl⟩ := roles.surjective b
    fin_cases j
    · exact (hne rfl).elim
    · exact hB1.trans hW1.symm
    · exact hBzero.trans hWzero.symm
  have hotherFixed (b : ActualBlock (k := k) (X := G)) (hne : b ≠ roles 0) :
      Nat.card {phi : IBr iota // operationsBlock iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi = b ∧
        MulOpposite.op tau • phi = phi} =
        Nat.card {w : WeightClass (p := 3) (K := K) (X := G) //
          R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w} := by
    obtain ⟨j, rfl⟩ := roles.surjective b
    fin_cases j
    · exact (hne rfl).elim
    · exact hB1fixed.trans hW1fixed.symm
    · exact hBzeroFixed.trans hWzeroFixed.symm
  obtain ⟨Omega, hOmega, hblock⟩ := exists_actual_equivariant_of_complement
    iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R tau (AD.literalEquiv iota Bridge)
      (fun phi => AD.literalEquiv_equivariant iota Bridge (MulOpposite.op tau) phi)
      (roles 0) hother hotherFixed decomposition
  exact ⟨Omega, hOmega, hblock,
    global_qOne_of_canonical_blocks iota Omega Dzero Tzero (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R
      (rawReductionOfAvailability iota availability) hblock compatibility Bzero⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ReferenceCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
