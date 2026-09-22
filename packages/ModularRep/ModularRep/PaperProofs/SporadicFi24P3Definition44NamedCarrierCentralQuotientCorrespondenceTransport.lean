import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientPartition
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRadicalLabels
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction

/-! Ordinary local consequences of the retained quotient correspondence. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceTransport

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRadicalLabels
open SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction


open SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalBlocks
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks
open SporadicFi24P3Definition44NamedCarrierCentralQuotientPartition

open CentralEllPrimeWeightLocalQuotient
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel

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
local notation "RC" => RadicalConjugacyClass (p := p) (G := X)

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


variable (eD : IBr (quotientRoot iota Z) ≃
  ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
variable (hBlockD : downstairsBlockProperty iota Z OD eD)
variable (hEquivD : ∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Z)),
  (∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) →
  ∀ psi : IBr (quotientRoot iota Z),
    eD (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) =
      MulOpposite.op beta • eD psi)

local notation "eU" =>
  transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
local notation "EB" => canonicalBrauerEquiv iota R Z hcentral
local notation "EW" => sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
local notation "ER" => quotientRadicalEquiv iota Z hcentral hprimeTo
local notation "L" => localOrdinaryEquiv iota R Z hcentral eU
local notation "LD" => localQuotientOrdinaryEquiv iota R Z hcentral hprimeTo
  OD CU CD compatU compatD Sglobal Slocal eU
local notation "P" => part iota R Z hcentral eU

/- The actual correspondence, all-radical partition and ordinary local maps
obtained from this one quotient correspondence. Invertibility is derived internally. -/
omit [Invertible (Fintype.card Z : k)] in
def correspondenceTransportOutput : Prop :=
  let _ := fixedCentralCardInvertible (k := k) Z hprimeTo
  (∀ phi : BF,
    PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) ((EB).symm phi).val = phi.val.val ∧
    EW (eU phi) = eD ((EB).symm phi) ∧
    brauerBlockOf iota R phi.val = R.1.weightBlock (eU phi).val) ∧
  ((⋃ c, P c) = Set.univ) ∧
  Pairwise (fun c d => Disjoint (P c) (P d)) ∧
  (∀ c d : RC, P c = P d ↔ c = d ∨ (P c = ∅ ∧ P d = ∅)) ∧
  (∀ Q : RadicalSubgroup (p := p) (G := X),
    (P (Quotient.mk'' Q)).Nonempty ↔ Nonempty (localOrdinaryRows iota R Z Q)) ∧
  (∀ (c : RC) (phi : BF),
    phi ∈ P c ↔ (EB).symm phi ∈ quotientPart iota Z eD (ER c)) ∧
  (∀ (Q : RadicalSubgroup (p := p) (G := X))
      (phi : brauerAtRadical iota R Z hcentral eU Q),
    classAt iota.prime Q (L Q phi).val = (eU phi.val).val ∧
    classAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) (LD Q phi) =
      eD ((EB).symm phi.val) ∧
    (∀ x : NormalizerQuotient Q.val, (L Q phi).val.val x = (LD Q phi).val (qW Z Q.val x)) ∧
    R.1.operations.rawWeightBlock (characterWeightAt iota.prime Q (L Q phi).val) =
      brauerBlockOf iota R phi.val.val ∧
    (let W := characterWeightAt iota.prime Q (L Q phi).val
     let O := R.1.operations
     let D := O.inflatedNormalizerBlockData W.subgroup
     let := O.ambientBlockData.fintypeBlock
     let := D.fintypeBlock
     BlockInducesTo (Subgroup.normalizer (W.subgroup : Set X))
       D.catalogue O.ambientBlockData.catalogue
       (O.inflateToNormalizer W.subgroup
         (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
       (brauerBlockOf iota R phi.val.val) ∧
     ∀ source : CanonicalRawReduction iota W,
       BlockInducesTo (Subgroup.normalizer (W.subgroup : Set X))
         D.catalogue O.ambientBlockData.catalogue
         (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
           O W.subgroup source.normalizerRoot source.localBrauer)
         (brauerBlockOf iota R phi.val.val))) ∧
  (∀ (Q : RadicalSubgroup (p := p) (G := X))
      (b : ActualBlock (k := k) (X := X))
      (hb : IsCentralCharacterSector Z b.val (1 : Z →* kˣ)),
    let LB := localBlockOrdinaryEquiv iota R Z hcentral hprimeTo OD CU CD compatU compatD
      Sglobal Slocal eD hBlockD Q b hb
    Function.Bijective LB ∧ ∀ phi, (LB phi).val = (L Q phi.val).val) ∧
  (∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
      (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)),
    (∀ phi : BF, eU (brauerSectorTwist iota R Z hcentral alpha beta square phi) =
      sectorTwist R Z hcentral alpha beta square (eU phi)) ∧
    (∀ c : RC, (brauerSectorTwist iota R Z hcentral alpha beta square) '' P c =
      P (MulOpposite.op alpha • c)) ∧
    (∀ (Q : RadicalSubgroup (p := p) (G := X))
        (phi : brauerAtRadical iota R Z hcentral eU Q),
      (L (Q.rightTwist alpha)
        (brauerTransport iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
          eD alpha beta square (hEquivD alpha beta square) Q phi)).val =
      SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localCharacterTwist
        iota.prime Q (MulOpposite.op alpha) (L Q phi).val))

omit [Invertible (Fintype.card Z : k)] in
theorem central_quotient_correspondence_transport_deduction :
    correspondenceTransportOutput iota R Z hcentral hprimeTo OD CU CD compatU compatD
      Sglobal Slocal eD hBlockD hEquivD := by
  let _ := fixedCentralCardInvertible (k := k) Z hprimeTo
  refine ⟨?_, part_cover iota R Z hcentral eU,
    part_pairwise_disjoint iota R Z hcentral eU,
    part_eq_iff iota R Z hcentral eU,
    part_support_iff iota R Z hcentral eU,
    part_quotient_iff iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD,
    ?_, ?_, ?_⟩
  · intro phi
    exact ⟨canonicalBrauerEquiv_symm_pullback iota R Z hcentral phi,
      transportedUp_square iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD phi,
      transportedUp_block iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD hBlockD phi⟩
  · intro Q phi
    exact ⟨localOrdinaryEquiv_class iota R Z hcentral eU Q phi,
      transported_local_quotient_class iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD Q phi,
      localQuotientOrdinaryEquiv_factorisation iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eU Q phi,
      localOrdinary_rawBlock iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD hBlockD Q phi,
      localOrdinary_blockInducesTo iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD hBlockD Q phi⟩
  · intro Q b hb
    exact ⟨(localBlockOrdinaryEquiv iota R Z hcentral hprimeTo OD CU CD compatU compatD
      Sglobal Slocal eD hBlockD Q b hb).bijective,
      localBlockOrdinaryEquiv_val iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD hBlockD Q b hb⟩
  · intro alpha beta square
    exact ⟨transportedUp_covariance iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD alpha beta square (hEquivD alpha beta square),
      part_covariance iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD alpha beta square (hEquivD alpha beta square),
      localOrdinaryEquiv_covariance iota R Z hcentral hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD alpha beta square (hEquivD alpha beta square)⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
