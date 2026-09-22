import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRadicalLabels
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction

/-! Ordinary local consequences of the retained quotient correspondence. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalBlocks

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

open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks

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
variable (hD : downstairsBlockProperty iota Z OD eD)
include hD

local notation "eU" =>
  transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD

theorem localOrdinary_rawBlock
    (Q : RadicalSubgroup (p := p) (G := X))
    (phi : brauerAtRadical iota R Z hcentral eU Q) :
    R.1.operations.rawWeightBlock
        (characterWeightAt iota.prime Q
          (localOrdinaryEquiv iota R Z hcentral eU Q phi).val) =
      brauerBlockOf iota R phi.val.val := by
  exact
    (congrArg R.1.weightBlock
      (localOrdinaryEquiv_class iota R Z hcentral eU Q phi)).trans
    (transportedUp_block iota R Z hcentral hprimeTo
      OD CU CD compatU compatD Sglobal Slocal eD hD phi.val).symm

theorem localOrdinary_blockInducesTo
    (Q : RadicalSubgroup (p := p) (G := X))
    (phi : brauerAtRadical iota R Z hcentral eU Q) :
    let W := characterWeightAt iota.prime Q
      (localOrdinaryEquiv iota R Z hcentral eU Q phi).val
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
        (brauerBlockOf iota R phi.val.val) := by
  let W := characterWeightAt iota.prime Q
    (localOrdinaryEquiv iota R Z hcentral eU Q phi).val
  let O := R.1.operations
  let D := O.inflatedNormalizerBlockData W.subgroup
  let := O.ambientBlockData.fintypeBlock
  let := D.fintypeBlock
  have hraw : O.rawWeightBlock W = brauerBlockOf iota R phi.val.val :=
    localOrdinary_rawBlock iota R Z hcentral hprimeTo
      OD CU CD compatU compatD Sglobal Slocal eD hD Q phi
  have hind := inducedBlock_spec
    (Subgroup.normalizer (W.subgroup : Set X))
    D.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
    (O.blockInductionDefined W)
  change BlockInducesTo _ _ _ _ (O.rawWeightBlock W) at hind
  rw [hraw] at hind
  refine ⟨hind, ?_⟩
  intro source
  rw [compatU.normalizerBrauerBlock_eq_inflateToNormalizer W source]
  exact hind

def localBlockOrdinaryEquiv
    (Q : RadicalSubgroup (p := p) (G := X))
    (b : ActualBlock (k := k) (X := X))
    (hb : IsCentralCharacterSector Z b.val (1 : Z →* kˣ)) :
    {phi : brauerAtRadical iota R Z hcentral eU Q //
      brauerBlockOf iota R phi.val.val = b} ≃
      RepresentativeDZ iota.prime R.1 Q b := by
  have hsupport {theta : LocalDefectZeroCharacter (K := K) Q}
      (h : R.1.operations.rawWeightBlock
        (characterWeightAt iota.prime Q theta) = b) :
      theta ∈ localOrdinaryRows iota R Z Q := by
    change IsCentralCharacterSector Z
      (R.1.operations.ambientBlockData.blockIdempotent
        (R.1.operations.rawWeightBlock
          (characterWeightAt iota.prime Q theta))) (1 : Z →* kˣ)
    rw [h, R.2]
    exact hb
  let restricted :
      {phi : brauerAtRadical iota R Z hcentral eU Q //
        brauerBlockOf iota R phi.val.val = b} ≃
      {theta : localOrdinaryRows iota R Z Q //
        R.1.operations.rawWeightBlock
          (characterWeightAt iota.prime Q theta.val) = b} :=
    (localOrdinaryEquiv iota R Z hcentral eU Q).subtypeEquiv
      (fun phi => by
        rw [localOrdinary_rawBlock iota R Z hcentral hprimeTo
          OD CU CD compatU compatD Sglobal Slocal eD hD Q phi])
  let flatten :
      {theta : localOrdinaryRows iota R Z Q //
        R.1.operations.rawWeightBlock
          (characterWeightAt iota.prime Q theta.val) = b} ≃
      RepresentativeDZ iota.prime R.1 Q b :=
    Equiv.subtypeSubtypeEquivSubtype hsupport
  exact restricted.trans flatten

theorem localBlockOrdinaryEquiv_val
    (Q : RadicalSubgroup (p := p) (G := X))
    (b : ActualBlock (k := k) (X := X))
    (hb : IsCentralCharacterSector Z b.val (1 : Z →* kˣ))
    (phi : {phi : brauerAtRadical iota R Z hcentral eU Q //
      brauerBlockOf iota R phi.val.val = b}) :
    (localBlockOrdinaryEquiv iota R Z hcentral hprimeTo OD CU CD compatU compatD
      Sglobal Slocal eD hD Q b hb phi).val =
      (localOrdinaryEquiv iota R Z hcentral eU Q phi.val).val := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
