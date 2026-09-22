import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
import ModularRep.BrauerCharacterHomPullback
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

/-! Actual ordinary local bijections for a correspondence in the specified
trivial sector. Their targets retain the support condition at the original radical. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedLocal

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


variable (eD : IBr (quotientRoot iota Z) ≃
  ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
local notation "eU" => transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
local notation "L" => localOrdinaryEquiv iota R Z hcentral eU
local notation "LD" => localQuotientOrdinaryEquiv iota R Z hcentral hprimeTo
  OD CU CD compatU compatD Sglobal Slocal eU
variable (Q : RadicalSubgroup (p := p) (G := X))
variable (phi : brauerAtRadical iota R Z hcentral
  (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD) Q)
local notation "Qbar" => fixedRadicalImage iota Z hcentral hprimeTo Q
local notation "W" => characterWeightAt iota.prime Q (Subtype.val (L Q phi))
local notation "Wbar" => characterWeightAt iota.prime Qbar (LD Q phi)
local notation "sourceU" => CU Q (Subtype.val (L Q phi))
local notation "sourceD" => CD Qbar (LD Q phi)
local notation "fN" => normalizerMap (QuotientGroup.mk' Z) Q.val

theorem transported_localBrauer_pullback :
    (sourceU).localBrauer.val = PrimeRegularClassFunction.pullback fN (sourceD).localBrauer.val := by
  exact localBrauer_pullback iota Z Q (Qbar).property
    (L Q phi).val (LD Q phi) sourceU sourceD
    (funext (localQuotientOrdinaryEquiv_factorisation iota R Z hcentral hprimeTo
      OD CU CD compatU compatD Sglobal Slocal eU Q phi))

theorem transported_localRepresentation_affords
    {T : Type u} [AddCommGroup T] [Module k T] [FiniteDimensional k T]
    (rhoD : Representation k (Subgroup.normalizer ((Qbar).val : Set (X ⧸ Z))) T)
    (haffordsD : (sourceD).localBrauer.val =
      Representation.brauerCharacterOfRootEmbedding rhoD (sourceD).normalizerRoot) :
    (sourceU).localBrauer.val =
      Representation.brauerCharacterOfRootEmbedding (rhoD.pullback fN) (sourceU).normalizerRoot := by
  have hroots := fixedZ_sourceNormalizerRoot_compatible iota Z W Wbar
    sourceU sourceD fN
    (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.val Q.property) rhoD
  exact (transported_localBrauer_pullback iota R Z hcentral hprimeTo
    OD CU CD compatU compatD Sglobal Slocal eD Q phi).trans
      ((congrArg (PrimeRegularClassFunction.pullback fN) haffordsD).trans
        (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
          rhoD (sourceD).normalizerRoot (sourceU).normalizerRoot fN hroots).symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedLocal


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
