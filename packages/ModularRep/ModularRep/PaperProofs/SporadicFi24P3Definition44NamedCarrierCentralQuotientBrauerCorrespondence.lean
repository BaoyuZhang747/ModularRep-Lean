import ModularRep.BrauerCharacterSeparation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport

/-! Transport one retained quotient correspondence using the original root
and its canonical quotient. The original specified block catalogue is retained. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

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
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

def trivialBrauerFibre : Set (IBr iota) := by
  letI : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  exact {phi | blockCentralCharacter iota R.1.operations.ambientBlockData.blocks
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral phi = 1}

local notation "BF" => trivialBrauerFibre iota R Z hcentral

def canonicalBrauerEquiv : IBr (quotientRoot iota Z) ≃ BF := by
  letI : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  exact quotientIBrEquivTrivialCentralCharacterFibre iota (quotientRoot iota Z)
    (canonicalQuotientRealisation iota Z) R.1.operations.ambientBlockData.blocks
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral

theorem canonicalBrauerEquiv_val (psi : IBr (quotientRoot iota Z)) :
    (canonicalBrauerEquiv iota R Z hcentral psi).val.val =
      PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) psi.val := rfl

theorem canonicalBrauerEquiv_symm_pullback (phi : BF) :
    PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z)
      ((canonicalBrauerEquiv iota R Z hcentral).symm phi).val = phi.val.val := by
  have h := congrArg (fun chi : BF => chi.val.val)
    ((canonicalBrauerEquiv iota R Z hcentral).apply_symm_apply phi)
  exact (canonicalBrauerEquiv_val iota R Z hcentral _).symm.trans h

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


def transportedUp (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z)) : BF ≃ SectorWeights R Z :=
  ((canonicalBrauerEquiv iota R Z hcentral).symm.trans eD).trans
    (sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal).symm

theorem transportedUp_square (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z)) (phi : BF) :
    sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
      (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD phi) =
    eD ((canonicalBrauerEquiv iota R Z hcentral).symm phi) := by
  let EB := canonicalBrauerEquiv iota R Z hcentral
  let EW := sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
  change EW (EW.symm (eD (EB.symm phi))) = eD (EB.symm phi)
  exact EW.apply_symm_apply _

theorem transportedUp_apply_inflate (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z)) (psi : IBr (quotientRoot iota Z)) :
    transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
      (canonicalBrauerEquiv iota R Z hcentral psi) =
    (sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal).symm
      (eD psi) := by
  let EB := canonicalBrauerEquiv iota R Z hcentral
  let EW := sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
  change EW.symm (eD (EB.symm (EB psi))) = EW.symm (eD psi)
  exact congrArg (fun chi => EW.symm (eD chi)) (EB.symm_apply_apply psi)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
