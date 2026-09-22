import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRadicalLabels
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction

/-! Ordinary local consequences of the retained quotient correspondence. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalAction

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


def brauerTransport (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (hD : ∀ psi : IBr (quotientRoot iota Z),
      eD (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) =
        MulOpposite.op beta • eD psi)
    (Q : RadicalSubgroup (p := p) (G := X))
    (phi : brauerAtRadical iota R Z hcentral
      (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD) Q) :
    brauerAtRadical iota R Z hcentral
      (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD)
      (Q.rightTwist alpha) := by
  refine ⟨brauerSectorTwist iota R Z hcentral alpha beta square phi.val, ?_⟩
  change radicalClass
    (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
      (brauerSectorTwist iota R Z hcentral alpha beta square phi.val)).val = _
  rw [transportedUp_covariance iota R Z hcentral hprimeTo OD CU CD compatU compatD
    Sglobal Slocal eD alpha beta square hD phi.val]
  change radicalClass (MulOpposite.op alpha •
    (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD phi.val).val) = _
  rw [radicalClass_equivariant, phi.property]
  rfl

theorem localOrdinaryEquiv_covariance (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (hD : ∀ psi : IBr (quotientRoot iota Z),
      eD (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) =
        MulOpposite.op beta • eD psi)
    (Q : RadicalSubgroup (p := p) (G := X))
    (phi : brauerAtRadical iota R Z hcentral
      (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD) Q) :
    (localOrdinaryEquiv iota R Z hcentral
      (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD)
      (Q.rightTwist alpha)
      (brauerTransport iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
        eD alpha beta square hD Q phi)).val =
    SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localCharacterTwist
      iota.prime Q (MulOpposite.op alpha)
      (localOrdinaryEquiv iota R Z hcentral
        (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD)
        Q phi).val := by
  apply classAt_injective iota.prime (Q.rightTwist alpha)
  rw [localOrdinaryEquiv_class]
  change
    (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
      (brauerSectorTwist iota R Z hcentral alpha beta square phi.val)).val =
    MulOpposite.op alpha • classAt iota.prime Q
      (localOrdinaryEquiv iota R Z hcentral
        (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD)
        Q phi).val
  rw [transportedUp_covariance iota R Z hcentral hprimeTo OD CU CD compatU compatD
    Sglobal Slocal eD alpha beta square hD phi.val,
    localOrdinaryEquiv_class]
  rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientLocalAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
