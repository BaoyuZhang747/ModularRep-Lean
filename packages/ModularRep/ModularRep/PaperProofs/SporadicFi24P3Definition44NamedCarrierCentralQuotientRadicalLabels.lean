import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport

/-! The constructed quotient weight map transports the actual radical label. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRadicalLabels

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRawWeights
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport

universe u

def quotientRadicalEquiv
    {p : ℕ} {k K X : Type u} [Field k] [Field K] [Group X] [Fintype X]
    (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z) :
    RadicalConjugacyClass (p := p) (G := X) ≃
      RadicalConjugacyClass (p := p) (G := X ⧸ Z) := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  exact radicalConjugacyEquiv (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    (by simpa only [QuotientGroup.ker_mk'] using hcentral)
    (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)

theorem quotientRadicalEquiv_mk
    {p : ℕ} {k K X : Type u} [Field k] [Field K] [Group X] [Fintype X]
    (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
    (Q : RadicalSubgroup (p := p) (G := X)) :
    quotientRadicalEquiv iota Z hcentral hprimeTo (Quotient.mk'' Q) =
      Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo Q) := rfl

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


local notation "EW" => sectorToQuotient iota R Z hcentral hprimeTo
  OD CU CD compatU compatD Sglobal Slocal
local notation "ER" => quotientRadicalEquiv iota Z hcentral hprimeTo

theorem sectorToQuotient_radicalClass (w : SectorWeights R Z) :
    radicalClass (EW w) = ER (radicalClass w.val) := by
  obtain ⟨W, hW⟩ := rawClass_surjective (p := p) (K := K) (X := X) w.val
  calc
    radicalClass (EW w) = radicalClass (rawClass
        (rawDescent Z hcentral hprimeTo W
          (sectorRawKernel iota R Z hcentral hprimeTo CU compatU w W hW))) :=
      congrArg radicalClass (sectorToQuotient_apply_raw iota R Z hcentral hprimeTo
        OD CU CD compatU compatD Sglobal Slocal w W hW)
    _ = ER (radicalClass (rawClass W)) := rfl
    _ = ER (radicalClass w.val) := congrArg (fun v => ER (radicalClass v)) hW

theorem sectorToQuotient_radicalClass_eq_iff (w : SectorWeights R Z)
    (Q : RadicalSubgroup (p := p) (G := X)) :
    radicalClass (EW w) = Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo Q) ↔
      radicalClass w.val = Quotient.mk'' Q := by
  rw [sectorToQuotient_radicalClass iota R Z hcentral hprimeTo
    OD CU CD compatU compatD Sglobal Slocal,
    ← quotientRadicalEquiv_mk iota Z hcentral hprimeTo Q]
  exact (ER).injective.eq_iff

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRadicalLabels


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
