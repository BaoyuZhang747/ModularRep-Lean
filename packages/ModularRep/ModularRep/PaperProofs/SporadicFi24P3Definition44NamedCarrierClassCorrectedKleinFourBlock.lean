import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalKleinFourBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPairedInnerCorrection

/-! # The original Klein-four fixed count from a fixed radical class -/
noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierClassCorrectedKleinFourBlock

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierOriginalKleinFourBlock
open SporadicFi24P3Definition44NamedCarrierPairedInnerCorrection
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFixedPoints
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction
open SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
open SporadicFi24P3Definition44NamedCarrierKleinFourRepresentativeCounts
open SporadicFi24P3Definition44NamedCarrierJointFibreSaturation
open SporadicFi24P3Definition44NamedCarrierFiniteRowHistograms
open CentralEllPrimeWeightLocalQuotient TypeBCentralKernelNormalizerInertia

universe u

def classCorrectionElement
    {p : ℕ} {X : Type u} [Group X]
    (Q : RadicalSubgroup (p := p) (G := X)) (tau : MulAut X)
    (hclass : MulOpposite.op tau •
      (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' Q) : X :=
  Classical.choose (exists_innerCorrection_of_fixed_radicalClass Q tau hclass)

theorem classCorrectionElement_stable
    {p : ℕ} {X : Type u} [Group X]
    (Q : RadicalSubgroup (p := p) (G := X)) (tau : MulAut X)
    (hclass : MulOpposite.op tau •
      (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' Q) :
    Q.1.comap (tau * MulAut.conj (classCorrectionElement Q tau hclass)).toMonoidHom = Q.1 :=
  Classical.choose_spec (exists_innerCorrection_of_fixed_radicalClass Q tau hclass)
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite H
variable (iota : PrimeRegularRootEmbedding 2 k K X) (Z : Subgroup X) [Z.Normal]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ 2 ∣ Nat.card Z)
variable [Invertible (Fintype.card Z : k)]
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (Rbar : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X ⧸ Z))
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Q : RadicalSubgroup (p := 2) (G := X))
variable (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q),
  CanonicalRawReduction (quotientRoot iota Z)
    (characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) Rbar.1.operations)
variable (Slocal : CentralPrimeToPrimitiveImageSource (k := k)
  (normalizerMap (QuotientGroup.mk' Z) Q.1)
  (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
  (fixedNormalizer_kernel_central Z Q.1 hcentral)
  (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))
variable (bK4 : ActualBlock (k := k) (X := X))
variable (hbSector : IsCentralCharacterSector Z
  (R.1.operations.ambientBlockData.blockIdempotent bK4) (1 : Z →* kˣ))
variable (bD8 : ActualBlock (k := k) (X := X ⧸ Z))
variable (tau : MulAut X) (tauD : MulAut (X ⧸ Z))
variable (square : ∀ x : X, QuotientGroup.mk' Z (tau x) = tauD (QuotientGroup.mk' Z x))
variable (hbD8 : MulOpposite.op tauD • bD8 = bD8)
variable (hfullTotal : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
  R.1.weightBlock w = bK4} = 3)

include CU CD compatU compatD Sglobal Slocal square hbD8 hfullTotal in
theorem weight_fixed_card_one_of_class_fixed_complementary_catalogue
    (hclass : MulOpposite.op tau •
      (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X)) = Quotient.mk'' Q)
    (rows : Fin 4 → LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q))
    (rowInjective : Function.Injective rows) (rowSurjective : Function.Surjective rows)
    (S414 : NormalizerIntervalSource Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo Q))
    (hit : Fin 4 → Bool)
    (evaluationD8 : ∀ r : Fin 4,
      intervalEvaluation Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo Q)
        (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo Q).1
          (CD (rows r)).normalizerRoot (CD (rows r)).localBrauer) bD8 =
        if hit r then (1 : k) else 0)
    (evaluationK4 : ∀ r : Fin 4,
      intervalEvaluation Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo Q)
        (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo Q).1
          (CD (rows r)).normalizerRoot (CD (rows r)).localBrauer)
        (quotientBlock iota Z hcentral hprimeTo R.1 Rbar.1 Sglobal bK4 hbSector) =
        if !hit r then (1 : k) else 0)
    (histogram : (List.ofFn hit).Perm [false, false, false, true])
    (hlocalFixed :
      let g := classCorrectionElement Q tau hclass
      let sigma := tau * MulAut.conj g
      let beta := tauD * MulAut.conj (QuotientGroup.mk' Z g)
      let correctedSquare := innerCorrection_square (QuotientGroup.mk' Z) tau tauD square g
      Nat.card {r : Fin 4 //
        OrdinaryIrreducibleCharacter.twist K _ (rows r).1
          (localAut (fixedRadicalImage iota Z hcentral hprimeTo Q).1 beta
            (image_stable (QuotientGroup.mk' Z) sigma beta correctedSquare
              Q.1 (classCorrectionElement_stable Q tau hclass))) = (rows r).1} = 2) :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = bK4 ∧ MulOpposite.op tau • w = w} = 1 := by
  let g := classCorrectionElement Q tau hclass
  let sigma : MulAut X := tau * MulAut.conj g
  let beta : MulAut (X ⧸ Z) := tauD * MulAut.conj (QuotientGroup.mk' Z g)
  have stable : Q.1.comap sigma.toMonoidHom = Q.1 := classCorrectionElement_stable Q tau hclass
  have correctedSquare : ∀ x : X,
      QuotientGroup.mk' Z (sigma x) = beta (QuotientGroup.mk' Z x) :=
    innerCorrection_square (QuotientGroup.mk' Z) tau tauD square g
  have hbD8' : MulOpposite.op beta • bD8 = bD8 := by
    simpa only [beta, innerCorrection_block_smul Rbar.1] using hbD8
  have hlocalFixed' : Nat.card {r : Fin 4 //
      OrdinaryIrreducibleCharacter.twist K _ (rows r).1
        (localAut (fixedRadicalImage iota Z hcentral hprimeTo Q).1 beta
          (image_stable (QuotientGroup.mk' Z) sigma beta correctedSquare Q.1 stable)) = (rows r).1} = 2 :=
    hlocalFixed
  have result := weight_fixed_card_one_of_complementary_catalogue
    (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
    (R := R) (Rbar := Rbar) (Sglobal := Sglobal) (Q := Q)
    (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD) (Slocal := Slocal)
    (bK4 := bK4) (hbSector := hbSector) (bD8 := bD8)
    (tau := sigma) (tauD := beta) (square := correctedSquare) (stableU := stable)
    (hbD8 := hbD8') (hfullTotal := hfullTotal)
    rows rowInjective rowSurjective S414 hit evaluationD8 evaluationK4 histogram hlocalFixed'
  simpa only [sigma, innerCorrection_weight_smul] using result

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierClassCorrectedKleinFourBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
