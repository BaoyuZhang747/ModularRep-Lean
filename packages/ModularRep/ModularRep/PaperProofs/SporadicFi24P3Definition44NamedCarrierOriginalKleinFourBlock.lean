import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourRepresentativeCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJointFibreSaturation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteRowHistograms

/-!
# The original Klein-four block from its quotient ordinary catalogue

Complementary specified interval evaluations derive the quotient row
counts. The checked local action square transports fixedness to the
original group; the independent full total exhausts the joint fibre.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalKleinFourBlock

open ModularRep ModularRep.CharacterWeight
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
variable (stableU : Q.1.comap tau.toMonoidHom = Q.1)
variable (hbD8 : MulOpposite.op tauD • bD8 = bD8)
variable (hfullTotal : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
  R.1.weightBlock w = bK4} = 3)

include CU CD compatU compatD Sglobal Slocal square stableU hbD8 hfullTotal in
theorem weight_fixed_card_one_of_complementary_catalogue
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
    (hlocalFixed : Nat.card {r : Fin 4 //
      OrdinaryIrreducibleCharacter.twist K _ (rows r).1
        (localAut (fixedRadicalImage iota Z hcentral hprimeTo Q).1 tauD
          (image_stable (QuotientGroup.mk' Z) tau tauD square Q.1 stableU)) = (rows r).1} = 2) :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = bK4 ∧ MulOpposite.op tau • w = w} = 1 := by
  let Qbar := fixedRadicalImage iota Z hcentral hprimeTo Q
  let bK4D := quotientBlock iota Z hcentral hprimeTo R.1 Rbar.1 Sglobal bK4 hbSector
  let stableD : Qbar.1.comap tauD.toMonoidHom = Qbar.1 :=
    image_stable (QuotientGroup.mk' Z) tau tauD square Q.1 stableU
  have hdown := representative_counts_of_complementary_catalogue
    (quotientRoot iota Z) Rbar Qbar bD8 bK4D rows rowInjective rowSurjective
    (fun r => CD (rows r)) compatD S414 hit evaluationD8 evaluationK4 tauD stableD hbD8 (by simp)
    (natCard_hit_fin4_of_histogram hit histogram) hlocalFixed
  let ET := (representativeDZEquivWeightBlockRadicalFibre iota.prime R.1 Q bK4).symm.trans
    (representativeDZEquiv (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
      (RU := R.1) (RD := Rbar.1) (Sglobal := Sglobal) (Q := Q) (CU := CU) (CD := CD)
      (compatU := compatU) (compatD := compatD) (Slocal := Slocal) bK4 hbSector)
  have hJointTotal : Nat.card (WeightBlockRadicalFibre R.1 Q bK4) = 3 := (Nat.card_congr ET).trans hdown.1
  let EF := (fixedRepresentativeDZEquiv iota.prime R.1 Q bK4 tau stableU).symm.trans
    (representativeDZFixedEquiv (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
      (RU := R.1) (RD := Rbar.1) (Sglobal := Sglobal) (Q := Q) (CU := CU) (CD := CD)
      (compatU := compatU) (compatD := compatD) (Slocal := Slocal) (sigma := tau) (beta := tauD)
      (square := square) (stableU := stableU) bK4 hbSector)
  have hJointFixed : Nat.card {w : WeightBlockRadicalFibre R.1 Q bK4 //
      MulOpposite.op tau • w.1 = w.1} = 1 := (Nat.card_congr EF).trans hdown.2
  exact weightBlock_fixed_card_one R.1 Q bK4 hJointTotal hfullTotal tau hJointFixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalKleinFourBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
