import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualThreePointBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteRowHistograms

/-!
# Two quotient rows and the original three-point block

The intermediate row-count lemma is discharged by ordinary catalogue
allocation in the final constructor. Original total three remains an
independent numerical input.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientThreePointBlock

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
open SporadicFi24P3Definition44NamedCarrierActualThreePointBlock
open SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
open SporadicFi24P3Definition44NamedCarrierFiniteRowHistograms
open CentralEllPrimeWeightLocalQuotient

universe u v

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) :=
  Fintype.ofFinite _
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
variable (Q : Bool → CharacterWeight.RadicalSubgroup (p := 2) (G := X))
variable (CU : ∀ j : Bool, ∀ theta : LocalDefectZeroCharacter (K := K) (Q j),
  CanonicalRawReduction iota (characterWeightAt iota.prime (Q j) theta))
variable (CD : ∀ j : Bool,
  ∀ eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo (Q j)),
  CanonicalRawReduction (quotientRoot iota Z)
    (characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo (Q j)) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) Rbar.1.operations)
variable (Slocal : ∀ j : Bool, CentralPrimeToPrimitiveImageSource (k := k)
  (normalizerMap (QuotientGroup.mk' Z) (Q j).1)
  (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo (Q j).1 (Q j).2) iota.prime
  (fixedNormalizer_kernel_central Z (Q j).1 hcentral)
  (fixedNormalizer_kernel_primeTo Z (Q j).1 hcentral hprimeTo))
variable (b : ActualBlock (k := k) (X := X))
variable (hbSector : IsCentralCharacterSector Z
  (R.1.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ))
variable (tau : MulAut X) (tauD : MulAut (X ⧸ Z))
variable (square : ∀ x : X, QuotientGroup.mk' Z (tau x) = tauD (QuotientGroup.mk' Z x))
variable (decomposition : ∀ a : MulAut X, ∃ x : X,
  a = MulAut.conj x ∨ a = MulAut.conj x * tau)
variable (hb : MulOpposite.op tau • b = b)
variable (hfixed : ∀ j : Bool,
  MulOpposite.op tauD •
      (Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo (Q j)) :
        RadicalConjugacyClass (p := 2) (G := X ⧸ Z)) =
    Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo (Q j)))
variable (hne :
  (Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo (Q false)) :
      RadicalConjugacyClass (p := 2) (G := X ⧸ Z)) ≠
    Quotient.mk'' (fixedRadicalImage iota Z hcentral hprimeTo (Q true)))
variable (hweightTotal : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
  R.1.weightBlock w = b} = 3)

include CU CD compatU compatD Sglobal Slocal square decomposition hb hfixed hne hweightTotal in
theorem weight_fixed_card_three_of_quotient_rows
    (hrows : ∀ j : Bool,
      Nat.card (RepresentativeDZ iota.prime Rbar.1
        (fixedRadicalImage iota Z hcentral hprimeTo (Q j))
        (quotientBlock iota Z hcentral hprimeTo R.1 Rbar.1 Sglobal b hbSector)) = 1) :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w} = 3 := by
  have hfixedU (j : Bool) : MulOpposite.op tau •
      (Quotient.mk'' (Q j) : RadicalConjugacyClass (p := 2) (G := X)) =
        Quotient.mk'' (Q j) :=
    (fixedRadicalImage_class_fixed_iff iota Z hcentral hprimeTo tau tauD square (Q j)).mpr (hfixed j)
  have hneU : (Quotient.mk'' (Q false) : RadicalConjugacyClass (p := 2) (G := X)) ≠
      Quotient.mk'' (Q true) := by
    intro h
    exact hne ((fixedRadicalImage_class_eq_iff iota Z hcentral hprimeTo (Q false) (Q true)).mpr h)
  have hrowU (j : Bool) : Nat.card (WeightBlockRadicalFibre R.1 (Q j) b) = 1 := by
    calc
      _ = Nat.card (RepresentativeDZ iota.prime R.1 (Q j) b) :=
        Nat.card_congr (representativeDZEquivWeightBlockRadicalFibre iota.prime R.1 (Q j) b).symm
      _ = Nat.card (RepresentativeDZ iota.prime Rbar.1
          (fixedRadicalImage iota Z hcentral hprimeTo (Q j))
          (quotientBlock iota Z hcentral hprimeTo R.1 Rbar.1 Sglobal b hbSector)) :=
        Nat.card_congr (representativeDZEquiv (iota := iota) (Z := Z)
          (hcentral := hcentral) (hprimeTo := hprimeTo)
          (RU := R.1) (RD := Rbar.1) (Sglobal := Sglobal) (Q := Q j)
          (CU := CU j) (CD := CD j) (compatU := compatU) (compatD := compatD)
          (Slocal := Slocal j) b hbSector)
      _ = 1 := hrows j
  exact weight_fixed_card_three R tau decomposition b (Quotient.mk'' (Q false))
    (Quotient.mk'' (Q true)) hb (hfixedU false) (hfixedU true) hneU
    (hrowU false) (hrowU true) hweightTotal

include CU CD compatU compatD Sglobal Slocal square decomposition hb hfixed hne hweightTotal in
theorem weight_fixed_card_three_of_ordinary_catalogues
    {Row : Bool → Type v}
    (rows : ∀ j : Bool, Row j → LocalDefectZeroCharacter (K := K)
      (fixedRadicalImage iota Z hcentral hprimeTo (Q j)))
    (rowInjective : ∀ j : Bool, Function.Injective (rows j))
    (rowSurjective : ∀ j : Bool, Function.Surjective (rows j))
    (S414 : ∀ j : Bool, NormalizerIntervalSource Rbar.1.operations
      (fixedRadicalImage iota Z hcentral hprimeTo (Q j)))
    (hit : ∀ j : Bool, Row j → Bool)
    (evaluation : ∀ (j : Bool) (r : Row j),
      intervalEvaluation Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo (Q j))
        (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo (Q j)).1
          (CD j (rows j r)).normalizerRoot (CD j (rows j r)).localBrauer)
        (quotientBlock iota Z hcentral hprimeTo R.1 Rbar.1 Sglobal b hbSector) =
          if hit j r then (1 : k) else 0)
    (hhit : ∀ j : Bool, Nat.card {r : Row j // hit j r = true} = 1) :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w} = 3 := by
  have hrows (j : Bool) : Nat.card (RepresentativeDZ iota.prime Rbar.1
      (fixedRadicalImage iota Z hcentral hprimeTo (Q j))
      (quotientBlock iota Z hcentral hprimeTo R.1 Rbar.1 Sglobal b hbSector)) = 1 := by
    let E := hitRowsEquivRepresentativeDZ (quotientRoot iota Z) Rbar.1
      (fixedRadicalImage iota Z hcentral hprimeTo (Q j))
      (quotientBlock iota Z hcentral hprimeTo R.1 Rbar.1 Sglobal b hbSector)
      (rows j) (rowInjective j) (rowSurjective j) (fun r => CD j (rows j r))
      compatD (S414 j) (hit j) (evaluation j)
    exact (Nat.card_congr E).symm.trans (hhit j)
  exact weight_fixed_card_three_of_quotient_rows
    (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
    (R := R) (Rbar := Rbar) (Sglobal := Sglobal) (Q := Q)
    (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD) (Slocal := Slocal)
    (b := b) (hbSector := hbSector) (tau := tau) (tauD := tauD) (square := square)
    (decomposition := decomposition) (hb := hb) (hfixed := hfixed) (hne := hne)
    (hweightTotal := hweightTotal) hrows

include CU CD compatU compatD Sglobal Slocal square decomposition hb hfixed hne hweightTotal in
theorem weight_fixed_card_three_of_one_four_histograms
    (rows : ∀ j : Bool, Fin (if j then 4 else 1) → LocalDefectZeroCharacter (K := K)
      (fixedRadicalImage iota Z hcentral hprimeTo (Q j)))
    (rowInjective : ∀ j : Bool, Function.Injective (rows j))
    (rowSurjective : ∀ j : Bool, Function.Surjective (rows j))
    (S414 : ∀ j : Bool, NormalizerIntervalSource Rbar.1.operations
      (fixedRadicalImage iota Z hcentral hprimeTo (Q j)))
    (hit : ∀ j : Bool, Fin (if j then 4 else 1) → Bool)
    (evaluation : ∀ (j : Bool) (r : Fin (if j then 4 else 1)),
      intervalEvaluation Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo (Q j))
        (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          Rbar.1.operations (fixedRadicalImage iota Z hcentral hprimeTo (Q j)).1
          (CD j (rows j r)).normalizerRoot (CD j (rows j r)).localBrauer)
        (quotientBlock iota Z hcentral hprimeTo R.1 Rbar.1 Sglobal b hbSector) =
          if hit j r then (1 : k) else 0)
    (histograms : ∀ j : Bool, (List.ofFn (hit j)).Perm
      (if j then [false, false, false, true] else [true])) :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w} = 3 := by
  have hhit (j : Bool) : Nat.card {r : Fin (if j then 4 else 1) // hit j r = true} = 1 := by
    cases j with
    | false => exact natCard_hit_fin1_of_histogram (hit false) (histograms false)
    | true => exact natCard_hit_fin4_of_histogram (hit true) (histograms true)
  exact weight_fixed_card_three_of_ordinary_catalogues
    (iota := iota) (Z := Z) (hcentral := hcentral) (hprimeTo := hprimeTo)
    (R := R) (Rbar := Rbar) (Sglobal := Sglobal) (Q := Q)
    (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD) (Slocal := Slocal)
    (b := b) (hbSector := hbSector) (tau := tau) (tauD := tauD) (square := square)
    (decomposition := decomposition) (hb := hb) (hfixed := hfixed) (hne := hne)
    (hweightTotal := hweightTotal) rows rowInjective rowSurjective S414 hit evaluation hhit

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientThreePointBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
