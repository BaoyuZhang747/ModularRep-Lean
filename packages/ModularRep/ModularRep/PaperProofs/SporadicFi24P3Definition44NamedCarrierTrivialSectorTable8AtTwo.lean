import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedAssembly
import ModularRep.PaperProofs.SporadicProposition57ComputationRelative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Original trivial-sector counts from the corrected ordinary Table 8 rows

The table is bound to actual local ordinary characters and their actual
corrected local twists. The original sector counts are then derived by the
previously constructed equivalences. The finite arithmetic is reused.
-/

noncomputable section
open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open TypeBCentralKernelNormalizerInertia
open SporadicProposition57ComputationRelative
open SporadicFi24P3Definition44NamedCarrierRadicalRowAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedAssembly
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

universe u w

section CatalogueCounts

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Fintype G]
variable {Row : Fin 34 → Type w} (C : Catalogue p K G (Fin 34) Row)

abbrev ActualFixedLocal (tau : MulAut G) (j : C.FixedIndex tau) :=
  {theta : LocalDefectZeroCharacter (K := K) (C.representative j.1) //
    OrdinaryIrreducibleCharacter.twist K _ theta.1
      (localAut (C.representative j.1).1 (C.correctedAut tau j)
        (C.correctedStable tau j)) = theta.1}

def fixedLocalRowEquivActual (tau : MulAut G) (j : C.FixedIndex tau) :
    C.FixedLocalRow tau j ≃ ActualFixedLocal C tau j :=
  (C.localEquiv j.1).subtypeEquiv (fun _ => Iff.rfl)

local instance fixedIndexFintype (tau : MulAut G) : Fintype (C.FixedIndex tau) :=
  Fintype.ofFinite _

theorem table8_catalogue_sums (tau : MulAut G)
    (hclasses : ∀ i : Fin 34, MulOpposite.op tau •
      (Quotient.mk'' (C.representative i) : RadicalConjugacyClass (p := p) (G := G)) =
        Quotient.mk'' (C.representative i))
    (entry : Fin 34 → TableSignatureEntry)
    (htable : (List.ofFn entry).Perm correctedFi24Table8AtTwo)
    (htotal : ∀ i : Fin 34,
      Nat.card (LocalDefectZeroCharacter (K := K) (C.representative i)) = (entry i).total)
    (hfixed : ∀ j : C.FixedIndex tau,
      Nat.card (ActualFixedLocal C tau j) = (entry j.1).fixed) :
    (∑ i : Fin 34, Nat.card (Row i)) = 41 ∧
      (∑ j : C.FixedIndex tau, Nat.card (C.FixedLocalRow tau j)) = 31 := by
  have hsumTotal : (∑ i : Fin 34, (entry i).total) = 41 := by
    have h := ((List.Perm.map TableSignatureEntry.total htable).sum_eq).trans
      correctedFi24Table8AtTwo_signature_sum.1
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using h
  have hsumFixed : (∑ i : Fin 34, (entry i).fixed) = 31 := by
    have h := ((List.Perm.map TableSignatureEntry.fixed htable).sum_eq).trans
      correctedFi24Table8AtTwo_signature_sum.2
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using h
  constructor
  · calc
      (∑ i : Fin 34, Nat.card (Row i)) = ∑ i : Fin 34, (entry i).total := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Nat.card_congr (C.localEquiv i)).trans (htotal i)
      _ = 41 := hsumTotal
  · let eIndex : C.FixedIndex tau ≃ Fin 34 := Equiv.subtypeUnivEquiv hclasses
    calc
      (∑ j : C.FixedIndex tau, Nat.card (C.FixedLocalRow tau j)) =
          ∑ i : Fin 34, (entry i).fixed := by
        apply Fintype.sum_equiv eIndex
        intro j
        exact (Nat.card_congr (fixedLocalRowEquivActual C tau j)).trans (hfixed j)
      _ = 31 := hsumFixed

end CatalogueCounts

section CenterSupport

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

omit [CharP k p] in
theorem center_support_iff_weightSector_one
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (w : WeightClass (p := p) (K := K) (X := X)) :
    IsCentralCharacterSector (Subgroup.center X) (R.1.weightBlock w).1
        (1 : Subgroup.center X →* kˣ) ↔ weightSector (R := R) w = 1 := by
  constructor
  · intro h
    change (R.1.weightBlock w).2.centralCharacterSector (Subgroup.center X) le_rfl = 1
    exact ((R.1.weightBlock w).2.centralCharacterSector_unique
      (Subgroup.center X) le_rfl h).symm
  · intro h
    have hs := (R.1.weightBlock w).2.centralCharacterSector_isSector
      (Subgroup.center X) le_rfl
    change IsCentralCharacterSector (Subgroup.center X) (R.1.weightBlock w).1
      (weightSector (R := R) w) at hs
    rwa [h] at hs

def centerSectorWeightsEquiv
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)) :
    SectorWeights R (Subgroup.center X) ≃
      {w : WeightClass (p := p) (K := K) (X := X) // weightSector (R := R) w = 1} :=
  Equiv.subtypeEquivRight (center_support_iff_weightSector_one R)

def centerSectorFixedWeightsEquiv
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (tau : MulAut X) :
    {w : SectorWeights R (Subgroup.center X) // MulOpposite.op tau • w.1 = w.1} ≃
      {w : WeightClass (p := p) (K := K) (X := X) //
        weightSector (R := R) w = 1 ∧ MulOpposite.op tau • w = w} := by
  let E : {w : SectorWeights R (Subgroup.center X) // MulOpposite.op tau • w.1 = w.1} ≃
      {w : {w : WeightClass (p := p) (K := K) (X := X) // weightSector (R := R) w = 1} //
        MulOpposite.op tau • w.1 = w.1} :=
    (centerSectorWeightsEquiv R).subtypeEquiv (fun _ => Iff.rfl)
  exact E.trans (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun w : WeightClass (p := p) (K := K) (X := X) => weightSector (R := R) w = 1)
    (fun w : WeightClass (p := p) (K := K) (X := X) => MulOpposite.op tau • w = w))

end CenterSupport

section OriginalCounts

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance originalSubgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance originalQuotientFintype : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {Row : Fin 34 → Type w} [∀ i, Finite (Row i)]
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hprimeTo : ¬ 2 ∣ Nat.card (Subgroup.center X))
variable (C : Catalogue 2 K (X ⧸ Subgroup.center X) (Fin 34) Row)
variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := 2) (k := k) (K := K) (G := X ⧸ Subgroup.center X) (Block := BlockD))
variable (CU : ∀ i (theta : LocalDefectZeroCharacter (K := K)
    (liftedRepresentative iota (Subgroup.center X) le_rfl hprimeTo C i)),
  CanonicalRawReduction iota (characterWeightAt iota.prime
    (liftedRepresentative iota (Subgroup.center X) le_rfl hprimeTo C i) theta))
variable (CD : ∀ i (eta : LocalDefectZeroCharacter (K := K) (C.representative i)),
  CanonicalRawReduction (quotientRoot iota (Subgroup.center X))
    (characterWeightAt iota.prime (C.representative i) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota (Subgroup.center X)) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective (Subgroup.center X)) iota.prime
  (by simp only [QuotientGroup.ker_mk']; exact le_rfl)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : ∀ i, CentralPrimeToPrimitiveImageSource (k := k)
  (normalizerMap (QuotientGroup.mk' (Subgroup.center X))
    (liftedRepresentative iota (Subgroup.center X) le_rfl hprimeTo C i).1)
  (fixedNormalizer_surjective iota.prime (Subgroup.center X) le_rfl hprimeTo
    (liftedRepresentative iota (Subgroup.center X) le_rfl hprimeTo C i).1
    (liftedRepresentative iota (Subgroup.center X) le_rfl hprimeTo C i).2) iota.prime
  (fixedNormalizer_kernel_central (Subgroup.center X)
    (liftedRepresentative iota (Subgroup.center X) le_rfl hprimeTo C i).1 le_rfl)
  (fixedNormalizer_kernel_primeTo (Subgroup.center X)
    (liftedRepresentative iota (Subgroup.center X) le_rfl hprimeTo C i).1 le_rfl hprimeTo))
variable (tau : MulAut X) (tauD : MulAut (X ⧸ Subgroup.center X))
variable (square : ∀ x : X,
  QuotientGroup.mk' (Subgroup.center X) (tau x) = tauD (QuotientGroup.mk' (Subgroup.center X) x))

local instance originalFixedIndexFintype : Fintype (C.FixedIndex tauD) := Fintype.ofFinite _

include CU CD compatU compatD Sglobal Slocal square in
theorem actualTrivialSectorCounts_of_table8
    (hclasses : ∀ i : Fin 34, MulOpposite.op tauD •
      (Quotient.mk'' (C.representative i) :
        RadicalConjugacyClass (p := 2) (G := X ⧸ Subgroup.center X)) =
          Quotient.mk'' (C.representative i))
    (entry : Fin 34 → TableSignatureEntry)
    (htable : (List.ofFn entry).Perm correctedFi24Table8AtTwo)
    (htotal : ∀ i : Fin 34,
      Nat.card (LocalDefectZeroCharacter (K := K) (C.representative i)) = (entry i).total)
    (hfixed : ∀ j : C.FixedIndex tauD,
      Nat.card (ActualFixedLocal C tauD j) = (entry j.1).fixed) :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) w = 1} = 41 ∧
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) w = 1 ∧ MulOpposite.op tau • w = w} = 31 := by
  have sums := table8_catalogue_sums C tauD hclasses entry htable htotal hfixed
  constructor
  · calc
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
          weightSector (R := R) w = 1} =
          Nat.card (SectorWeights R (Subgroup.center X)) :=
        Nat.card_congr (centerSectorWeightsEquiv R).symm
      _ = ∑ i : Fin 34, Nat.card (Row i) :=
        sectorWeights_card (R := R) (Z := Subgroup.center X) (iota := iota)
          (hcentral := le_rfl) (hprimeTo := hprimeTo) (C := C) (OD := OD)
          (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD)
          (Sglobal := Sglobal) (Slocal := Slocal)
      _ = 41 := sums.1
  · calc
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
          weightSector (R := R) w = 1 ∧ MulOpposite.op tau • w = w} =
          Nat.card {w : SectorWeights R (Subgroup.center X) //
            MulOpposite.op tau • w.1 = w.1} :=
        Nat.card_congr (centerSectorFixedWeightsEquiv R tau).symm
      _ = ∑ j : C.FixedIndex tauD, Nat.card (C.FixedLocalRow tauD j) :=
        sectorFixedWeights_card (R := R) (Z := Subgroup.center X) (iota := iota)
          (hcentral := le_rfl) (hprimeTo := hprimeTo) (C := C) (OD := OD)
          (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD)
          (Sglobal := Sglobal) (Slocal := Slocal)
          (tau := tau) (tauD := tauD) (square := square)
      _ = 31 := sums.2

end OriginalCounts

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
