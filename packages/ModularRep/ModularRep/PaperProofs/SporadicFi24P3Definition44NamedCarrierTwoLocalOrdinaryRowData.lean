import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData

/-! The same two local ordinary row catalogues, with no class fixedness,
class distinctness or corrected local fixed-count fields. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryRowData

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
open SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts
open SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFixedCentralRadicalClasses
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction
open SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
open SporadicFi24P3Definition44NamedCarrierClassCorrectedKleinFourBlock
open SporadicFi24P3Definition44NamedCarrierPairedInnerCorrection
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientBrauerCounts
open SporadicFi24P3Definition44NamedCarrierQuotientThreePointBlock
open CentralEllPrimeWeightLocalQuotient TypeBCentralKernelNormalizerInertia

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance quotientFintype : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

open SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData

variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (Rbar : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X ⧸ Subgroup.center X))
variable (tau : MulAut X) (tauD : MulAut (X ⧸ Subgroup.center X))
variable (hprimeTo : ¬ 2 ∣ Nat.card (Subgroup.center X))
variable (square : ∀ x : X, QuotientGroup.mk' (Subgroup.center X) (tau x) =
  tauD (QuotientGroup.mk' (Subgroup.center X) x))
variable (roles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' (Subgroup.center X))
  (QuotientGroup.mk'_surjective (Subgroup.center X)) iota.prime
  (by simp only [QuotientGroup.ker_mk']; exact le_rfl)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))

structure TwoLocalOrdinaryRowData where
  Q : Bool → CharacterWeight.RadicalSubgroup (p := 2) (G := X)
  reductionU : ∀ j : Bool, ∀ theta : LocalDefectZeroCharacter (K := K) (Q j),
    CanonicalRawReduction iota (characterWeightAt iota.prime (Q j) theta)
  reductionD : ∀ j : Bool,
    ∀ eta : LocalDefectZeroCharacter (K := K)
      (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q j)),
    CanonicalRawReduction (quotientRoot iota (Subgroup.center X))
      (characterWeightAt iota.prime
        (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q j)) eta)
  compatibilityD : CanonicalLocalBlockCompatibility
    (quotientRoot iota (Subgroup.center X)) Rbar.1.operations
  primitiveLocal : ∀ j : Bool, CentralPrimeToPrimitiveImageSource (k := k)
    (normalizerMap (QuotientGroup.mk' (Subgroup.center X)) (Q j).1)
    (fixedNormalizer_surjective iota.prime (Subgroup.center X) le_rfl hprimeTo (Q j).1 (Q j).2) iota.prime
    (fixedNormalizer_kernel_central (Subgroup.center X) (Q j).1 le_rfl)
    (fixedNormalizer_kernel_primeTo (Subgroup.center X) (Q j).1 le_rfl hprimeTo)
  rows : ∀ j : Bool, Fin (if j then 4 else 1) → LocalDefectZeroCharacter (K := K)
    (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q j))
  rowInjective : ∀ j : Bool, Function.Injective (rows j)
  rowSurjective : ∀ j : Bool, Function.Surjective (rows j)
  interval : ∀ j : Bool, NormalizerIntervalSource Rbar.1.operations
    (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q j))
  hit : ∀ j : Bool, Fin (if j then 4 else 1) → Bool
  evaluationD8 : ∀ (j : Bool) (r : Fin (if j then 4 else 1)),
    intervalEvaluation Rbar.1.operations
      (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q j))
      (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock Rbar.1.operations
        (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q j)).1
        (reductionD j (rows j r)).normalizerRoot (reductionD j (rows j r)).localBrauer)
      (quotientBlock iota (Subgroup.center X) le_rfl hprimeTo R.1 Rbar.1 Sglobal
        (roles 2).1 (trivialRoleSupport R roles 2)) = if hit j r then (1 : k) else 0
  evaluationK4 : ∀ r : Fin 4,
    intervalEvaluation Rbar.1.operations
      (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q true))
      (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock Rbar.1.operations
        (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q true)).1
        (reductionD true (rows true r)).normalizerRoot (reductionD true (rows true r)).localBrauer)
      (quotientBlock iota (Subgroup.center X) le_rfl hprimeTo R.1 Rbar.1 Sglobal
        (roles 1).1 (trivialRoleSupport R roles 1)) = if !hit true r then (1 : k) else 0
  histograms : ∀ j : Bool, (List.ofFn (hit j)).Perm
    (if j then [false, false, false, true] else [true])

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryRowData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
