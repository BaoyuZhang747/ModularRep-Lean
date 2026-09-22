import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryRowData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTable8RadicalConsequences

/-! Derive local class and fixed-count data from the full table and original rows. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryTableConstructor

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

universe u v
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance quotientFintype : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

open SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData


open SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryRowData
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
open SporadicFi24P3Definition44NamedCarrierRadicalClassLocalCounts
open SporadicFi24P3Definition44NamedCarrierTable8RadicalConsequences

variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (Rbar : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X ⧸ Subgroup.center X))
variable (tau : MulAut X)
variable {Row : Fin 34 → Type v}
variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]
variable (T : TrivialOrdinaryTableData iota tau Row BlockD)
variable (roles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})

def of_table_and_rows
    (D : TwoLocalOrdinaryRowData (iota := iota) (R := R) (Rbar := Rbar)
      (hprimeTo := T.primeToCenter) (roles := roles) (Sglobal := T.primitiveGlobal)) :
    TwoLocalOrdinaryBlockData (iota := iota) (R := R) (Rbar := Rbar)
      (tau := tau) (tauD := T.quotientAut) (hprimeTo := T.primeToCenter) (square := T.square)
      (roles := roles) (Sglobal := T.primitiveGlobal) := by
  have hclasses (Q : RadicalSubgroup (p := 2) (G := X ⧸ Subgroup.center X)) :
      MulOpposite.op T.quotientAut •
        (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X ⧸ Subgroup.center X)) =
          Quotient.mk'' Q :=
    radical_class_fixed_of_catalogue T.catalogue T.quotientAut T.classesFixed Q
  have hcard (j : Bool) :
      Nat.card (LocalDefectZeroCharacter (K := K)
        (fixedRadicalImage iota (Subgroup.center X) le_rfl T.primeToCenter (D.Q j))) =
          if j then 4 else 1 := by
    simpa only [Nat.card_fin] using
      (Nat.card_congr (Equiv.ofBijective (D.rows j)
        ⟨D.rowInjective j, D.rowSurjective j⟩)).symm
  have hdistinct :
      (Quotient.mk'' (fixedRadicalImage iota (Subgroup.center X) le_rfl
        T.primeToCenter (D.Q false)) : RadicalConjugacyClass (p := 2) (G := X ⧸ Subgroup.center X)) ≠
      Quotient.mk'' (fixedRadicalImage iota (Subgroup.center X) le_rfl T.primeToCenter (D.Q true)) := by
    intro heq
    have h := local_card_eq_of_radicalClass_eq (K := K) iota.prime
      (fixedRadicalImage iota (Subgroup.center X) le_rfl T.primeToCenter (D.Q false))
      (fixedRadicalImage iota (Subgroup.center X) le_rfl T.primeToCenter (D.Q true)) heq
    rw [hcard false, hcard true] at h
    norm_num at h
  refine {
    Q := D.Q
    reductionU := D.reductionU
    reductionD := D.reductionD
    compatibilityD := D.compatibilityD
    primitiveLocal := D.primitiveLocal
    rows := D.rows
    rowInjective := D.rowInjective
    rowSurjective := D.rowSurjective
    interval := D.interval
    hit := D.hit
    evaluationD8 := D.evaluationD8
    evaluationK4 := D.evaluationK4
    histograms := D.histograms
    classesFixed := fun j => hclasses
      (fixedRadicalImage iota (Subgroup.center X) le_rfl T.primeToCenter (D.Q j))
    classesDistinct := hdistinct
    correctedLocalFixed := ?_ }
  dsimp only
  exact corrected_four_rows_fixed_two_of_table
    T.catalogue T.quotientAut T.classesFixed T.entry T.table T.total T.fixed
    (fixedRadicalImage iota (Subgroup.center X) le_rfl T.primeToCenter (D.Q true))
    _ _ (D.rows true) ⟨D.rowInjective true, D.rowSurjective true⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryTableConstructor


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
