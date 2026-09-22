import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierClassCorrectedKleinFourBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientThreePointBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientBrauerCounts

/-!
# Nonprincipal weight signatures from two local ordinary catalogues

Interval evaluations target computed quotient blocks of the original
specified roles. Small-defect totals, original and quotient block stability,
and all four weight signatures are derived inside the constructor.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData

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

omit [CharP k 2] in
theorem trivialRoleSupport
    (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
    (roles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1}) (i : Fin 5) :
    IsCentralCharacterSector (Subgroup.center X)
      (R.1.operations.ambientBlockData.blockIdempotent (roles i).1)
      (1 : Subgroup.center X →* kˣ) := by
  rw [R.2]
  have h := (roles i).1.2.centralCharacterSector_isSector (Subgroup.center X) le_rfl
  change IsCentralCharacterSector (Subgroup.center X) (roles i).1.1 (blockSector (roles i).1) at h
  rw [(roles i).2] at h
  exact h

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

structure TwoLocalOrdinaryBlockData where
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
  classesFixed : ∀ j : Bool, MulOpposite.op tauD •
    (Quotient.mk'' (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q j)) :
      RadicalConjugacyClass (p := 2) (G := X ⧸ Subgroup.center X)) =
      Quotient.mk'' (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q j))
  classesDistinct :
    (Quotient.mk'' (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q false)) :
      RadicalConjugacyClass (p := 2) (G := X ⧸ Subgroup.center X)) ≠
      Quotient.mk'' (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q true))
  correctedLocalFixed :
    let hclass := (fixedRadicalImage_class_fixed_iff iota (Subgroup.center X)
      le_rfl hprimeTo tau tauD square (Q true)).mpr (classesFixed true)
    let g := classCorrectionElement (Q true) tau hclass
    let sigma := tau * MulAut.conj g
    let beta := tauD * MulAut.conj (QuotientGroup.mk' (Subgroup.center X) g)
    let correctedSquare := innerCorrection_square (QuotientGroup.mk' (Subgroup.center X))
      tau tauD square g
    Nat.card {r : Fin 4 // OrdinaryIrreducibleCharacter.twist K _ (rows true r).1
      (localAut (fixedRadicalImage iota (Subgroup.center X) le_rfl hprimeTo (Q true)).1 beta
        (image_stable (QuotientGroup.mk' (Subgroup.center X)) sigma beta correctedSquare
          (Q true).1 (classCorrectionElement_stable (Q true) tau hclass))) = (rows true r).1} = 2

variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {I : Type u} [Fintype I] {e : I → k[X]} (blocks : BlockIdempotentDecomposition e)

theorem nonprincipal_weight_signatures_of_two_local_ordinary_data
    (D : TwoLocalOrdinaryBlockData (iota := iota) (R := R) (Rbar := Rbar)
      (tau := tau) (tauD := tauD) (hprimeTo := hprimeTo) (square := square)
      (roles := roles) (Sglobal := Sglobal))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hBrOther : ∀ j : Fin 4,
      actualBrauerSignature iota hinj blocks tau (roles j.succ).1 = nonprincipalSignature j)
    (small : SmallDefectNumericalSource iota hinj R)
    (hDefectTrivial : ∀ j : Fin 4, ∃ H : Subgroup X,
      actualHasDefect R (roles j.succ).1 H ∧ Nat.card H =
        (if j = 0 then 4 else if j = 1 then 8 else 1)) :
    ∀ j : Fin 4, actualWeightSignature R tau (roles j.succ).1 = nonprincipalSignature j := by
  classical
  let _ := R.1.operations.ambientBlockData.fintypeBlock
  let _ := Rbar.1.operations.ambientBlockData.fintypeBlock
  have hTotal := nonprincipal_weight_totals iota hinj blocks R tau roles hBrOther small hDefectTrivial
  have hBlockFixed := nonprincipal_blocks_fixed iota hinj blocks tau roles hBrOther
  let injD := irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot iota (Subgroup.center X))
  let downD8 := quotientBlock iota (Subgroup.center X) le_rfl hprimeTo R.1 Rbar.1 Sglobal
    (roles 2).1 (trivialRoleSupport R roles 2)
  have hUpD8Brauer : Nat.card {phi : IBr iota //
      operationsBlock iota hinj R phi = (roles 2).1 ∧ MulOpposite.op tau • phi = phi} = 3 := by
    have h := congrArg Prod.snd (hBrOther 1)
    change Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (roles 2).1 ∧
      MulOpposite.op tau • phi = phi} = 3 at h
    simpa only [operationsBlock_eq iota hinj R blocks] using h
  have hTransport := quotientBlock_brauer_fixed_card iota (Subgroup.center X) le_rfl hprimeTo
    R.1 Rbar.1 Sglobal hinj injD (roles 2).1 (trivialRoleSupport R roles 2) tau tauD square
  change Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = (roles 2).1 ∧
    MulOpposite.op tau • phi = phi} =
    Nat.card {chi : IBr (quotientRoot iota (Subgroup.center X)) //
      operationsBlock (quotientRoot iota (Subgroup.center X)) injD Rbar chi = downD8 ∧
        MulOpposite.op tauD • chi = chi} at hTransport
  have hDownD8Brauer : Nat.card {chi : IBr (quotientRoot iota (Subgroup.center X)) //
      operationsBlock (quotientRoot iota (Subgroup.center X)) injD Rbar chi = downD8 ∧
        MulOpposite.op tauD • chi = chi} = 3 := hTransport.symm.trans hUpD8Brauer
  have hDownD8Fixed : MulOpposite.op tauD • downD8 = downD8 := by
    apply block_fixed_of_brauer_fixed_card_pos (quotientRoot iota (Subgroup.center X)) injD
      Rbar.1.operations.ambientBlockData.blocks tauD downD8
    have hpos : 0 < Nat.card {chi : IBr (quotientRoot iota (Subgroup.center X)) //
        operationsBlock (quotientRoot iota (Subgroup.center X)) injD Rbar chi = downD8 ∧
          MulOpposite.op tauD • chi = chi} := by
      rw [hDownD8Brauer]
      decide
    simpa only [operationsBlock_eq (quotientRoot iota (Subgroup.center X)) injD Rbar
      Rbar.1.operations.ambientBlockData.blocks] using hpos
  have hD8 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = (roles 2).1 ∧ MulOpposite.op tau • w = w} = 3 := by
    exact weight_fixed_card_three_of_one_four_histograms
      (iota := iota) (Z := Subgroup.center X) (hcentral := le_rfl) (hprimeTo := hprimeTo)
      (R := R) (Rbar := Rbar) (Sglobal := Sglobal) (Q := D.Q)
      (CU := D.reductionU) (CD := D.reductionD) (compatU := compatibility) (compatD := D.compatibilityD)
      (Slocal := D.primitiveLocal) (b := (roles 2).1) (hbSector := trivialRoleSupport R roles 2)
      (tau := tau) (tauD := tauD) (square := square) (decomposition := decomposition)
      (hb := hBlockFixed 1) (hfixed := D.classesFixed) (hne := D.classesDistinct)
      (hweightTotal := by simpa [nonprincipalSignature] using hTotal 1)
      D.rows D.rowInjective D.rowSurjective D.interval D.hit D.evaluationD8 D.histograms
  have hclassTrue : MulOpposite.op tau •
      (Quotient.mk'' (D.Q true) : RadicalConjugacyClass (p := 2) (G := X)) = Quotient.mk'' (D.Q true) :=
    (fixedRadicalImage_class_fixed_iff iota (Subgroup.center X)
      le_rfl hprimeTo tau tauD square (D.Q true)).mpr (D.classesFixed true)
  have hK4 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = (roles 1).1 ∧ MulOpposite.op tau • w = w} = 1 := by
    exact weight_fixed_card_one_of_class_fixed_complementary_catalogue
      (iota := iota) (Z := Subgroup.center X) (hcentral := le_rfl) (hprimeTo := hprimeTo)
      (R := R) (Rbar := Rbar) (Sglobal := Sglobal) (Q := D.Q true)
      (CU := D.reductionU true) (CD := D.reductionD true)
      (compatU := compatibility) (compatD := D.compatibilityD) (Slocal := D.primitiveLocal true)
      (bK4 := (roles 1).1) (hbSector := trivialRoleSupport R roles 1) (bD8 := downD8)
      (tau := tau) (tauD := tauD) (square := square) (hbD8 := hDownD8Fixed)
      (hfullTotal := by simpa [nonprincipalSignature] using hTotal 0) hclassTrue
      (D.rows true) (D.rowInjective true) (D.rowSurjective true) (D.interval true) (D.hit true)
      (D.evaluationD8 true) D.evaluationK4 (D.histograms true) D.correctedLocalFixed
  exact nonprincipal_weight_signatures_of_two_fixed_counts
    iota hinj blocks R tau roles hBrOther small hDefectTrivial hK4 hD8

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
