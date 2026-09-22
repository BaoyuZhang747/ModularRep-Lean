import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralCorrespondence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLiteralActualCount
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallActualCount

/-! The original conditional correspondence with every Brauer numerical input
derived internally from the literal ordinary rows and actual source bindings. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllLiteralBrauerCorrespondence

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
open SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData
open SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
open SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts
open SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorAllCountsAtTwo
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorCounts
open SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
open SporadicFi24P3Definition44NamedCarrierWeightSectorFinite
open SporadicFi24P3Definition44NamedCarrierAllPairs

open SporadicFi24P3Definition44NamedCarrierActualTwoSectorSmallDefectCorrespondence
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
open SporadicFi24P3Definition44NamedCarrierKleinFourActualCounts
open SporadicFi24P3Definition44NamedCarrierTrivialLiteralActualCounts

open SporadicFi24P3Definition44NamedCarrierKleinFourLiteralCorrespondence
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialActualCounts

universe u v w
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
local instance quotientFintype : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {BIndex : Type u} [Fintype BIndex] {e : BIndex → k[X]} (blocks : BlockIdempotentDecomposition e)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (Rbar : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X ⧸ Subgroup.center X))
variable (tau : MulAut X)
variable {RowT : Fin 34 → Type v} {RowF : Fin 34 → Type w}
variable [∀ i, Finite (RowT i)] [∀ i, Finite (RowF i)]
variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]
variable (T : TrivialOrdinaryTableData iota tau RowT BlockD)
variable (F : FaithfulOrdinaryTableData iota RowF)
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (decomposition : ∀ a : MulAut X, ∃ x : X,
  a = MulAut.conj x ∨ a = MulAut.conj x * tau)
variable (hcardCenter : Nat.card (Subgroup.center X) = 3)
variable (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
variable (trivialRoles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
variable (faithfulRoles : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
  Fin 2 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = nu})
variable (L : TwoLocalOrdinaryBlockData (iota := iota) (R := R) (Rbar := Rbar)
  (tau := tau) (tauD := T.quotientAut) (hprimeTo := T.primeToCenter) (square := T.square)
  (roles := trivialRoles) (Sglobal := T.primitiveGlobal))
variable (small : SmallDefectNumericalSource iota hinj R)
variable (hDefectTrivial : ∀ j : Fin 4, ∃ H : Subgroup X,
  actualHasDefect R (trivialRoles j.succ).1 H ∧ Nat.card H =
    (if j = 0 then 4 else if j = 1 then 8 else 1))
variable (hDefectFaithful : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
  ∃ H : Subgroup X, actualHasDefect R (faithfulRoles nu hnu 1).1 H ∧ Nat.card H = 8)
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (C : ActualSectorOrdinaryRows iota hinj blocks D
  (1 : CentralSector (k := k) (X := X)) (Fin 108))
variable (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
variable (roots : SameIotaConductorRoot iota 10015005)
variable (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
  SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation.rawEvaluatedRows (iota.lift roots.source_root) r c)
variable (allocation : ∀ r : Fin 108, D.ordinaryBlock (C.character r) =
  (trivialRoles (printedBlockLabel r)).1)
variable (fusion : ∀ c : Fin 91, ∃ x : X, tau (A.representative c).1 =
  x * (A.representative (fullPerm c)).1 * x⁻¹)

open SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralCorrespondence
open SporadicFi24P3Definition44NamedCarrierFaithfulLiteralActualCount
open SporadicFi24P3Definition44NamedCarrierFaithfulSmallActualCount

variable (CF : ∀ nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1},
  ActualSectorOrdinaryRows iota hinj blocks D nu.1 (Fin 74))
variable (rootsF : {nu : CentralSector (k := k) (X := X) // nu ≠ 1} →
  SameIotaConductorRoot iota 770385)
variable (valuesF : ∀ (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1}) r c,
  ((CF nu).character r).1 (A.representative c).1 =
    SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation.rawEvaluatedRows
      (iota.lift (rootsF nu).source_root) r c)
variable (allocationF : ∀ (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1}) r,
  D.ordinaryBlock ((CF nu).character r) =
    (faithfulRoles nu.1 nu.2
      (SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData.faithfulPrintedBlockLabel r)).1)

include T F L compatibility decomposition hcardCenter hinverts small hDefectTrivial
  hDefectFaithful D C A roots hvalues allocation fusion CF rootsF valuesF allocationF

theorem exists_actual_equivariant_of_literal_brauer_values :
    ∃ Omega : IBr iota ≃ WeightClass (p := 2) (K := K) (X := X),
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi) := by
  have hBr25 : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = 25 := by
    intro nu hnu
    exact actualFaithfulSector_card_twentyFive_of_literal_values
      iota hinj blocks D ⟨nu, hnu⟩ (CF ⟨nu, hnu⟩) A
      (rootsF ⟨nu, hnu⟩) (valuesF ⟨nu, hnu⟩)
  have hBrSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
      Nat.card {phi : IBr iota //
        brauerBlock iota hinj blocks phi = (faithfulRoles nu hnu 1).1} = 2 := by
    intro nu hnu
    exact actualFaithfulSmallBlock_card_two_of_literal_values
      iota hinj blocks D ⟨nu, hnu⟩ (CF ⟨nu, hnu⟩)
      (faithfulRoles nu hnu) (allocationF ⟨nu, hnu⟩) A
      (rootsF ⟨nu, hnu⟩) (valuesF ⟨nu, hnu⟩)
  exact exists_actual_equivariant_of_literal_trivial_block_values
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) (Rbar := Rbar) (tau := tau)
    (T := T) (F := F) (compatibility := compatibility) (decomposition := decomposition)
    (hcardCenter := hcardCenter) (hinverts := hinverts) (trivialRoles := trivialRoles)
    (faithfulRoles := faithfulRoles) (L := L) (small := small) (hDefectTrivial := hDefectTrivial)
    (hDefectFaithful := hDefectFaithful) (D := D) (C := C) (A := A) (roots := roots)
    (hvalues := hvalues) (allocation := allocation) (fusion := fusion)
    (hBr25 := hBr25) (hBrSmall := hBrSmall)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllLiteralBrauerCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
