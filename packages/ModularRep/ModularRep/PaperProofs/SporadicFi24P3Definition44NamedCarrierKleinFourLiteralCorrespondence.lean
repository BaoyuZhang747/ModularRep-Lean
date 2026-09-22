import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorSmallDefectCorrespondence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLiteralActualCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourActualCounts

/-! The original equivariant correspondence with trivial-sector and Klein-four
Brauer counts derived from literal ordinary values. Other specified blocks and
the local weight-side sources retain their explicit lower hypotheses. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourLiteralCorrespondence

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
  rawEvaluatedRows (iota.lift roots.source_root) r c)
variable (allocation : ∀ r : Fin 108, D.ordinaryBlock (C.character r) =
  (trivialRoles (printedBlockLabel r)).1)
variable (fusion : ∀ c : Fin 91, ∃ x : X, tau (A.representative c).1 =
  x * (A.representative (fullPerm c)).1 * x⁻¹)
variable (hBrRest : ∀ j : Fin 3,
  actualBrauerSignature iota hinj blocks tau (trivialRoles j.succ.succ).1 =
    nonprincipalSignature j.succ)
variable (hBr25 : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
  Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = 25)
variable (hBrSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
  Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (faithfulRoles nu hnu 1).1} = 2)

include T F L compatibility decomposition hcardCenter hinverts small hDefectTrivial
  hDefectFaithful D C A roots hvalues allocation fusion hBrRest hBr25 hBrSmall

theorem exists_actual_equivariant_of_literal_trivial_and_kleinFour_values :
    ∃ Omega : IBr iota ≃ WeightClass (p := 2) (K := K) (X := X),
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi) := by
  have hBr41 := actualTrivialSector_card_fortyOne_of_literal_values
    iota hinj blocks D C A roots hvalues
  have hBr31 := actualTrivialSector_fixed_card_thirtyOne_of_literal_values
    iota hinj blocks D C A roots hvalues tau decomposition fusion
  have hK4 : actualBrauerSignature iota hinj blocks tau (trivialRoles 1).1 = (3, 1) := by
    apply Prod.ext
    · exact actualKleinFourBlock_card_three_of_literal_values
        iota hinj blocks D C trivialRoles allocation A roots hvalues
    · exact actualKleinFourBlock_fixed_card_one_of_literal_values
        iota hinj blocks D C trivialRoles allocation A roots hvalues tau decomposition fusion
  have hBrOther : ∀ j : Fin 4,
      actualBrauerSignature iota hinj blocks tau (trivialRoles j.succ).1 =
        nonprincipalSignature j := by
    refine Fin.cases ?_ ?_
    · simpa [nonprincipalSignature] using hK4
    · intro j
      exact hBrRest j
  exact exists_actual_equivariant_of_ordinary_tables_and_small_defect
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) (Rbar := Rbar) (tau := tau)
    (T := T) (F := F) (compatibility := compatibility) (decomposition := decomposition)
    (hcardCenter := hcardCenter) (hinverts := hinverts) (trivialRoles := trivialRoles)
    (faithfulRoles := faithfulRoles) (L := L) (small := small) (hDefectTrivial := hDefectTrivial)
    (hDefectFaithful := hDefectFaithful) (hBr41 := hBr41) (hBr31 := hBr31)
    (hBrOther := hBrOther) (hBr25 := hBr25) (hBrSmall := hBrSmall)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourLiteralCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
