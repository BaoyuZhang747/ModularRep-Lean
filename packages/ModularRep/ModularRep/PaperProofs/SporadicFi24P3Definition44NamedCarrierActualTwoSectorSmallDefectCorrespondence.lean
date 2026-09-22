import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData

/-!
# All original weight counts and the correspondence from ordinary data

Global ordinary tables, two local ordinary catalogues and the guarded
small-defect numerical theorem supply all weight-side counts internally.
The Brauer counts and their specified dictionaries remain explicit.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorSmallDefectCorrespondence

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
variable (hBr41 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1} = 41)
variable (hBr31 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1 ∧
  MulOpposite.op tau • phi = phi} = 31)
variable (hBrOther : ∀ j : Fin 4,
  actualBrauerSignature iota hinj blocks tau (trivialRoles j.succ).1 = nonprincipalSignature j)
variable (hBr25 : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
  Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = 25)
variable (hBrSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
  Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (faithfulRoles nu hnu 1).1} = 2)

include T F L compatibility decomposition hcardCenter hinverts small hDefectTrivial hDefectFaithful
  hBr41 hBr31 hBrOther hBr25 hBrSmall

theorem actual_counts_and_finite_of_ordinary_tables_and_small_defect :
    ActualBlockC2Counts iota hinj R tau ∧ Finite (WeightClass (p := 2) (K := K) (X := X)) := by
  have hWtOther := nonprincipal_weight_signatures_of_two_local_ordinary_data
    (iota := iota) (R := R) (Rbar := Rbar) (tau := tau) (tauD := T.quotientAut)
    (hprimeTo := T.primeToCenter) (square := T.square) (roles := trivialRoles)
    (Sglobal := T.primitiveGlobal) (hinj := hinj) (blocks := blocks)
    L compatibility decomposition hBrOther small hDefectTrivial
  have hWtSmall := faithful_small_weight_totals iota hinj blocks R small
    faithfulRoles hDefectFaithful hBrSmall
  have hWtTrivial := actualTrivialSectorCounts_of_table8
    (R := R) (iota := iota) (hprimeTo := T.primeToCenter)
    (C := T.catalogue) (OD := T.operationsD) (CU := T.reductionU) (CD := T.reductionD)
    (compatU := compatibility) (compatD := T.compatibilityD)
    (Sglobal := T.primitiveGlobal) (Slocal := T.primitiveLocal)
    (tau := tau) (tauD := T.quotientAut) (square := T.square)
    T.classesFixed T.entry T.table T.total T.fixed
  have hWtFaithful := allFaithfulSectorCounts_of_table8
    (iota := iota) (R := R) (nu0 := F.nu0) (C := F.catalogue)
    (CU := F.reduction) (compatibility := compatibility)
    tau hinverts hcardCenter F.nontrivial F.table
  exact ⟨actualBlockC2Counts_of_five_and_two_block_data
    iota hinj blocks R tau hcardCenter hinverts trivialRoles faithfulRoles
    hBr41 hBr31 hWtTrivial.1 hWtTrivial.2 hBrOther hWtOther hBr25 hWtFaithful hBrSmall hWtSmall,
    weight_finite_of_sector_counts R hWtTrivial.1 hWtFaithful⟩

theorem exists_actual_equivariant_of_ordinary_tables_and_small_defect :
    ∃ Omega : IBr iota ≃ WeightClass (p := 2) (K := K) (X := X),
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi) := by
  have result := actual_counts_and_finite_of_ordinary_tables_and_small_defect
    (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) (Rbar := Rbar) (tau := tau)
    (T := T) (F := F) (compatibility := compatibility) (decomposition := decomposition)
    (hcardCenter := hcardCenter) (hinverts := hinverts) (trivialRoles := trivialRoles)
    (faithfulRoles := faithfulRoles) (L := L) (small := small) (hDefectTrivial := hDefectTrivial)
    (hDefectFaithful := hDefectFaithful) (hBr41 := hBr41) (hBr31 := hBr31)
    (hBrOther := hBrOther) (hBr25 := hBr25) (hBrSmall := hBrSmall)
  let _ : Finite (WeightClass (p := 2) (K := K) (X := X)) := result.2
  exact exists_actual_equivariant_of_counts iota hinj R tau decomposition result.1

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoSectorSmallDefectCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
