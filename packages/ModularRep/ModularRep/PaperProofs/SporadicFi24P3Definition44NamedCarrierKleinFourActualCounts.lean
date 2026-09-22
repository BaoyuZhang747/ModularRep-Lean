import ModularRep.IBrSimpleModuleClass
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockBrauerAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRankEquality
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourLiteralRank
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

/-! The actual specified Klein-four block has three Brauer characters, one fixed by tau,
from the original full trivial-sector values and literal ordinary block allocation. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourActualCounts

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualBlockBrauerAction
open SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRankEquality
open SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
open SporadicFi24P3Definition44NamedCarrierKleinFourLiteralRank
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

universe u
variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (C : ActualSectorOrdinaryRows iota hinj blocks D
  (1 : CentralSector (k := k) (X := X)) (Fin 108))
variable (trivialRoles : Fin 5 ≃
  {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
variable (allocation : ∀ r, D.ordinaryBlock (C.character r) =
  (trivialRoles (printedBlockLabel r)).1)
variable (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
variable (roots : SameIotaConductorRoot iota 10015005)
variable (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
  rawEvaluatedRows (iota.lift roots.source_root) r c)

include allocation hvalues

theorem actualKleinFourBlock_card_three_of_literal_values :
    Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = (trivialRoles 1).1} = 3 := by
  let selected : Fin 4 → OrdinaryIrreducibleCharacter.Irr K X :=
    fun r => C.character (selectedRow r)
  have hcomplete : ∀ chi, D.ordinaryBlock chi = (trivialRoles 1).1 ↔
      ∃ r, selected r = chi :=
    blockRows_complete_of_trivial_allocation iota hinj blocks D C trivialRoles
      printedBlockLabel allocation selectedRow selected_fibre
  have hvalues' : ∀ r c, (selected r).1 (A.representative c).1 = integerRows r c := by
    intro r c
    exact (hvalues (selectedRow r) c).trans
      (selected_raw_eq_integer (iota.lift roots.source_root) r c)
  exact actualBlock_card_of_certificate iota hinj blocks D (trivialRoles 1).1
    selected hcomplete A integerRows hvalues' 3 (rankCertificate integerRawCertificate)

theorem actualKleinFourBlock_fixed_card_one_of_literal_values
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (fusion : ∀ c : Fin 91, ∃ x : X,
      tau (A.representative c).1 = x * (A.representative (fullPerm c)).1 * x⁻¹) :
    Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = (trivialRoles 1).1 ∧
      MulOpposite.op tau • phi = phi} = 1 := by
  classical
  let physical := (trivialRoles 1).1
  let selected : Fin 4 → OrdinaryIrreducibleCharacter.Irr K X :=
    fun r => C.character (selectedRow r)
  have hcomplete : ∀ chi, D.ordinaryBlock chi = physical ↔ ∃ r, selected r = chi :=
    blockRows_complete_of_trivial_allocation iota hinj blocks D C trivialRoles
      printedBlockLabel allocation selectedRow selected_fibre
  let matrix : Fin 4 → Fin 91 → K := integerRows
  have hvalues' : ∀ r c, (selected r).1 (A.representative c).1 = matrix r c := by
    intro r c
    exact (hvalues (selectedRow r) c).trans
      (selected_raw_eq_integer (iota.lift roots.source_root) r c)
  have closed : ∀ phi : IBr iota, brauerBlock iota hinj blocks phi = physical →
      brauerBlock iota hinj blocks (MulOpposite.op tau • phi) = physical :=
    actualBlockBrauer_closed_of_ordinary_values iota hinj blocks physical tau
      D selected hcomplete A matrix hvalues' fullPerm fusion rowImage integerRows_action
  let I := ActualBrauerBlock iota hinj blocks physical
  let V := actualBlockBrauerSpan iota hinj blocks physical
  let _ : Finite I := finiteIBrSubtype iota
    (fun phi => brauerBlock iota hinj blocks phi = physical)
  let _ : Fintype I := Fintype.ofFinite I
  let b : Module.Basis I K V := actualBlockBrauerBasis iota hinj blocks physical
  let T : V →ₗ[K] V := actualBlockBrauerAction iota hinj blocks physical tau closed
  have hmap : Function.Involutive
      (actualBlockBrauerMap iota hinj blocks physical tau closed) :=
    actualBlockBrauerMap_involutive iota hinj blocks physical tau closed decomposition
  let sigma : Equiv.Perm I :=
    hmap.toPerm (actualBlockBrauerMap iota hinj blocks physical tau closed)
  have hsigma : Function.Involutive sigma := by
    intro phi
    exact hmap phi
  have hT : ∀ phi : I, T (b phi) = b (sigma phi) := by
    intro phi
    exact actualBlockBrauerAction_basis iota hinj blocks physical tau closed phi
  let ordinary : Fin 4 → PrimeRegularFunction K X 2 :=
    fun r => actualOrdinaryRestriction (p := 2) (selected r)
  have hmem (r : Fin 4) : ordinary r ∈ actualBlockBrauerSpan iota hinj blocks physical := by
    rw [← actualBlockOrdinaryRows_span iota hinj blocks D physical selected hcomplete]
    exact Submodule.subset_span (Set.mem_range_self r)
  let g : Fin 4 → V := fun r => ⟨ordinary r, hmem r⟩
  have hspan : Submodule.span K (Set.range g) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff
      (actualBlockBrauerSpan iota hinj blocks physical) hmem).mpr
        (actualBlockOrdinaryRows_span iota hinj blocks D physical selected hcomplete)
  let e : V ≃ₗ[K] Submodule.span K (Set.range matrix) :=
    actualBlockBrauerEvaluationEquiv iota hinj blocks D physical selected hcomplete
      A matrix hvalues'
  let E : V →ₗ[K] (Fin 91 → K) :=
    (Submodule.span K (Set.range matrix)).subtype.comp e.toLinearMap
  have hE : Function.Injective E := by
    intro f q h
    apply e.injective
    exact Subtype.ext h
  have hEval : ∀ r c, E (g r) c = matrix r c := by
    intro r c
    change (selected r).1 (A.representative c).1 = matrix r c
    exact hvalues' r c
  have hAction : ∀ r c, E (T (g r)) c = matrix r (fullPerm c) := by
    intro r c
    exact (actualBlockBrauerEvaluationEquiv_action_apply
      iota hinj blocks physical tau closed D selected hcomplete A matrix hvalues'
      fullPerm fusion (g r) c).trans (hEval r (fullPerm c))
  have hraw : Module.finrank K V = 3 := e.finrank_eq.trans integer_rows_finrank
  have hplus : Module.finrank K (LinearMap.range (LinearMap.id + T)) = 2 :=
    (finrank_range_id_add_eq_symmetrizedRows
      g hspan E hE T matrix fullPerm hEval hAction).trans integer_plus_rows_finrank
  have hcard : Nat.card I = 3 := (Module.finrank_eq_nat_card_basis b).symm.trans hraw
  have hfixed : Nat.card (Function.fixedPoints sigma) = 1 := by
    have h := fixed_card_add_card_eq_two_mul_plus_rank b T sigma hT hsigma
    rw [hcard, hplus] at h
    omega
  let fixedEquiv : Function.fixedPoints sigma ≃
      {phi : IBr iota // brauerBlock iota hinj blocks phi = physical ∧
        MulOpposite.op tau • phi = phi} :=
    actualBlockBrauerFixedEquiv iota hinj blocks physical tau closed
  exact (Nat.card_congr fixedEquiv.symm).trans hfixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourActualCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
