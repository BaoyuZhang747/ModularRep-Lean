import ModularRep.IBrSimpleModuleClass
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorRankCertificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRankEquality
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLiteralRank

/-! Actual trivial-sector total and fixed counts from the checked literal matrix. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLiteralActualCounts

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualSectorRankCertificate
open SporadicFi24P3Definition44NamedCarrierActualSectorBrauerAction
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion
open SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRankEquality
open SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierTrivialLiteralRank

universe u
variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem actualTrivialSector_card_fortyOne_of_literal_values
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (C : ActualSectorOrdinaryRows iota hinj blocks D
      (1 : CentralSector (k := k) (X := X)) (Fin 108))
    (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
    (roots : SameIotaConductorRoot iota 10015005)
    (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
      rawEvaluatedRows (iota.lift roots.source_root) r c) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1} = 41 := by
  have hvalues' : ∀ r c, (C.character r).1 (A.representative c).1 =
      rawEvaluatedRows (targetRoot iota roots) r c := by
    intro r c
    rw [targetRoot_eq_iota_lift_source iota roots]
    exact hvalues r c
  exact actualSector_card_of_certificate iota hinj blocks D 1 C A
    (rawEvaluatedRows (targetRoot iota roots)) hvalues' 41
    (sameIotaLiteralRankCertificate iota roots)

theorem actualTrivialSector_fixed_card_thirtyOne_of_literal_values
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (C : ActualSectorOrdinaryRows iota hinj blocks D
      (1 : CentralSector (k := k) (X := X)) (Fin 108))
    (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
    (roots : SameIotaConductorRoot iota 10015005)
    (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
      rawEvaluatedRows (iota.lift roots.source_root) r c)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (fusion : ∀ c : Fin 91, ∃ x : X,
      tau (A.representative c).1 = x * (A.representative (fullPerm c)).1 * x⁻¹) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1 ∧
      MulOpposite.op tau • phi = phi} = 31 := by
  classical
  let nu : CentralSector (k := k) (X := X) := 1
  have hnu : MulOpposite.op tau • nu = nu := by
    apply MonoidHom.ext
    intro z
    rfl
  let matrix : Fin 108 → Fin 91 → K := rawEvaluatedRows (targetRoot iota roots)
  have hvalues' : ∀ r c, (C.character r).1 (A.representative c).1 = matrix r c := by
    intro r c
    change (C.character r).1 (A.representative c).1 =
      rawEvaluatedRows (targetRoot iota roots) r c
    rw [targetRoot_eq_iota_lift_source iota roots]
    exact hvalues r c
  let I := ActualBrauerSector iota hinj blocks nu
  let V := actualSectorBrauerSpan iota hinj blocks nu
  let _ : Finite I := finiteIBrSubtype iota
    (fun phi => brauerSector iota hinj blocks phi = nu)
  let _ : Fintype I := Fintype.ofFinite I
  let b : Module.Basis I K V := actualSectorBrauerBasis iota hinj blocks nu
  let T : V →ₗ[K] V := actualSectorBrauerAction iota hinj blocks nu tau hnu
  have hmap : Function.Involutive (actualSectorBrauerMap iota hinj blocks nu tau hnu) :=
    actualSectorBrauerMap_involutive iota hinj blocks nu tau hnu decomposition
  let sigma : Equiv.Perm I :=
    hmap.toPerm (actualSectorBrauerMap iota hinj blocks nu tau hnu)
  have hsigma : Function.Involutive sigma := by
    intro phi
    exact hmap phi
  have hT : ∀ phi : I, T (b phi) = b (sigma phi) := by
    intro phi
    exact actualSectorBrauerAction_basis iota hinj blocks nu tau hnu phi
  let ordinary : Fin 108 → PrimeRegularFunction K X 2 :=
    actualSectorOrdinaryRestrictionRows iota hinj blocks D nu C
  have hmem (r : Fin 108) : ordinary r ∈ actualSectorBrauerSpan iota hinj blocks nu := by
    rw [← actualSectorOrdinaryRows_span iota hinj blocks D nu C]
    exact Submodule.subset_span (Set.mem_range_self r)
  let g : Fin 108 → V := fun r => ⟨ordinary r, hmem r⟩
  have hspan : Submodule.span K (Set.range g) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff
      (actualSectorBrauerSpan iota hinj blocks nu) hmem).mpr
        (actualSectorOrdinaryRows_span iota hinj blocks D nu C)
  let e : V ≃ₗ[K] Submodule.span K (Set.range matrix) :=
    actualSectorBrauerEvaluationEquiv iota hinj blocks D nu C A matrix hvalues'
  let E : V →ₗ[K] (Fin 91 → K) :=
    (Submodule.span K (Set.range matrix)).subtype.comp e.toLinearMap
  have hE : Function.Injective E := by
    intro f q h
    apply e.injective
    exact Subtype.ext h
  have hEval : ∀ r c, E (g r) c = matrix r c := by
    intro r c
    change (C.character r).1 (A.representative c).1 = matrix r c
    exact hvalues' r c
  have hAction : ∀ r c, E (T (g r)) c = matrix r (fullPerm c) := by
    intro r c
    exact (actualSectorBrauerEvaluationEquiv_action_apply
      iota hinj blocks D nu C A matrix hvalues' tau hnu fullPerm fusion (g r) c).trans
        (hEval r (fullPerm c))
  have hraw : Module.finrank K V = 41 :=
    e.finrank_eq.trans (sameIotaLiteralRankCertificate iota roots).rows_finrank
  have hplus : Module.finrank K (LinearMap.range (LinearMap.id + T)) = 36 :=
    (finrank_range_id_add_eq_symmetrizedRows
      g hspan E hE T matrix fullPerm hEval hAction).trans
        (literal_plus_rows_finrank (targetRoot iota roots) (targetRoot_isPrimitive iota roots))
  have hfixed : Nat.card (Function.fixedPoints sigma) = 31 :=
    fixed_card_eq_thirty_one_of_ranks b T sigma hT hsigma hraw hplus
  let fixedEquiv : Function.fixedPoints sigma ≃
      {phi : IBr iota // brauerSector iota hinj blocks phi = nu ∧
        MulOpposite.op tau • phi = phi} :=
    actualSectorBrauerFixedEquiv iota hinj blocks nu tau hnu
  exact (Nat.card_congr fixedEquiv.symm).trans hfixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLiteralActualCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
