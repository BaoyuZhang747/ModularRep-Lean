import ModularRep.IBrSimpleModuleClass
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRank
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank

/-!
# Actual sector fixed counts from raw matrix certificates

Ordinary generators, spanning, coordinate injection, action compatibility,
the Brauer basis permutation and fixed-subtype identification are derived.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorFixedRankCertificate

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualSectorBrauerAction
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion
open SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRank
open SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank

universe u v w
variable {p : ℕ} {k K X BlockIndex : Type u}
variable {Row : Type v} {Column : Type w}
variable [Field k] [Field K]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem actualSector_fixed_card_of_certificates
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : CentralSector (k := k) (X := X))
    (C : ActualSectorOrdinaryRows iota hinj blocks D nu Row)
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 = matrix r c)
    (tau : MulAut X) (hnu : MulOpposite.op tau • nu = nu)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (perm : Equiv.Perm Column)
    (fusion : ∀ c : Column, ∃ x : X,
      tau (A.representative c).1 = x * (A.representative (perm c)).1 * x⁻¹)
    (rawCertificate : FiniteRowRankCertificate K matrix 41)
    (plusCertificate : FiniteRowRankCertificate K
      (fun r c => matrix r c + matrix r (perm c)) 36) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu ∧
      MulOpposite.op tau • phi = phi} = 31 := by
  classical
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
  let ordinary : Row → PrimeRegularFunction K X p :=
    actualSectorOrdinaryRestrictionRows iota hinj blocks D nu C
  have hmem (r : Row) : ordinary r ∈ actualSectorBrauerSpan iota hinj blocks nu := by
    rw [← actualSectorOrdinaryRows_span iota hinj blocks D nu C]
    exact Submodule.subset_span (Set.mem_range_self r)
  let g : Row → V := fun r => ⟨ordinary r, hmem r⟩
  have hspan : Submodule.span K (Set.range g) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff
      (actualSectorBrauerSpan iota hinj blocks nu) hmem).mpr
        (actualSectorOrdinaryRows_span iota hinj blocks D nu C)
  let e : V ≃ₗ[K] Submodule.span K (Set.range matrix) :=
    actualSectorBrauerEvaluationEquiv iota hinj blocks D nu C A matrix hvalues
  let E : V →ₗ[K] (Column → K) :=
    (Submodule.span K (Set.range matrix)).subtype.comp e.toLinearMap
  have hE : Function.Injective E := by
    intro f q h
    apply e.injective
    exact Subtype.ext h
  have hEval : ∀ r c, E (g r) c = matrix r c := by
    intro r c
    change (C.character r).1 (A.representative c).1 = matrix r c
    exact hvalues r c
  have hAction : ∀ r c, E (T (g r)) c = matrix r (perm c) := by
    intro r c
    exact (actualSectorBrauerEvaluationEquiv_action_apply
      iota hinj blocks D nu C A matrix hvalues tau hnu perm fusion (g r) c).trans
        (hEval r (perm c))
  have hraw : Module.finrank K V = 41 :=
    e.finrank_eq.trans rawCertificate.rows_finrank
  have hplus : Module.finrank K (LinearMap.range (LinearMap.id + T)) = 36 :=
    finrank_range_id_add_eq_of_certificate g hspan E hE T matrix perm hEval hAction plusCertificate
  have hfixed : Nat.card (Function.fixedPoints sigma) = 31 :=
    fixed_card_eq_thirty_one_of_ranks b T sigma hT hsigma hraw hplus
  let fixedEquiv : Function.fixedPoints sigma ≃
      {phi : IBr iota // brauerSector iota hinj blocks phi = nu ∧
        MulOpposite.op tau • phi = phi} :=
    actualSectorBrauerFixedEquiv iota hinj blocks nu tau hnu
  exact (Nat.card_congr fixedEquiv.symm).trans hfixed

/-- Trivial-sector stability is derived here as well. -/
theorem actualTrivialSector_fixed_card_of_certificates
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (C : ActualSectorOrdinaryRows iota hinj blocks D
      (1 : CentralSector (k := k) (X := X)) Row)
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, (C.character r).1 (A.representative c).1 = matrix r c)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (perm : Equiv.Perm Column)
    (fusion : ∀ c : Column, ∃ x : X,
      tau (A.representative c).1 = x * (A.representative (perm c)).1 * x⁻¹)
    (rawCertificate : FiniteRowRankCertificate K matrix 41)
    (plusCertificate : FiniteRowRankCertificate K
      (fun r c => matrix r c + matrix r (perm c)) 36) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1 ∧
      MulOpposite.op tau • phi = phi} = 31 := by
  have hone : MulOpposite.op tau • (1 : CentralSector (k := k) (X := X)) = 1 := by
    apply MonoidHom.ext
    intro z
    rfl
  exact actualSector_fixed_card_of_certificates iota hinj blocks D 1 C A matrix hvalues
    tau hone decomposition perm fusion rawCertificate plusCertificate

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorFixedRankCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
