import ModularRep.IBrSimpleModuleClass
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockBrauerAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRankEquality
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank
import ModularRep.PaperProofs.SporadicFi24P3V3RawRankCertificate

/-! The actual nonprincipal Brauer signature from the six ordinary rows.
Literal row values and fusion bind the finite replay to the specified block;
neither a rank nor a Brauer cardinality is supplied. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualBlockBrauerAction
open SporadicFi24P3Definition44NamedCarrierSymmetrizedRowRankEquality
open SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank
open SporadicFi24P3V3RawRankCertificate
open SporadicFi24P3PlusRankReplayContract

universe u
variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (b : ActualBlock (k := k) (X := X))
variable (selected : Fin 6 → OrdinaryIrreducibleCharacter.Irr K X)
variable (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
variable (A : PrimeRegularRepresentativeCover 3 X (Fin 30))
variable (encoding : PrimitiveTwentyNineEncoding K)
variable (V3 : CanonicalSupplementV3Binding encoding)
variable (hvalues : ∀ r c,
  (selected r).1 (A.representative c).1 = V3.restrictionRows r c)

include hcomplete hvalues

theorem actual_b1_card_four :
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} = 4 :=
  actualBlock_card_of_certificate iota hinj blocks D b selected hcomplete
    A V3.restrictionRows hvalues 4 V3.rawPacket.rankCertificate

theorem actual_b1_fixed_card_two
    (tau : MulAut X) (hb : MulOpposite.op tau • b = b)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (fusion : ∀ c : Fin 30, ∃ x : X,
      tau (A.representative c).1 =
        x * (A.representative (regularOuterPermutation c)).1 * x⁻¹) :
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b ∧
      MulOpposite.op tau • phi = phi} = 2 := by
  classical
  have closed : ∀ phi : IBr iota, brauerBlock iota hinj blocks phi = b →
      brauerBlock iota hinj blocks (MulOpposite.op tau • phi) = b := by
    intro phi hphi
    rw [brauerBlock_transport iota hinj blocks, hphi, hb]
  let I := ActualBrauerBlock iota hinj blocks b
  let V := actualBlockBrauerSpan iota hinj blocks b
  let _ : Finite I := finiteIBrSubtype iota
    (fun phi => brauerBlock iota hinj blocks phi = b)
  let _ : Fintype I := Fintype.ofFinite I
  let basis : Module.Basis I K V := actualBlockBrauerBasis iota hinj blocks b
  let T : V →ₗ[K] V := actualBlockBrauerAction iota hinj blocks b tau closed
  have hmap : Function.Involutive
      (actualBlockBrauerMap iota hinj blocks b tau closed) :=
    actualBlockBrauerMap_involutive iota hinj blocks b tau closed decomposition
  let sigma : Equiv.Perm I :=
    hmap.toPerm (actualBlockBrauerMap iota hinj blocks b tau closed)
  have hsigma : Function.Involutive sigma := by
    intro phi
    exact hmap phi
  have hT : ∀ phi : I, T (basis phi) = basis (sigma phi) := by
    intro phi
    exact actualBlockBrauerAction_basis iota hinj blocks b tau closed phi
  let ordinary : Fin 6 → PrimeRegularFunction K X 3 :=
    fun r => actualOrdinaryRestriction (p := 3) (selected r)
  have hmem (r : Fin 6) : ordinary r ∈ actualBlockBrauerSpan iota hinj blocks b := by
    rw [← actualBlockOrdinaryRows_span iota hinj blocks D b selected hcomplete]
    exact Submodule.subset_span (Set.mem_range_self r)
  let g : Fin 6 → V := fun r => ⟨ordinary r, hmem r⟩
  have hspan : Submodule.span K (Set.range g) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff
      (actualBlockBrauerSpan iota hinj blocks b) hmem).mpr
        (actualBlockOrdinaryRows_span iota hinj blocks D b selected hcomplete)
  let matrix := V3.restrictionRows
  let e : V ≃ₗ[K] Submodule.span K (Set.range matrix) :=
    actualBlockBrauerEvaluationEquiv iota hinj blocks D b selected hcomplete
      A matrix hvalues
  let E : V →ₗ[K] (Fin 30 → K) :=
    (Submodule.span K (Set.range matrix)).subtype.comp e.toLinearMap
  have hE : Function.Injective E := by
    intro f q h
    apply e.injective
    exact Subtype.ext h
  have hEval : ∀ r c, E (g r) c = matrix r c := by
    intro r c
    change (selected r).1 (A.representative c).1 = matrix r c
    exact hvalues r c
  have hAction : ∀ r c, E (T (g r)) c = matrix r (regularOuterPermutation c) := by
    intro r c
    exact (actualBlockBrauerEvaluationEquiv_action_apply
      iota hinj blocks b tau closed D selected hcomplete A matrix hvalues
      regularOuterPermutation fusion (g r) c).trans (hEval r (regularOuterPermutation c))
  have hraw : Module.finrank K V = 4 :=
    e.finrank_eq.trans V3.rawPacket.rows_finrank_eq_four
  have hplusRows :
      Module.finrank K (Submodule.span K (Set.range fun r c =>
        matrix r c + matrix r (regularOuterPermutation c))) = 3 := by
    have heq : (fun r c => matrix r c + matrix r (regularOuterPermutation c)) =
        replayedPlusRows (K := K) := by
      funext r c
      exact V3.symmetrised_rows_eq r c
    rw [heq]
    exact replayedPlusRows_finrank_eq_three
  have hplus : Module.finrank K (LinearMap.range (LinearMap.id + T)) = 3 :=
    (finrank_range_id_add_eq_symmetrizedRows g hspan E hE T matrix
      regularOuterPermutation hEval hAction).trans hplusRows
  have hcard : Nat.card I = 4 := (Module.finrank_eq_nat_card_basis basis).symm.trans hraw
  have hfixed : Nat.card (Function.fixedPoints sigma) = 2 := by
    have h := fixed_card_add_card_eq_two_mul_plus_rank basis T sigma hT hsigma
    rw [hcard, hplus] at h
    omega
  let fixedEquiv : Function.fixedPoints sigma ≃
      {phi : IBr iota // brauerBlock iota hinj blocks phi = b ∧
        MulOpposite.op tau • phi = phi} :=
    actualBlockBrauerFixedEquiv iota hinj blocks b tau closed
  exact (Nat.card_congr fixedEquiv.symm).trans hfixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3NonprincipalBrauerSignature


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
