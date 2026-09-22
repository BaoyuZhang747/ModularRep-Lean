import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierClassFunctionRowsPullback

/-! Fixed ordinary regular restrictions imply pointwise fixedness of the actual Brauer fibre. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockBrauerFixedRows

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierClassFunctionRowsPullback

universe u v w

theorem pullback_eq_self_of_mem_classFunctionRowSpan
    {p : ℕ} {K X : Type u} {Row : Type v} [Field K] [Group X]
    (rows : Row → PrimeRegularClassFunction K X p) (tau : MulAut X)
    (hrows : ∀ r, (rows r).twist tau = rows r)
    (f : PrimeRegularFunction K X p) (hf : f ∈ classFunctionRowSpan rows) :
    regularPullbackLinear tau f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨r, rfl⟩ := hf
      exact congrArg PrimeRegularClassFunction.toFun (hrows r)
  | zero => exact (regularPullbackLinear tau).map_zero
  | add f g hf hg ihf ihg => rw [map_add, ihf, ihg]
  | smul a f hf ih => rw [map_smul, ih]

variable {p : ℕ} {k K X BlockIndex : Type u} {Row : Type v} {Column : Type w}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (b : ActualBlock (k := k) (X := X)) (tau : MulAut X)

theorem actualBlockBrauer_fixed_of_ordinary_values
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (selected : Row → OrdinaryIrreducibleCharacter.Irr K X)
    (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, (selected r).1 (A.representative c).1 = matrix r c)
    (perm : Equiv.Perm Column)
    (fusion : ∀ c, ∃ x : X, tau (A.representative c).1 =
      x * (A.representative (perm c)).1 * x⁻¹)
    (hmatrix : ∀ r c, matrix r (perm c) = matrix r c) :
    ∀ phi : IBr iota, brauerBlock iota hinj blocks phi = b →
      MulOpposite.op tau • phi = phi := by
  let rows : Row → PrimeRegularClassFunction K X p :=
    fun r => ordinaryRestrictionClassFunction (p := p) (selected r)
  have hspan : classFunctionRowSpan rows = actualBlockBrauerSpan iota hinj blocks b :=
    actualBlockOrdinaryRows_span iota hinj blocks D b selected hcomplete
  have hrows : ∀ r, (rows r).twist tau = rows r :=
    classFunctionRows_twist_of_values A rows matrix hvalues tau perm fusion id hmatrix
  intro phi hphi
  have hf : actualBrauerFunction iota phi ∈ classFunctionRowSpan rows := by
    rw [hspan]
    exact Submodule.subset_span ⟨⟨phi, hphi⟩, rfl⟩
  apply (irreducibleBrauerCharacters_linearIndependent iota).injective
  exact pullback_eq_self_of_mem_classFunctionRowSpan rows tau hrows
    (actualBrauerFunction iota phi) hf

theorem actualBlock_fixed_card_eq_card_of_pointwise_fixed
    (hfixed : ∀ phi : IBr iota, brauerBlock iota hinj blocks phi = b →
      MulOpposite.op tau • phi = phi) :
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b ∧
      MulOpposite.op tau • phi = phi} =
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} := by
  let E : {phi : IBr iota // brauerBlock iota hinj blocks phi = b ∧
      MulOpposite.op tau • phi = phi} ≃
      {phi : IBr iota // brauerBlock iota hinj blocks phi = b} := {
    toFun := fun phi => ⟨phi.1, phi.2.1⟩
    invFun := fun phi => ⟨phi.1, phi.2, hfixed phi.1 phi.2⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl }
  exact Nat.card_congr E

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockBrauerFixedRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
