import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierClassFunctionRowsPullback

/-! Actual block fibre/action stability derived from ordinary row values and fusion. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockBrauerAction

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion
open SporadicFi24P3Definition44NamedCarrierActualTwoActions
open SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierClassFunctionRowsPullback

universe u v w
variable {p : ℕ} {k K X BlockIndex : Type u} {Row : Type v} {Column : Type w}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (b : ActualBlock (k := k) (X := X)) (tau : MulAut X)

theorem actualBlockBrauer_closed_of_ordinary_values
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (selected : Row → OrdinaryIrreducibleCharacter.Irr K X)
    (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, (selected r).1 (A.representative c).1 = matrix r c)
    (perm : Equiv.Perm Column)
    (fusion : ∀ c, ∃ x : X, tau (A.representative c).1 =
      x * (A.representative (perm c)).1 * x⁻¹)
    (s : Row → Row) (hmatrix : ∀ r c, matrix r (perm c) = matrix (s r) c) :
    ∀ phi : IBr iota, brauerBlock iota hinj blocks phi = b →
      brauerBlock iota hinj blocks (MulOpposite.op tau • phi) = b := by
  let rows : Row → PrimeRegularClassFunction K X p :=
    fun r => ordinaryRestrictionClassFunction (p := p) (selected r)
  have hspan : classFunctionRowSpan rows = actualBlockBrauerSpan iota hinj blocks b :=
    actualBlockOrdinaryRows_span iota hinj blocks D b selected hcomplete
  have hrows : ∀ r, (rows r).twist tau = rows (s r) :=
    classFunctionRows_twist_of_values A rows matrix hvalues tau perm fusion s hmatrix
  intro phi hphi
  apply label_eq_of_mem_blockSpan
    (actualBrauerFunction iota) (brauerBlock iota hinj blocks) b
    (irreducibleBrauerCharacters_linearIndependent iota) (MulOpposite.op tau • phi)
  have hf : actualBrauerFunction iota phi ∈ classFunctionRowSpan rows := by
    rw [hspan]
    exact Submodule.subset_span ⟨⟨phi, hphi⟩, rfl⟩
  have ht := pullback_mem_classFunctionRowSpan rows tau s hrows (actualBrauerFunction iota phi) hf
  rw [hspan] at ht
  exact ht

variable (closed : ∀ phi : IBr iota, brauerBlock iota hinj blocks phi = b →
  brauerBlock iota hinj blocks (MulOpposite.op tau • phi) = b)

def actualBlockBrauerMap : ActualBrauerBlock iota hinj blocks b →
    ActualBrauerBlock iota hinj blocks b :=
  fun phi => ⟨MulOpposite.op tau • phi.1, closed phi.1 phi.2⟩

@[simp]
theorem actualBlockBrauerMap_apply_val (phi : ActualBrauerBlock iota hinj blocks b) :
    (actualBlockBrauerMap iota hinj blocks b tau closed phi).1 =
      MulOpposite.op tau • phi.1 := rfl

theorem actualBlockBrauerMap_fixed_iff (phi : ActualBrauerBlock iota hinj blocks b) :
    actualBlockBrauerMap iota hinj blocks b tau closed phi = phi ↔
      MulOpposite.op tau • phi.1 = phi.1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

def actualBlockBrauerFixedEquiv :
    {phi : ActualBrauerBlock iota hinj blocks b //
      actualBlockBrauerMap iota hinj blocks b tau closed phi = phi} ≃
    {phi : IBr iota // brauerBlock iota hinj blocks phi = b ∧
      MulOpposite.op tau • phi = phi} :=
  (Equiv.subtypeEquivRight
    (actualBlockBrauerMap_fixed_iff iota hinj blocks b tau closed)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun phi : IBr iota => brauerBlock iota hinj blocks phi = b)
        (fun phi : IBr iota => MulOpposite.op tau • phi = phi))

def actualBlockBrauerAction :
    actualBlockBrauerSpan iota hinj blocks b →ₗ[K]
      actualBlockBrauerSpan iota hinj blocks b :=
  (actualBlockBrauerBasis iota hinj blocks b).constr K
    (fun phi => actualBlockBrauerBasis iota hinj blocks b
      (actualBlockBrauerMap iota hinj blocks b tau closed phi))

@[simp]
theorem actualBlockBrauerAction_basis (phi : ActualBrauerBlock iota hinj blocks b) :
    actualBlockBrauerAction iota hinj blocks b tau closed
        (actualBlockBrauerBasis iota hinj blocks b phi) =
      actualBlockBrauerBasis iota hinj blocks b
        (actualBlockBrauerMap iota hinj blocks b tau closed phi) := by
  simp only [actualBlockBrauerAction, Module.Basis.constr_basis]

theorem coe_actualBlockBrauerAction_apply
    (f : actualBlockBrauerSpan iota hinj blocks b) :
    ((actualBlockBrauerAction iota hinj blocks b tau closed f :
      actualBlockBrauerSpan iota hinj blocks b) : PrimeRegularFunction K X p) =
      f.1.pullback tau.toMonoidHom := by
  let P : PrimeRegularFunction K X p →ₗ[K] PrimeRegularFunction K X p := {
    toFun := fun g => g.pullback tau.toMonoidHom
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have h : (actualBlockBrauerSpan iota hinj blocks b).subtype.comp
      (actualBlockBrauerAction iota hinj blocks b tau closed) =
      P.comp (actualBlockBrauerSpan iota hinj blocks b).subtype := by
    apply (actualBlockBrauerBasis iota hinj blocks b).ext
    intro phi
    change ((actualBlockBrauerAction iota hinj blocks b tau closed
        (actualBlockBrauerBasis iota hinj blocks b phi) :
          actualBlockBrauerSpan iota hinj blocks b) : PrimeRegularFunction K X p) =
      ((actualBlockBrauerBasis iota hinj blocks b phi :
        actualBlockBrauerSpan iota hinj blocks b) : PrimeRegularFunction K X p).pullback
          tau.toMonoidHom
    rw [actualBlockBrauerAction_basis, coe_actualBlockBrauerBasis_apply,
      coe_actualBlockBrauerBasis_apply]
    rfl
  exact congrArg (fun L : actualBlockBrauerSpan iota hinj blocks b →ₗ[K]
    PrimeRegularFunction K X p => L f) h

theorem actualBlockBrauerEvaluationEquiv_action_apply
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (selected : Row → OrdinaryIrreducibleCharacter.Irr K X)
    (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, (selected r).1 (A.representative c).1 = matrix r c)
    (perm : Equiv.Perm Column)
    (fusion : ∀ c, ∃ x : X, tau (A.representative c).1 =
      x * (A.representative (perm c)).1 * x⁻¹)
    (f : actualBlockBrauerSpan iota hinj blocks b) (c : Column) :
    ((actualBlockBrauerEvaluationEquiv iota hinj blocks D b selected hcomplete A matrix hvalues
        (actualBlockBrauerAction iota hinj blocks b tau closed f) :
          Submodule.span K (Set.range matrix)) : Column → K) c =
      ((actualBlockBrauerEvaluationEquiv iota hinj blocks D b selected hcomplete A matrix hvalues f :
        Submodule.span K (Set.range matrix)) : Column → K) (perm c) := by
  change ((actualBlockBrauerAction iota hinj blocks b tau closed f :
    actualBlockBrauerSpan iota hinj blocks b) : PrimeRegularFunction K X p)
      (A.representative c) = f.1 (A.representative (perm c))
  rw [coe_actualBlockBrauerAction_apply iota hinj blocks b tau closed f]
  exact regularCoordinateEvaluation_pullback_apply A
    (fun phi : ActualBrauerBlock iota hinj blocks b => phi.1.1)
    tau perm fusion f.1 f.2 c

variable (decomposition : ∀ a : MulAut X, ∃ x : X,
  a = MulAut.conj x ∨ a = MulAut.conj x * tau)

include decomposition

theorem actualBlockBrauerMap_involutive :
    Function.Involutive (actualBlockBrauerMap iota hinj blocks b tau closed) := by
  intro phi
  apply Subtype.ext
  change MulOpposite.op tau • (MulOpposite.op tau • phi.1) = phi.1
  exact brauer_tau_involutive iota tau decomposition phi.1

theorem actualBlockBrauerAction_comp_self :
    (actualBlockBrauerAction iota hinj blocks b tau closed).comp
      (actualBlockBrauerAction iota hinj blocks b tau closed) = LinearMap.id := by
  apply (actualBlockBrauerBasis iota hinj blocks b).ext
  intro phi
  change actualBlockBrauerAction iota hinj blocks b tau closed
      (actualBlockBrauerAction iota hinj blocks b tau closed
        (actualBlockBrauerBasis iota hinj blocks b phi)) =
    actualBlockBrauerBasis iota hinj blocks b phi
  rw [actualBlockBrauerAction_basis, actualBlockBrauerAction_basis,
    actualBlockBrauerMap_involutive iota hinj blocks b tau closed decomposition phi]

theorem actualBlockBrauerAction_involutive :
    Function.Involutive (actualBlockBrauerAction iota hinj blocks b tau closed) := by
  intro f
  exact congrArg (fun L : actualBlockBrauerSpan iota hinj blocks b →ₗ[K]
      actualBlockBrauerSpan iota hinj blocks b => L f)
    (actualBlockBrauerAction_comp_self iota hinj blocks b tau closed decomposition)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockBrauerAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
