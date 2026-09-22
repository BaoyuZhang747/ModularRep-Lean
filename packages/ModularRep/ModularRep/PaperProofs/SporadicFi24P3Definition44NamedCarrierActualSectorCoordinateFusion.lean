import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorBrauerAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoActions

/-! # Actual outer fusion and coordinate precomposition -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualSectorBrauerAction
open SporadicFi24P3Definition44NamedCarrierActualTwoActions

universe u v w

section Generic

variable {p : ℕ} {K X : Type u}
variable {Row : Type v} {Column : Type w}
variable [Field K] [Group X]

def regularPullbackLinear (tau : MulAut X) :
    PrimeRegularFunction K X p →ₗ[K] PrimeRegularFunction K X p where
  toFun f := f.pullback tau.toMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinatePullbackLinear (perm : Equiv.Perm Column) :
    (Column → K) →ₗ[K] (Column → K) where
  toFun a := fun c => a (perm c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem regularCoordinateEvaluation_pullback_apply
    (A : PrimeRegularRepresentativeCover p X Column)
    (rows : Row → PrimeRegularClassFunction K X p)
    (tau : MulAut X) (perm : Equiv.Perm Column)
    (fusion : ∀ c : Column, ∃ x : X,
      tau (A.representative c).1 =
        x * (A.representative (perm c)).1 * x⁻¹)
    (f : PrimeRegularFunction K X p)
    (hf : f ∈ classFunctionRowSpan rows) (c : Column) :
    regularCoordinateEvaluation A (regularPullbackLinear tau f) c =
      regularCoordinateEvaluation A f (perm c) := by
  obtain ⟨x, hx⟩ := fusion c
  change f (PrimeRegularElement.map tau.toMonoidHom (A.representative c)) =
    f (A.representative (perm c))
  have hrep : PrimeRegularElement.map tau.toMonoidHom (A.representative c) =
      ⟨x * (A.representative (perm c)).1 * x⁻¹,
        (A.representative (perm c)).2.conj x⟩ := Subtype.ext hx
  exact (congrArg f hrep).trans
    (classFunctionRowSpan_map_conj rows f hf x (A.representative (perm c)))

theorem regularCoordinateEvaluation_pullback
    (A : PrimeRegularRepresentativeCover p X Column)
    (rows : Row → PrimeRegularClassFunction K X p)
    (tau : MulAut X) (perm : Equiv.Perm Column)
    (fusion : ∀ c : Column, ∃ x : X,
      tau (A.representative c).1 =
        x * (A.representative (perm c)).1 * x⁻¹)
    (f : PrimeRegularFunction K X p)
    (hf : f ∈ classFunctionRowSpan rows) :
    regularCoordinateEvaluation A (regularPullbackLinear tau f) =
      coordinatePullbackLinear perm (regularCoordinateEvaluation A f) := by
  funext c
  exact regularCoordinateEvaluation_pullback_apply A rows tau perm fusion f hf c

/-- Involutivity is asserted only on the class-function row span. -/
theorem classFunctionRowSpan_pullback_twice
    (rows : Row → PrimeRegularClassFunction K X p)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (f : PrimeRegularFunction K X p)
    (hf : f ∈ classFunctionRowSpan rows) :
    regularPullbackLinear tau (regularPullbackLinear tau f) = f := by
  let F : PrimeRegularClassFunction K X p :=
    ⟨f, classFunctionRowSpan_map_conj rows f hf⟩
  obtain ⟨x, hx⟩ := square_inner_of_two_cosets tau decomposition
  have hF : (F.twist tau).twist tau = F := by
    calc
      (F.twist tau).twist tau = F.twist (tau ^ 2) := by
        rw [PrimeRegularClassFunction.twist_mul, pow_two]
      _ = F := by rw [hx, PrimeRegularClassFunction.twist_conj]
  exact congrArg PrimeRegularClassFunction.toFun hF

end Generic

section Actual

variable {p : ℕ} {k K X BlockIndex : Type u}
variable {Row : Type v} {Column : Type w}
variable [Field k] [Field K]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (D : ActualOrdinaryDecomposition iota hinj blocks)
variable (nu : CentralSector (k := k) (X := X))
variable (C : ActualSectorOrdinaryRows iota hinj blocks D nu Row)

def actualSectorBrauerEvaluationEquiv
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c,
      (C.character r).1 (A.representative c).1 = matrix r c) :
    actualSectorBrauerSpan iota hinj blocks nu ≃ₗ[K]
      Submodule.span K (Set.range matrix) :=
  (LinearEquiv.ofEq _ _
    (actualSectorOrdinaryRows_span iota hinj blocks D nu C).symm).trans
      (actualSectorEvaluationEquiv iota hinj blocks D nu C A matrix hvalues)

@[simp]
theorem actualSectorBrauerEvaluationEquiv_apply
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c,
      (C.character r).1 (A.representative c).1 = matrix r c)
    (f : actualSectorBrauerSpan iota hinj blocks nu) :
    ((actualSectorBrauerEvaluationEquiv iota hinj blocks D nu C A matrix hvalues f :
      Submodule.span K (Set.range matrix)) : Column → K) =
        fun c => f.1 (A.representative c) := rfl

theorem actualSectorBrauerEvaluationEquiv_action_apply
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c,
      (C.character r).1 (A.representative c).1 = matrix r c)
    (tau : MulAut X) (hnu : MulOpposite.op tau • nu = nu)
    (perm : Equiv.Perm Column)
    (fusion : ∀ c : Column, ∃ x : X,
      tau (A.representative c).1 =
        x * (A.representative (perm c)).1 * x⁻¹)
    (f : actualSectorBrauerSpan iota hinj blocks nu) (c : Column) :
    ((actualSectorBrauerEvaluationEquiv iota hinj blocks D nu C A matrix hvalues
        (actualSectorBrauerAction iota hinj blocks nu tau hnu f) :
          Submodule.span K (Set.range matrix)) : Column → K) c =
      ((actualSectorBrauerEvaluationEquiv iota hinj blocks D nu C A matrix hvalues f :
        Submodule.span K (Set.range matrix)) : Column → K) (perm c) := by
  change ((actualSectorBrauerAction iota hinj blocks nu tau hnu f :
      actualSectorBrauerSpan iota hinj blocks nu) : PrimeRegularFunction K X p)
        (A.representative c) = f.1 (A.representative (perm c))
  rw [coe_actualSectorBrauerAction_apply iota hinj blocks nu tau hnu f]
  exact regularCoordinateEvaluation_pullback_apply A
    (fun phi : ActualBrauerSector iota hinj blocks nu => phi.1.1)
    tau perm fusion f.1 f.2 c

end Actual

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
