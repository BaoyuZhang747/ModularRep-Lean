import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Span.Basic
import ModularRep.PrimeRegularClassFunction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan

/-!
# Evaluation of actual ordinary sector spans

Conjugacy coverage by actual regular representatives proves evaluation
injective. Pointwise ordinary-character values determine its image span.
The resulting coordinate equivalence is a deduction, not a source field.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan

universe u v w

/-- Actual regular representatives covering regular elements up to conjugacy. -/
structure PrimeRegularRepresentativeCover
    (p : ℕ) (X : Type u) [Group X] (Column : Type w) :
    Type (max u w) where
  representative : Column → PrimeRegularElement (G := X) p
  complete : ∀ g : PrimeRegularElement (G := X) p,
    ∃ c : Column, ∃ x : X,
      g.1 = x * (representative c).1 * x⁻¹

section Generic

variable {p : ℕ} {K X : Type u} {Row : Type v} {Column : Type w}
variable [Field K] [Group X]

abbrev classFunctionRowSpan
    (rows : Row → PrimeRegularClassFunction K X p) :
    Submodule K (PrimeRegularFunction K X p) :=
  Submodule.span K (Set.range fun r => (rows r).toFun)

def regularCoordinateEvaluation
    (A : PrimeRegularRepresentativeCover p X Column) :
    PrimeRegularFunction K X p →ₗ[K] (Column → K) where
  toFun f := fun c => f (A.representative c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem classFunctionRowSpan_map_conj
    (rows : Row → PrimeRegularClassFunction K X p)
    (f : PrimeRegularFunction K X p)
    (hf : f ∈ classFunctionRowSpan rows)
    (x : X) (g : PrimeRegularElement (G := X) p) :
    f ⟨x * g.1 * x⁻¹, g.2.conj x⟩ = f g := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨r, rfl⟩
      exact (rows r).map_conj x g
  | zero => rfl
  | add f q hf hq ihf ihq =>
      exact congrArg₂ (fun a b : K => a + b) ihf ihq
  | smul a f hf ih =>
      exact congrArg (fun z : K => a • z) ih

def classFunctionSpanEvaluation
    (A : PrimeRegularRepresentativeCover p X Column)
    (rows : Row → PrimeRegularClassFunction K X p) :
    classFunctionRowSpan rows →ₗ[K] (Column → K) :=
  (regularCoordinateEvaluation (K := K) A).domRestrict
    (classFunctionRowSpan rows)

theorem classFunctionSpanEvaluation_injective
    (A : PrimeRegularRepresentativeCover p X Column)
    (rows : Row → PrimeRegularClassFunction K X p) :
    Function.Injective (classFunctionSpanEvaluation A rows) := by
  intro f q h
  apply Subtype.ext
  funext g
  obtain ⟨c, x, hx⟩ := A.complete g
  have hg :
      g = ⟨x * (A.representative c).1 * x⁻¹,
        (A.representative c).2.conj x⟩ := Subtype.ext hx
  have hf : f.1 g = f.1 (A.representative c) :=
    (congrArg f.1 hg).trans
      (classFunctionRowSpan_map_conj rows f.1 f.2 x (A.representative c))
  have hq : q.1 g = q.1 (A.representative c) :=
    (congrArg q.1 hg).trans
      (classFunctionRowSpan_map_conj rows q.1 q.2 x (A.representative c))
  exact hf.trans ((congrFun h c).trans hq.symm)

theorem classFunctionSpanEvaluation_range
    (A : PrimeRegularRepresentativeCover p X Column)
    (rows : Row → PrimeRegularClassFunction K X p)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, rows r (A.representative c) = matrix r c) :
    LinearMap.range (classFunctionSpanEvaluation A rows) =
      Submodule.span K (Set.range matrix) := by
  change
    LinearMap.range
        ((regularCoordinateEvaluation (K := K) A).domRestrict
          (Submodule.span K (Set.range fun r => (rows r).toFun))) =
      Submodule.span K (Set.range matrix)
  rw [LinearMap.range_domRestrict, Submodule.map_span]
  apply congrArg (Submodule.span K)
  ext y
  constructor
  · rintro ⟨f, ⟨r, rfl⟩, rfl⟩
    refine ⟨r, ?_⟩
    funext c
    exact (hvalues r c).symm
  · rintro ⟨r, rfl⟩
    refine ⟨(rows r).toFun, ⟨r, rfl⟩, ?_⟩
    funext c
    exact hvalues r c

def classFunctionSpanEvaluationEquiv
    (A : PrimeRegularRepresentativeCover p X Column)
    (rows : Row → PrimeRegularClassFunction K X p)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, rows r (A.representative c) = matrix r c) :
    classFunctionRowSpan rows ≃ₗ[K]
      Submodule.span K (Set.range matrix) :=
  (LinearEquiv.ofInjective
    (classFunctionSpanEvaluation A rows)
    (classFunctionSpanEvaluation_injective A rows)).trans
      (LinearEquiv.ofEq _ _
        (classFunctionSpanEvaluation_range A rows matrix hvalues))

@[simp]
theorem classFunctionSpanEvaluationEquiv_apply
    (A : PrimeRegularRepresentativeCover p X Column)
    (rows : Row → PrimeRegularClassFunction K X p)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, rows r (A.representative c) = matrix r c)
    (f : classFunctionRowSpan rows) :
    ((classFunctionSpanEvaluationEquiv A rows matrix hvalues f :
        Submodule.span K (Set.range matrix)) : Column → K) =
      fun c => f.1 (A.representative c) := rfl

end Generic

section Ordinary

variable {p : ℕ} {K X : Type u}
variable [Field K] [Group X]

theorem ordinaryCharacter_conj
    (chi : OrdinaryIrreducibleCharacter.Irr K X)
    (x g : X) : chi.1 (x * g * x⁻¹) = chi.1 g := by
  rcases chi.2 with ⟨R⟩
  calc
    chi.1 (x * g * x⁻¹) =
        R.representation.character (x * g * x⁻¹) :=
      (congrFun R.character_eq (x * g * x⁻¹)).symm
    _ = R.representation.character g := R.representation.char_conj g x
    _ = chi.1 g := congrFun R.character_eq g

def ordinaryRestrictionClassFunction
    (chi : OrdinaryIrreducibleCharacter.Irr K X) :
    PrimeRegularClassFunction K X p :=
  PrimeRegularClassFunction.ofFunction chi.1 (ordinaryCharacter_conj chi)

@[simp]
theorem ordinaryRestrictionClassFunction_apply
    (chi : OrdinaryIrreducibleCharacter.Irr K X)
    (g : PrimeRegularElement (G := X) p) :
    ordinaryRestrictionClassFunction (p := p) chi g = chi.1 g.1 := rfl

end Ordinary

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

abbrev actualSectorOrdinaryClassRows :
    Row → PrimeRegularClassFunction K X p :=
  fun r => ordinaryRestrictionClassFunction (p := p) (C.character r)

def actualSectorEvaluation
    (A : PrimeRegularRepresentativeCover p X Column) :
    actualSectorOrdinarySpan iota hinj blocks D nu C →ₗ[K] (Column → K) :=
  classFunctionSpanEvaluation A
    (actualSectorOrdinaryClassRows iota hinj blocks D nu C)

theorem actualSectorEvaluation_injective
    (A : PrimeRegularRepresentativeCover p X Column) :
    Function.Injective (actualSectorEvaluation iota hinj blocks D nu C A) :=
  classFunctionSpanEvaluation_injective A
    (actualSectorOrdinaryClassRows iota hinj blocks D nu C)

theorem actualSectorEvaluation_range
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c,
      (C.character r).1 (A.representative c).1 = matrix r c) :
    LinearMap.range (actualSectorEvaluation iota hinj blocks D nu C A) =
      Submodule.span K (Set.range matrix) :=
  classFunctionSpanEvaluation_range A
    (actualSectorOrdinaryClassRows iota hinj blocks D nu C) matrix hvalues

def actualSectorEvaluationEquiv
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c,
      (C.character r).1 (A.representative c).1 = matrix r c) :
    actualSectorOrdinarySpan iota hinj blocks D nu C ≃ₗ[K]
      Submodule.span K (Set.range matrix) :=
  classFunctionSpanEvaluationEquiv A
    (actualSectorOrdinaryClassRows iota hinj blocks D nu C) matrix hvalues

@[simp]
theorem actualSectorEvaluationEquiv_apply
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c,
      (C.character r).1 (A.representative c).1 = matrix r c)
    (f : actualSectorOrdinarySpan iota hinj blocks D nu C) :
    ((actualSectorEvaluationEquiv iota hinj blocks D nu C A matrix hvalues f :
        Submodule.span K (Set.range matrix)) : Column → K) =
      fun c => f.1 (A.representative c) := rfl

end Actual

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
