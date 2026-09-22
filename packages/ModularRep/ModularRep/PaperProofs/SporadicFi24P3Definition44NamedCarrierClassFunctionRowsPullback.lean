import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! Full regular coverage derives row-span closure; independence reflects block labels. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierClassFunctionRowsPullback

open ModularRep ModularRep.BlockwiseOrdinaryBrauerSpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateFusion

universe u v w z

theorem classFunction_eq_of_regularValues
    {p : ℕ} {K X : Type u} {Column : Type w} [Field K] [Group X]
    (A : PrimeRegularRepresentativeCover p X Column)
    (F G : PrimeRegularClassFunction K X p)
    (h : ∀ c, F (A.representative c) = G (A.representative c)) :
    F = G := by
  ext g
  obtain ⟨c, x, hx⟩ := A.complete g
  have hg : g = ⟨x * (A.representative c).1 * x⁻¹,
      (A.representative c).2.conj x⟩ := Subtype.ext hx
  calc
    F g = F ⟨x * (A.representative c).1 * x⁻¹,
        (A.representative c).2.conj x⟩ := congrArg F hg
    _ = F (A.representative c) := F.map_conj x _
    _ = G (A.representative c) := h c
    _ = G ⟨x * (A.representative c).1 * x⁻¹,
        (A.representative c).2.conj x⟩ := (G.map_conj x _).symm
    _ = G g := (congrArg G hg).symm

theorem classFunctionRows_twist_of_values
    {p : ℕ} {K X : Type u} {Row : Type v} {Column : Type w} [Field K] [Group X]
    (A : PrimeRegularRepresentativeCover p X Column)
    (rows : Row → PrimeRegularClassFunction K X p)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, rows r (A.representative c) = matrix r c)
    (tau : MulAut X) (perm : Equiv.Perm Column)
    (fusion : ∀ c, ∃ x : X, tau (A.representative c).1 =
      x * (A.representative (perm c)).1 * x⁻¹)
    (s : Row → Row)
    (hmatrix : ∀ r c, matrix r (perm c) = matrix (s r) c) (r : Row) :
    (rows r).twist tau = rows (s r) := by
  apply classFunction_eq_of_regularValues A
  intro c
  obtain ⟨x, hx⟩ := fusion c
  have hrep : PrimeRegularElement.map tau.toMonoidHom (A.representative c) =
      ⟨x * (A.representative (perm c)).1 * x⁻¹,
        (A.representative (perm c)).2.conj x⟩ := Subtype.ext hx
  change rows r (PrimeRegularElement.map tau.toMonoidHom (A.representative c)) =
    rows (s r) (A.representative c)
  calc
    _ = rows r ⟨x * (A.representative (perm c)).1 * x⁻¹,
        (A.representative (perm c)).2.conj x⟩ := congrArg (rows r) hrep
    _ = rows r (A.representative (perm c)) := (rows r).map_conj x _
    _ = matrix r (perm c) := hvalues r (perm c)
    _ = matrix (s r) c := hmatrix r c
    _ = rows (s r) (A.representative c) := (hvalues (s r) c).symm

theorem pullback_mem_classFunctionRowSpan
    {p : ℕ} {K X : Type u} {Row : Type v} [Field K] [Group X]
    (rows : Row → PrimeRegularClassFunction K X p)
    (tau : MulAut X) (s : Row → Row)
    (hrows : ∀ r, (rows r).twist tau = rows (s r))
    (f : PrimeRegularFunction K X p) (hf : f ∈ classFunctionRowSpan rows) :
    regularPullbackLinear tau f ∈ classFunctionRowSpan rows := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨r, rfl⟩ := hf
      have hr : regularPullbackLinear tau (rows r).toFun = (rows (s r)).toFun :=
        congrArg PrimeRegularClassFunction.toFun (hrows r)
      rw [hr]
      exact Submodule.subset_span (Set.mem_range_self (s r))
  | zero =>
      simpa only [map_zero] using (classFunctionRowSpan rows).zero_mem
  | add f g hf hg ihf ihg =>
      simpa only [map_add] using (classFunctionRowSpan rows).add_mem ihf ihg
  | smul a f hf ih =>
      simpa only [map_smul] using (classFunctionRowSpan rows).smul_mem a ih

theorem label_eq_of_mem_blockSpan
    {K : Type u} {V : Type v} {I : Type w} {B : Type z}
    [Field K] [AddCommGroup V] [Module K V]
    (values : I → V) (label : I → B) (b : B)
    (hv : LinearIndependent K values) (i : I)
    (hi : values i ∈ blockSpan (K := K) values label b) : label i = b := by
  classical
  have hs : Set.range (blockFamily values label b) = values '' {j | label j = b} := by
    ext x
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  by_contra hnot
  apply hv.notMem_span_image (s := {j | label j = b}) (x := i) hnot
  simpa only [blockSpan, hs] using hi

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierClassFunctionRowsPullback


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
