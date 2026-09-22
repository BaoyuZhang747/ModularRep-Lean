import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Support of an irreducible module under central idempotents

A complete finite family of pairwise orthogonal central idempotents has a
unique support on a simple module: one idempotent acts as the identity and all
the others act as zero.
-/

open scoped BigOperators

namespace ModularRep

/-- A complete finite family of pairwise orthogonal idempotents whose members
are central.  This extends Mathlib's standard
`CompleteOrthogonalIdempotents` predicate. -/
structure CompleteOrthogonalCentralIdempotents {A ι : Type*} [Ring A] [Fintype ι]
    (e : ι → A) : Prop extends CompleteOrthogonalIdempotents e where
  /-- Every member of the family is central. -/
  central : ∀ i, IsMulCentral (e i)

namespace CompleteOrthogonalCentralIdempotents

variable {A V ι : Type*}
variable [Ring A] [AddCommGroup V] [Module A V] [Fintype ι]

/-- The `A`-linear endomorphism induced by one member of a central idempotent
family. -/
def actionEnd {e : ι → A} (E : CompleteOrthogonalCentralIdempotents e) (i : ι) :
    Module.End A V where
  toFun v := e i • v
  map_add' _ _ := smul_add _ _ _
  map_smul' a v := by
    simpa only [smul_smul, RingHom.id_apply] using
      congrArg (fun b : A ↦ b • v) ((E.central i).comm a).eq

@[simp]
theorem actionEnd_apply {e : ι → A} (E : CompleteOrthogonalCentralIdempotents e)
    (i : ι) (v : V) : E.actionEnd i v = e i • v :=
  rfl

variable [IsSimpleModule A V]

/-- On a simple module, each central idempotent in the family acts either as
the identity or as zero. -/
theorem actsAsIdentity_or_zero {e : ι → A} (E : CompleteOrthogonalCentralIdempotents e)
    (i : ι) : (∀ v : V, e i • v = v) ∨ (∀ v : V, e i • v = 0) := by
  let f : Module.End A V := E.actionEnd i
  rcases LinearMap.bijective_or_eq_zero f with hf | hf
  · left
    intro v
    apply hf.1
    change e i • (e i • v) = e i • v
    rw [← mul_smul, (E.idem i).eq]
  · right
    intro v
    have h := congrArg (fun g : Module.End A V ↦ g v) hf
    simpa [f] using h

/-- The assertion that `i` is the unique member of the family supported by
the simple module. -/
def IsSupport (e : ι → A) (i : ι) : Prop :=
  (∀ v : V, e i • v = v) ∧ ∀ j, j ≠ i → ∀ v : V, e j • v = 0

/-- A complete finite family of pairwise orthogonal central idempotents has a
unique support on a simple module. -/
theorem existsUnique_isSupport {e : ι → A} (E : CompleteOrthogonalCentralIdempotents e) :
    ∃! i, IsSupport (V := V) e i := by
  classical
  have hidentity : ∃ i, ∀ v : V, e i • v = v := by
    by_contra h
    have hzero : ∀ i, ∀ v : V, e i • v = 0 := by
      intro i
      exact (E.actsAsIdentity_or_zero (V := V) i).resolve_left (not_exists.mp h i)
    let _ : Nontrivial V := IsSimpleModule.nontrivial A V
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    calc
      v = (1 : A) • v := by simp
      _ = (∑ i, e i) • v := by rw [E.complete]
      _ = ∑ i, e i • v := by rw [Finset.sum_smul]
      _ = 0 := by simp_rw [hzero]; simp
  obtain ⟨i, hi⟩ := hidentity
  have hiSupport : IsSupport (V := V) e i := by
    refine ⟨hi, ?_⟩
    intro j hji v
    calc
      e j • v = e j • (e i • v) := by rw [hi]
      _ = (e j * e i) • v := by rw [mul_smul]
      _ = 0 := by rw [E.ortho hji]; simp
  refine ⟨i, hiSupport, ?_⟩
  intro j hjSupport
  by_contra hij
  let _ : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  calc
    v = e j • v := (hjSupport.1 v).symm
    _ = 0 := hiSupport.2 j hij v

/-- The support index of a complete family on a simple module. -/
noncomputable def support {e : ι → A} (E : CompleteOrthogonalCentralIdempotents e) : ι :=
  Classical.choose (E.existsUnique_isSupport (V := V)).exists

theorem support_isSupport {e : ι → A} (E : CompleteOrthogonalCentralIdempotents e) :
    IsSupport (V := V) e (E.support (V := V)) :=
  Classical.choose_spec (E.existsUnique_isSupport (V := V)).exists

@[simp]
theorem support_smul {e : ι → A} (E : CompleteOrthogonalCentralIdempotents e) (v : V) :
    e (E.support (V := V)) • v = v :=
  (E.support_isSupport (V := V)).1 v

theorem smul_eq_zero_of_ne_support {e : ι → A}
    (E : CompleteOrthogonalCentralIdempotents e)
    {i : ι} (hi : i ≠ E.support (V := V)) (v : V) :
    e i • v = 0 :=
  (E.support_isSupport (V := V)).2 i hi v

theorem support_unique {e : ι → A} (E : CompleteOrthogonalCentralIdempotents e) {i : ι}
    (hi : IsSupport (V := V) e i) : i = E.support (V := V) :=
  (E.existsUnique_isSupport (V := V)).unique hi (E.support_isSupport (V := V))

end CompleteOrthogonalCentralIdempotents

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
