import ModularRep.CentralIdempotentSupport
import Mathlib.GroupTheory.Submonoid.Center

/-!
# Primitive central idempotents

This file defines primitive central idempotents by the absence of a
nontrivial central idempotent below them.  It then proves that a primitive
central idempotent has a unique support in every complete finite family of
pairwise orthogonal central idempotents.
-/

open scoped BigOperators

namespace ModularRep

/-- A primitive central idempotent is a nonzero central idempotent whose only
central idempotent factors are zero and itself.  The equation `c * b = c`
expresses that the central idempotent `c` lies below `b`. -/
structure IsPrimitiveCentralIdempotent {A : Type*} [Ring A] (b : A) : Prop where
  /-- The element is idempotent. -/
  idempotent : IsIdempotentElem b
  /-- The element is central. -/
  central : IsMulCentral b
  /-- A primitive idempotent is nonzero. -/
  ne_zero : b ≠ 0
  /-- There is no nontrivial central idempotent below `b`. -/
  eq_zero_or_eq_self : ∀ c : A, IsIdempotentElem c → IsMulCentral c → c * b = c →
    c = 0 ∨ c = b

namespace IsPrimitiveCentralIdempotent

section RingEquiv

variable {A B : Type*} [Ring A] [Ring B] {b : A}

/-- Ring equivalences preserve primitive central idempotents. -/
theorem mapRingEquiv (hb : IsPrimitiveCentralIdempotent b)
    (sigma : A ≃+* B) : IsPrimitiveCentralIdempotent (sigma b) where
  idempotent := by
    change sigma b * sigma b = sigma b
    calc
      sigma b * sigma b = sigma (b * b) := (sigma.map_mul b b).symm
      _ = sigma b := congrArg sigma hb.idempotent.eq
  central := MulEquivClass.apply_mem_center sigma hb.central
  ne_zero := by
    intro hzero
    apply hb.ne_zero
    calc
      b = sigma.symm (sigma b) := (sigma.symm_apply_apply b).symm
      _ = sigma.symm 0 := congrArg sigma.symm hzero
      _ = 0 := sigma.symm.map_zero
  eq_zero_or_eq_self := by
    intro c hcIdempotent hcCentral hcBelow
    have hcIdempotent' : IsIdempotentElem (sigma.symm c) := by
      change sigma.symm c * sigma.symm c = sigma.symm c
      calc
        sigma.symm c * sigma.symm c = sigma.symm (c * c) :=
          (sigma.symm.map_mul c c).symm
        _ = sigma.symm c := congrArg sigma.symm hcIdempotent.eq
    have hcCentral' : IsMulCentral (sigma.symm c) :=
      MulEquivClass.apply_mem_center sigma.symm hcCentral
    have hcBelow' : sigma.symm c * b = sigma.symm c := by
      calc
        sigma.symm c * b = sigma.symm c * sigma.symm (sigma b) := by
          rw [sigma.symm_apply_apply]
        _ = sigma.symm (c * sigma b) :=
          (sigma.symm.map_mul c (sigma b)).symm
        _ = sigma.symm c := congrArg sigma.symm hcBelow
    rcases hb.eq_zero_or_eq_self (sigma.symm c)
        hcIdempotent' hcCentral' hcBelow' with hzero | hself
    · left
      calc
        c = sigma (sigma.symm c) := (sigma.apply_symm_apply c).symm
        _ = sigma 0 := congrArg sigma hzero
        _ = 0 := sigma.map_zero
    · right
      calc
        c = sigma (sigma.symm c) := (sigma.apply_symm_apply c).symm
        _ = sigma b := congrArg sigma hself

end RingEquiv

variable {A ι : Type*} [Ring A] [Fintype ι]
variable {b : A} {e : ι → A}

/-- The product with each member of a complete central idempotent family is
either zero or the original primitive central idempotent. -/
theorem mul_eq_zero_or_eq_self (hb : IsPrimitiveCentralIdempotent b)
    (E : CompleteOrthogonalCentralIdempotents e) (i : ι) :
    b * e i = 0 ∨ b * e i = b := by
  apply hb.eq_zero_or_eq_self
  · exact IsIdempotentElem.mul_of_commute (hb.central.comm (e i))
      hb.idempotent (E.idem i)
  · exact Set.mul_mem_center hb.central (E.central i)
  · calc
      (b * e i) * b = b * (e i * b) := mul_assoc _ _ _
      _ = b * (b * e i) := by rw [(E.central i).comm b]
      _ = (b * b) * e i := (mul_assoc _ _ _).symm
      _ = b * e i := by rw [hb.idempotent.eq]

/-- The assertion that `i` supports the primitive central idempotent `b`
inside the family `e`. -/
def IsSupport (b : A) (e : ι → A) (i : ι) : Prop :=
  b * e i = b ∧ ∀ j, j ≠ i → b * e j = 0

/-- A primitive central idempotent has a unique support in every complete
finite family of pairwise orthogonal central idempotents. -/
theorem existsUnique_isSupport (hb : IsPrimitiveCentralIdempotent b)
    (E : CompleteOrthogonalCentralIdempotents e) :
    ∃! i, IsSupport b e i := by
  classical
  have hsum : ∑ i, b * e i = b := by
    rw [← Finset.mul_sum, E.complete, mul_one]
  have hexists : ∃ i, b * e i ≠ 0 := by
    by_contra h
    have hzero : ∀ i, b * e i = 0 := by
      intro i
      exact not_ne_iff.mp (not_exists.mp h i)
    apply hb.ne_zero
    rw [← hsum]
    simp [hzero]
  obtain ⟨i, hi⟩ := hexists
  have hi_self : b * e i = b :=
    (hb.mul_eq_zero_or_eq_self E i).resolve_left hi
  have hi_support : IsSupport b e i := by
    refine ⟨hi_self, ?_⟩
    intro j hij
    have h := congrArg (fun x : A ↦ x * e j) hi_self
    calc
      b * e j = (b * e i) * e j := h.symm
      _ = b * (e i * e j) := mul_assoc _ _ _
      _ = 0 := by rw [E.ortho (Ne.symm hij), mul_zero]
  refine ⟨i, hi_support, ?_⟩
  intro j hj_support
  by_contra hji
  apply hb.ne_zero
  rw [← hi_self, hj_support.2 i (Ne.symm hji)]

/-- The unique member of a complete central idempotent family supporting a
given primitive central idempotent. -/
noncomputable def support (hb : IsPrimitiveCentralIdempotent b)
    (E : CompleteOrthogonalCentralIdempotents e) : ι :=
  Classical.choose (hb.existsUnique_isSupport E).exists

theorem support_isSupport (hb : IsPrimitiveCentralIdempotent b)
    (E : CompleteOrthogonalCentralIdempotents e) :
    IsSupport b e (hb.support E) :=
  Classical.choose_spec (hb.existsUnique_isSupport E).exists

@[simp]
theorem mul_support (hb : IsPrimitiveCentralIdempotent b)
    (E : CompleteOrthogonalCentralIdempotents e) :
    b * e (hb.support E) = b :=
  (hb.support_isSupport E).1

theorem mul_eq_zero_of_ne_support (hb : IsPrimitiveCentralIdempotent b)
    (E : CompleteOrthogonalCentralIdempotents e) {i : ι}
    (hi : i ≠ hb.support E) :
    b * e i = 0 :=
  (hb.support_isSupport E).2 i hi

theorem support_unique (hb : IsPrimitiveCentralIdempotent b)
    (E : CompleteOrthogonalCentralIdempotents e) {i : ι}
    (hi : IsSupport b e i) :
    i = hb.support E :=
  (hb.existsUnique_isSupport E).unique hi (hb.support_isSupport E)

namespace IsSupport

variable {V : Type*} [AddCommGroup V] [Module A V]

omit [Fintype ι] in
/-- If `b` acts as the identity on a module, support of `b` at `i` implies
support of the module at the same index. -/
theorem toModuleSupport {i : ι} (hi : IsSupport b e i)
    (hbV : ∀ v : V, b • v = v) :
    CompleteOrthogonalCentralIdempotents.IsSupport (V := V) e i := by
  constructor
  · intro v
    calc
      e i • v = b • (e i • v) := (hbV (e i • v)).symm
      _ = (b * e i) • v := by rw [mul_smul]
      _ = b • v := by rw [hi.1]
      _ = v := hbV v
  · intro j hji v
    calc
      e j • v = b • (e j • v) := (hbV (e j • v)).symm
      _ = (b * e j) • v := by rw [mul_smul]
      _ = 0 := by rw [hi.2 j hji, zero_smul]

end IsSupport

end IsPrimitiveCentralIdempotent

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
