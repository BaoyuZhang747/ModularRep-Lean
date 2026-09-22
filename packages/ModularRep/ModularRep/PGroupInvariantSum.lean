import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.GroupTheory.PGroup

namespace ModularRep

open scoped BigOperators

noncomputable section

attribute [local instance] Fintype.ofFinite

/-- An invariant weighted sum for a finite action of a `p`-group in characteristic `p`
is supported on the fixed points. -/
theorem IsPGroup.sum_eq_sum_fixedPoints_of_invariant
    {p : Nat} {Q alpha k : Type*}
    [Group Q] [Fintype alpha] [MulAction Q alpha]
    [CommSemiring k] [CharP k p] [Fact p.Prime]
    (hQ : IsPGroup p Q) (f : alpha → k)
    (hf : ∀ q : Q, ∀ x : alpha, f (q • x) = f x) :
    (∑ x : alpha, f x) =
      ∑ x : MulAction.fixedPoints Q alpha, f (x : alpha) := by
  let _ : Fintype (MulAction.fixedPoints Q alpha) := Fintype.ofFinite _
  classical
  let orbitWeight : Quotient (MulAction.orbitRel Q alpha) → k :=
    fun y ↦ ∑ x : {x // Quotient.mk'' x = y}, f x
  have key :
      ∀ x : alpha,
        Fintype.card
            {y //
              (Quotient.mk'' y : Quotient (MulAction.orbitRel Q alpha)) =
                Quotient.mk'' x} =
          Fintype.card (MulAction.orbit Q x) :=
    fun x ↦ by
      simp only [Quotient.eq'']
      congr
  have orbitWeight_eq_card_nsmul (x : alpha) :
      orbitWeight (Quotient.mk'' x) =
        Fintype.card (MulAction.orbit Q x) • f x := by
    dsimp only [orbitWeight]
    calc
      (∑ y :
          {y //
            (Quotient.mk'' y : Quotient (MulAction.orbitRel Q alpha)) =
              Quotient.mk'' x},
          f y) =
          ∑ _y :
            {y //
              (Quotient.mk'' y : Quotient (MulAction.orbitRel Q alpha)) =
                Quotient.mk'' x},
            f x := by
              apply Fintype.sum_congr
              intro y
              have hy : (y : alpha) ∈ MulAction.orbit Q x :=
                MulAction.orbitRel_apply.mp (Quotient.exact' y.property)
              obtain ⟨q, hq⟩ := MulAction.mem_orbit_iff.mp hy
              exact (congrArg f hq).symm.trans (hf q x)
      _ =
          Fintype.card
              {y //
                (Quotient.mk'' y : Quotient (MulAction.orbitRel Q alpha)) =
                  Quotient.mk'' x} •
            f x := by simp
      _ = Fintype.card (MulAction.orbit Q x) • f x := by
        rw [key x]
  have orbitWeight_eq_of_fixed (x : alpha)
      (hx : x ∈ MulAction.fixedPoints Q alpha) :
      orbitWeight (Quotient.mk'' x) = f x := by
    rw [orbitWeight_eq_card_nsmul,
      MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp hx, one_nsmul]
  have orbitWeight_eq_zero_of_not_fixed (x : alpha)
      (hx : x ∉ MulAction.fixedPoints Q alpha) :
      orbitWeight (Quotient.mk'' x) = 0 := by
    rw [orbitWeight_eq_card_nsmul, nsmul_eq_mul]
    obtain ⟨n, hn⟩ := hQ.card_orbit x
    rw [Nat.card_eq_fintype_card] at hn
    have hn0 : n ≠ 0 := by
      intro hnzero
      apply hx
      apply MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr
      rw [hn, hnzero, pow_zero]
    have hcast : ((Fintype.card (MulAction.orbit Q x) : Nat) : k) = 0 := by
      have hmod : Fintype.card (MulAction.orbit Q x) ≡ 0 [MOD p] := by
        rw [hn]
        exact Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p hn0)
      simpa only [Nat.cast_zero] using CharP.natCast_eq_natCast' k p hmod
    rw [hcast, zero_mul]
  rw [← Fintype.sum_fiberwise
    (@Quotient.mk'' alpha (MulAction.orbitRel Q alpha)) f]
  change (∑ y : Quotient (MulAction.orbitRel Q alpha), orbitWeight y) =
    ∑ x : MulAction.fixedPoints Q alpha, f (x : alpha)
  refine Eq.symm
    (Finset.sum_bij_ne_zero
      (fun a _ _ ↦ Quotient.mk'' a.1)
      (fun _ _ _ ↦ Finset.mem_univ _)
      (fun a₁ _ _ a₂ _ _ h ↦
        Subtype.ext
          (MulAction.mem_fixedPoints'.mp a₂.2 a₁.1
            (Quotient.exact' h)))
      (fun b ↦ Quotient.inductionOn' b fun b _ hb ↦ ?_)
      (fun a _ _ ↦ (orbitWeight_eq_of_fixed a.1 a.2).symm))
  have hfixed : b ∈ MulAction.fixedPoints Q alpha := by
    by_contra hnot
    exact hb (orbitWeight_eq_zero_of_not_fixed b hnot)
  have hfb : f b ≠ 0 := by
    intro hzero
    exact hb ((orbitWeight_eq_of_fixed b hfixed).trans hzero)
  exact ⟨⟨b, hfixed⟩, Finset.mem_univ _, hfb, rfl⟩

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
