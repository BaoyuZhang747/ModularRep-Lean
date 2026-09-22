import Mathlib.GroupTheory.IsPerfect

/-!
# Neutral source predicates for universal central covers

This module contains the group-theoretic predicates shared by the fixed
Feng--Li--Zhang Theorem 3.18 and Theorem 5.7 gates.  It contains no
Theorem 3.18, Theorem 5.7, Brough--Spaeth, equation-(3.17), BAW-goodness, or
iBAW endpoint.

The declarations intentionally retain their established
`EvenFieldFLZ318FixedTheoremGate` namespace so existing source users and
aggregate trust gates keep their names while the Theorem 5.7 gate no longer
imports the Theorem 3.18 application module.
-/

namespace ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate

universe u

open scoped commutatorElement

/-- A surjective group homomorphism whose kernel is central. -/
def IsCentralExtension {U V : Type u} [Group U] [Group V]
    (f : U →* V) : Prop :=
  Function.Surjective f ∧ f.ker ≤ Subgroup.center U

/-- The universal property of a central extension, restricted to groups in
the same universe as its source and target. -/
def IsUniversalCentralExtension {U V : Type u} [Group U] [Group V]
    (u : U →* V) : Prop :=
  IsCentralExtension u ∧
    ∀ (D : Type u) [Group D] (f : D →* V), IsCentralExtension f →
      ∃! lift : U →* D, f.comp lift = u

/-- The fixed predicate saying that a group, with the identity map to itself,
is its own full universal central cover. -/
def IsOwnUniversalCover (H : Type u) [Group H] : Prop :=
  IsUniversalCentralExtension (MonoidHom.id H)

/-- A section of a central extension of a perfect group is surjective.

The perfectness hypothesis is on the total group `U`, not the quotient `V`.
This is the group-theoretic input needed to turn the universal lifting property
of the identity central extension into the maximality clause for the canonical
identity prime-to-`ell` cover. -/
theorem centralExtension_section_surjective
    {U V : Type u} [Group U] [Group V]
    (f : U →* V) (hcentral : f.ker ≤ Subgroup.center U)
    (s : V →* U) (hs : f.comp s = MonoidHom.id V)
    (hperfect : commutator U = ⊤) :
    Function.Surjective s := by
  have hsection : Function.LeftInverse f s := by
    intro v
    change (f.comp s) v = v
    rw [hs]
    rfl
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← hperfect, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have hx : (s (f x))⁻¹ * x ∈ Subgroup.center U :=
    hcentral ((MonoidHom.eq_iff f).mp (hsection (f x)).symm)
  have hy : (s (f y))⁻¹ * y ∈ Subgroup.center U :=
    hcentral ((MonoidHom.eq_iff f).mp (hsection (f y)).symm)
  have hxcomm : Commute ((s (f x))⁻¹ * x) y :=
    (Subgroup.mem_center_iff.mp hx y).symm
  have hycomm : Commute (s (f x)) ((s (f y))⁻¹ * y) :=
    Subgroup.mem_center_iff.mp hy (s (f x))
  refine ⟨⁅f x, f y⁆, ?_⟩
  rw [map_commutatorElement]
  symm
  calc
    ⁅x, y⁆ = ⁅s (f x) * ((s (f x))⁻¹ * x), y⁆ := by
      rw [mul_inv_cancel_left]
    _ = ⁅s (f x), y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul,
        hxcomm.commutator_eq]
      simp
    _ = ⁅s (f x), s (f y) * ((s (f y))⁻¹ * y)⁆ := by
      rw [mul_inv_cancel_left]
    _ = ⁅s (f x), s (f y)⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        hycomm.commutator_eq]
      simp

end ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
