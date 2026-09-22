import Mathlib.Logic.Equiv.Basic

/-!
# Orienting a seed involution-equivariant equivalence

The predicate `R x (seed x)` is constant on each involution orbit. On an
orbit where it fails, switch both character points before applying the
seed. This gives an equivariant equivalence with the same orbit map.
If one of the two character orientations is related to each seed weight,
the resulting equivalence satisfies that relation pointwise.

This is a conditional elementary construction, not an external source.
In a literal triple application, the relation, its simultaneous covariance
and its representative quantifiers must first be bound and proved. No
representation theoretic predicate or certificate is introduced here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrincipalOrbitOrientation

universe u v w

variable {X : Type u} {Y : Type v}
  (sigma : Equiv.Perm X) (tau : Equiv.Perm Y)
  (sigma_involutive : Function.Involutive sigma)
  (seed : X ≃ Y) (seed_equivariant : ∀ x, seed (sigma x) = tau (seed x))
  (R : X → Y → Prop)
  (simultaneous : ∀ x y, R (sigma x) (tau y) ↔ R x y)

/-- The switch tests the seed pair itself. It does not choose a new orbit. -/
def orientPoint (x : X) : X := by
  classical
  exact if R x (seed x) then x else sigma x

include sigma_involutive seed_equivariant in
/-- The target involution law already follows from the seed square. -/
theorem target_involutive : Function.Involutive tau := by
  intro y
  obtain ⟨x, rfl⟩ := seed.surjective y
  rw [← seed_equivariant, ← seed_equivariant, sigma_involutive]

include seed_equivariant simultaneous in
theorem seedRelation_step (x : X) :
    R (sigma x) (seed (sigma x)) ↔ R x (seed x) := by
  rw [seed_equivariant]
  exact simultaneous x (seed x)

include seed_equivariant simultaneous in
theorem orientPoint_equivariant (x : X) :
    orientPoint sigma seed R (sigma x) = sigma (orientPoint sigma seed R x) := by
  classical
  by_cases hx : R x (seed x)
  · have hs := (seedRelation_step sigma tau seed seed_equivariant R simultaneous x).mpr hx
    simp only [orientPoint, if_pos hx, if_pos hs]
  · have hs : ¬ R (sigma x) (seed (sigma x)) :=
      fun h => hx ((seedRelation_step sigma tau seed seed_equivariant R simultaneous x).mp h)
    simp only [orientPoint, if_neg hx, if_neg hs]

include sigma_involutive seed_equivariant simultaneous in
theorem orientPoint_involutive : Function.Involutive (orientPoint sigma seed R) := by
  classical
  intro x
  by_cases hx : R x (seed x)
  · simp only [orientPoint, if_pos hx]
  · have hs : ¬ R (sigma x) (seed (sigma x)) :=
      fun h => hx ((seedRelation_step sigma tau seed seed_equivariant R simultaneous x).mp h)
    simp only [orientPoint, if_neg hx, if_neg hs, sigma_involutive x]

/-- The orbitwise switch is its own inverse. -/
def characterOrientation : Equiv.Perm X where
  toFun := orientPoint sigma seed R
  invFun := orientPoint sigma seed R
  left_inv := orientPoint_involutive sigma tau sigma_involutive seed seed_equivariant R simultaneous
  right_inv := orientPoint_involutive sigma tau sigma_involutive seed seed_equivariant R simultaneous

/-- Reorientation is precomposition of the seed by that actual character switch. -/
def orientedEquiv : X ≃ Y :=
  (characterOrientation sigma tau sigma_involutive seed seed_equivariant R simultaneous).trans seed

theorem orientPoint_eq_or_step (x : X) :
    orientPoint sigma seed R x = x ∨ orientPoint sigma seed R x = sigma x := by
  classical
  by_cases hx : R x (seed x)
  · exact Or.inl (if_pos hx)
  · exact Or.inr (if_neg hx)

theorem orientedEquiv_equivariant (x : X) :
    orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous (sigma x) =
      tau (orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x) := by
  change seed (orientPoint sigma seed R (sigma x)) = tau (seed (orientPoint sigma seed R x))
  rw [orientPoint_equivariant sigma tau seed seed_equivariant R simultaneous, seed_equivariant]

/-- The oriented character is sent to exactly the original seed weight. -/
theorem orientedEquiv_orientPoint (x : X) :
    orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous
        (orientPoint sigma seed R x) = seed x := by
  change seed (orientPoint sigma seed R (orientPoint sigma seed R x)) = seed x
  rw [orientPoint_involutive sigma tau sigma_involutive seed seed_equivariant R simultaneous x]

/-- Pointwise preservation of the seed's target orbit. -/
theorem orientedEquiv_sameOrbit (x : X) :
    orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x = seed x ∨
      orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x =
        tau (seed x) := by
  rcases orientPoint_eq_or_step sigma seed R x with hx | hx
  · exact Or.inl (congrArg seed hx)
  · exact Or.inr ((congrArg seed hx).trans (seed_equivariant x))

/-- In particular every invariant orbit label has the same induced map. -/
theorem orientedEquiv_orbitLabel {I : Type w} (label : Y → I)
    (label_invariant : ∀ y, label (tau y) = label y) (x : X) :
    label (orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x) =
      label (seed x) := by
  rcases orientedEquiv_sameOrbit sigma tau sigma_involutive seed seed_equivariant R simultaneous x
    with hx | hx
  · exact congrArg label hx
  · exact (congrArg label hx).trans (label_invariant (seed x))

/-- The inverse selects one of exactly the two original character orientations. -/
theorem orientedEquiv_symm_orientation (y : Y) :
    (orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous).symm y =
        seed.symm y ∨
      (orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous).symm y =
        sigma (seed.symm y) := by
  change orientPoint sigma seed R (seed.symm y) = seed.symm y ∨
    orientPoint sigma seed R (seed.symm y) = sigma (seed.symm y)
  exact orientPoint_eq_or_step sigma seed R (seed.symm y)

/-- Fixed character points retain the seed's exact value. -/
theorem orientedEquiv_fixed_unchanged (x : X) (hx : sigma x = x) :
    orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x = seed x := by
  rcases orientPoint_eq_or_step sigma seed R x with hs | hs
  · exact congrArg seed hs
  · exact congrArg seed (hs.trans hx)

/-- This is precisely the fixed/free stabilizer distinction for an involution. -/
theorem orientedEquiv_fixed_iff (x : X) :
    tau (orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x) =
        orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x ↔
      sigma x = x := by
  rw [← orientedEquiv_equivariant]
  exact (orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous).injective.eq_iff

theorem orientedEquiv_free_iff (x : X) :
    tau (orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x) ≠
        orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x ↔
      sigma x ≠ x :=
  not_congr (orientedEquiv_fixed_iff sigma tau sigma_involutive seed seed_equivariant R simultaneous x)

variable (oneOrientation : ∀ x, R x (seed x) ∨ R (sigma x) (seed x))

include oneOrientation in
/-- The original weight point stays fixed while its character orientation is selected. -/
theorem orientPoint_related (x : X) : R (orientPoint sigma seed R x) (seed x) := by
  classical
  by_cases hx : R x (seed x)
  · simpa only [orientPoint, if_pos hx] using hx
  · simpa only [orientPoint, if_neg hx] using (oneOrientation x).resolve_left hx

include oneOrientation in
/-- The final equivalence satisfies the relation at every actual point. -/
theorem orientedEquiv_related (x : X) :
    R x (orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous x) := by
  have h := orientPoint_related sigma seed R oneOrientation (orientPoint sigma seed R x)
  rw [orientPoint_involutive sigma tau sigma_involutive seed seed_equivariant R simultaneous x] at h
  exact h

include oneOrientation in
theorem orientedEquiv_symm_related (y : Y) :
    R ((orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous).symm y) y := by
  have h := orientedEquiv_related sigma tau sigma_involutive seed seed_equivariant R simultaneous
    oneOrientation ((orientedEquiv sigma tau sigma_involutive seed seed_equivariant R simultaneous).symm y)
  simpa only [Equiv.apply_symm_apply] using h

end ModularRep.PaperProofs.TypeBPrincipalOrbitOrientation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
