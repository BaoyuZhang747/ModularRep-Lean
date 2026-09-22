import ModularRep.ConformalFactorization
import ModularRep.PrimeRegularClassFunction

/-!
# Prime regular class functions under conformal conjugation

This file proves the value-function core of the Brauer-character assertion
in manuscript Proposition 3.9.  Under explicit multiplier and central-scalar
hypotheses, conjugation by the conformal overgroup fixes every prime regular
class function on the multiplier kernel.

It does not identify the abstract kernel with a symplectic group, construct
the concrete conformal multiplier, package irreducible Brauer characters as
a subtype, or identify the manuscript action on that subtype with the twist
used here.
-/

namespace ModularRep.ManuscriptVerification.ConformalCharacterFixed

variable {C F R : Type*} [Group C] [Group F] {p : ℕ}

/-- A central square lift makes conjugation by the overgroup fix every
prime regular class function on the multiplier kernel. -/
theorem primeRegularClassFunction_fixed
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : F, scalar a ∈ Subgroup.center C)
    (square_surjective : Function.Surjective (fun a : F ↦ a ^ 2))
    (f : PrimeRegularClassFunction R multiplier.ker p) (c : C) :
    f.twist (MulAut.conjNormal (H := multiplier.ker) c) = f := by
  obtain ⟨k, hk⟩ :=
    ConformalFactorization.exists_ker_factor_conjNormal_eq_inner
      multiplier scalar multiplier_scalar scalar_central square_surjective c
  rw [hk]
  exact PrimeRegularClassFunction.twist_conj f k

/-- Odd cardinality of the multiplier group supplies square-surjectivity in
`primeRegularClassFunction_fixed`. -/
theorem primeRegularClassFunction_fixed_of_odd_card
    [Finite F] (hOdd : Odd (Nat.card F))
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : F, scalar a ∈ Subgroup.center C)
    (f : PrimeRegularClassFunction R multiplier.ker p) (c : C) :
    f.twist (MulAut.conjNormal (H := multiplier.ker) c) = f :=
  primeRegularClassFunction_fixed multiplier scalar multiplier_scalar
    scalar_central (pow_two_bijective_of_odd_card hOdd).surjective f c

end ModularRep.ManuscriptVerification.ConformalCharacterFixed


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
