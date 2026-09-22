import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group

/-!
# Removing an inner twist from conjugacy

Lemma 4.7 of the manuscript uses that the Frobenius action on a component
group is inner.  Rational classes are parametrised by twisted conjugacy
classes, and multiplication by `c⁻ᶠ` identifies those classes with ordinary
conjugacy classes when the twisting automorphism is conjugation by `cᶠ`.

The two identities below formalise that algebraic calculation.  The cited
parametrisation of rational unipotent classes and the assertion that the
Frobenius action is inner remain external representation theoretic inputs.
-/

namespace Formalisation.InnerTwistedConjugacy

variable {A : Type*} [Group A]

/-- The element map used to remove the `f`th inner twist. -/
def untwist (c : A) (f : ℕ) (x : A) : A := (c ^ f)⁻¹ * x

/-- A conjugacy relation twisted by conjugation with `cᶠ` becomes an
ordinary conjugacy relation after applying `untwist`. -/
theorem untwist_twisted_conjugate (c g x : A) (f : ℕ) :
    untwist c f ((c ^ f) * g * (c ^ f)⁻¹ * x * g⁻¹) =
      g * untwist c f x * g⁻¹ := by
  simp only [untwist]
  group

/-- Applying another power of the same inner automorphism becomes ordinary
conjugation on the untwisted parameter. -/
theorem untwist_inner_power (c x : A) (e f : ℕ) :
    untwist c f ((c ^ e) * x * (c ^ e)⁻¹) =
      (c ^ e) * untwist c f x * (c ^ e)⁻¹ := by
  simp only [untwist]
  group

end Formalisation.InnerTwistedConjugacy


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
