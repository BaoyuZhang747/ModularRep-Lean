import ModularRep.CentralAction
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Characteristic polynomials of scalar actions

This file computes the characteristic polynomial and its multiset of roots for
a scalar endomorphism.  The final theorem applies the computation to the
central character of an irreducible representation.  The roots are mapped
individually before they are summed, so the map used to lift roots need not be
additive.
-/

open Polynomial

namespace Representation

universe u v w

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The characteristic polynomial of scalar multiplication by `c`. -/
theorem charpoly_smul_id (c : k) :
    (c • LinearMap.id : Module.End k V).charpoly =
      (X - C c) ^ Module.finrank k V := by
  have h := LinearMap.charpoly_sub_smul
    (R := k) (M := V) (0 : Module.End k V) (-c)
  simpa [LinearMap.charpoly_zero, sub_eq_add_neg, Module.End.one_eq_id] using h

/-- The roots of the characteristic polynomial of scalar multiplication,
including multiplicity. -/
theorem roots_charpoly_smul_id (c : k) :
    (c • LinearMap.id : Module.End k V).charpoly.roots =
      Multiset.replicate (Module.finrank k V) c := by
  rw [charpoly_smul_id, Polynomial.roots_pow,
    Polynomial.roots_X_sub_C, Multiset.nsmul_singleton]

/-- At a central element, mapping and summing the characteristic-polynomial
roots gives the dimension times the mapped central character scalar. -/
theorem sum_map_roots_charpoly_centralCharacter
    {R : Type w} [AddCommMonoid R] (lift : k → R)
    {G : Type*} [Group G] [IsAlgClosed k]
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) (z : Z) :
    ((rho (z : G)).charpoly.roots.map lift).sum =
      Module.finrank k V • lift (rho.centralCharacter Z hZ z : k) := by
  rw [rho.centralCharacter_spec Z hZ z, roots_charpoly_smul_id,
    Multiset.map_replicate, Multiset.sum_replicate]

end Representation



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
