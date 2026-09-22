import ModularRep.PrimeRegular
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RepresentationTheory.Basic

/-!
# Eigenvalues of prime regular elements

For a finite group `G`, `primeRegularExponent p G` is the part of `|G|`
prime to `p`.  Every `p`-regular group element, and hence every eigenvalue of
its action in a finite dimensional representation, is killed by this
exponent.  This is the elementary input needed to lift modular eigenvalues in
the construction of Brauer-character values.
-/

namespace ModularRep

universe u v w

/-- The part of the order of a finite group prime to `p`. -/
noncomputable def primeRegularExponent (p : ℕ) (G : Type u) [Finite G] : ℕ :=
  ordCompl[p] (Nat.card G)

/-- The prime regular exponent of a finite nonempty type is positive. -/
theorem primeRegularExponent_pos (p : ℕ) (G : Type u) [Finite G] [Nonempty G] :
    0 < primeRegularExponent p G :=
  Nat.ordCompl_pos p Nat.card_pos.ne'

namespace PrimeRegularElement

variable {G : Type u} {p : ℕ}

/-- Every `p`-regular element of a finite group is killed by the part of the
group order prime to `p`. -/
@[simp]
theorem pow_primeRegularExponent_eq_one [Group G] [Finite G]
    (hp : p.Prime) (g : PrimeRegularElement (G := G) p) :
    g.1 ^ primeRegularExponent p G = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  exact Nat.dvd_ordCompl_of_dvd_not_dvd (orderOf_dvd_natCard g.1)
    ((isPrimeRegular_iff_not_dvd hp g.1).mp g.2)

end PrimeRegularElement

end ModularRep

namespace Representation

variable {k : Type w} {G : Type u} {V : Type v} {p : ℕ}
variable [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/-- A root of the characteristic polynomial of a `p`-regular representation
matrix is killed by the prime regular exponent of the group. -/
theorem charpolyIsRoot_pow_primeRegularExponent_eq_one
    (rho : Representation k G V) (hp : p.Prime)
    (g : ModularRep.PrimeRegularElement (G := G) p) {a : k}
    (ha : (rho g.1).charpoly.IsRoot a) :
    a ^ ModularRep.primeRegularExponent p G = 1 := by
  have haEigen : Module.End.HasEigenvalue (rho g.1) a :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (rho g.1) a).2 ha
  obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector haEigen
  apply smul_left_injective k hv.2
  change a ^ ModularRep.primeRegularExponent p G • v = (1 : k) • v
  rw [one_smul, ← hv.pow_apply (ModularRep.primeRegularExponent p G),
    ← map_pow,
    ModularRep.PrimeRegularElement.pow_primeRegularExponent_eq_one hp g,
    map_one, Module.End.one_apply]

/-- Membership in the multiset of characteristic-polynomial roots gives the
same exponent conclusion. -/
theorem charpolyRoot_pow_primeRegularExponent_eq_one
    (rho : Representation k G V) (hp : p.Prime)
    (g : ModularRep.PrimeRegularElement (G := G) p) {a : k}
    (ha : a ∈ (rho g.1).charpoly.roots) :
    a ^ ModularRep.primeRegularExponent p G = 1 := by
  apply rho.charpolyIsRoot_pow_primeRegularExponent_eq_one hp g
  exact (Polynomial.mem_roots (rho g.1).charpoly_monic.ne_zero).mp ha

end Representation



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
