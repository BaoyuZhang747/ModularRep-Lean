import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RepresentationTheory.Basic

/-!
# Change of scalars for representations

This file supplies the two scalar-change constructions needed for integral
lattices and modular reduction: restriction along an algebra map and tensor
extension along an algebra map.
-/

open scoped TensorProduct

namespace Representation

universe uR uS uG uV

section RestrictScalars

variable (R : Type uR) {S : Type uS} {G : Type uG} {V : Type uV}
variable [CommSemiring R] [Semiring S] [Algebra R S] [Monoid G]
variable [AddCommMonoid V] [Module R V] [Module S V] [IsScalarTower R S V]

/-- Restrict the coefficient ring of a representation along an algebra map. -/
def restrictScalars (rho : Representation S G V) : Representation R G V where
  toFun g := (rho g).restrictScalars R
  map_one' := by
    ext v
    change rho 1 v = v
    simp
  map_mul' g h := by
    ext v
    change rho (g * h) v = rho g (rho h v)
    simp [← Module.End.mul_apply]

@[simp]
theorem restrictScalars_apply (rho : Representation S G V) (g : G) (v : V) :
    rho.restrictScalars R g v = rho g v :=
  rfl

end RestrictScalars

section BaseChange

variable (S : Type uS) {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommSemiring R] [Semiring S] [Algebra R S] [Monoid G]
variable [AddCommMonoid V] [Module R V]

/-- Extend the coefficient ring of a representation by tensor product. -/
def baseChange (rho : Representation R G V) :
    Representation S G (S ⊗[R] V) :=
  (Module.End.baseChangeHom R S V).toMonoidHom.comp rho

@[simp]
theorem baseChange_apply_tmul (rho : Representation R G V)
    (g : G) (s : S) (v : V) :
    rho.baseChange S g (s ⊗ₜ[R] v) = s ⊗ₜ[R] rho g v :=
  rfl

end BaseChange

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
