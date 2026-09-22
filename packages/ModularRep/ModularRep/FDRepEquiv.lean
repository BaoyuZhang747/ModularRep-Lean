import ModularRep.ExactGrothendieckGroup
import Mathlib.RepresentationTheory.Equiv

/-!
# From unbundled representation equivalences to `FDRep` isomorphisms

This small bridge allows representation-level equivalences to be used in the
categorical exact `K₀` presentation, whose generators are isomorphism classes
of objects of `FDRep`.
-/

open CategoryTheory

namespace Representation.Equiv

universe u v

variable {k : Type u} {G : Type v} {V W : Type u}
variable [Field k] [Monoid G]
variable [AddCommGroup V] [Module k V] [Module.Finite k V]
variable [AddCommGroup W] [Module k W] [Module.Finite k W]
variable {rho : Representation k G V} {sigma : Representation k G W}

/-- An equivalence of finite representations induces an isomorphism of their
bundled `FDRep` objects. -/
noncomputable def toFDRepIso (e : rho.Equiv sigma) :
    FDRep.of rho ≅ FDRep.of sigma := by
  refine Action.mkIso
    (LinearEquiv.toFGModuleCatIso e.toLinearEquiv) (fun g => ?_)
  ext x
  exact Representation.IntertwiningMap.isIntertwining
    rho sigma e.toIntertwiningMap g x

/-- Equivalent finite representations have the same class in the exact
Grothendieck-group presentation of `FDRep`. -/
theorem fdRepKZero_classOf_eq (e : rho.Equiv sigma) :
    ModularRep.ExactGrothendieckGroup.classOf (FDRep k G) (FDRep.of rho) =
      ModularRep.ExactGrothendieckGroup.classOf (FDRep k G) (FDRep.of sigma) :=
  ModularRep.ExactGrothendieckGroup.classOf_iso (FDRep k G) e.toFDRepIso

end Representation.Equiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
