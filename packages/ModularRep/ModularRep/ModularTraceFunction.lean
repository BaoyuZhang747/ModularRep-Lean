import Mathlib.RepresentationTheory.Character

/-!
# Modular trace functions on a group algebra

Navarro's trace-separation theorem is stated for the trace functions of
representations of a finite-dimensional algebra, whereas the project uses
the character of a group representation as a function on group elements.
This file defines the linear trace function on the group algebra and proves
that equality of the two kinds of trace functions is equivalent.
-/

noncomputable section

open scoped MonoidAlgebra

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Monoid G]
variable [AddCommGroup V] [Module k V]

/-- The trace of the linear extension of a representation to the monoid
algebra. -/
noncomputable def algebraTraceFunction
    (rho : Representation k G V) : k[G] →ₗ[k] k :=
  (LinearMap.trace k V).comp rho.asAlgebraHom.toLinearMap

@[simp]
theorem algebraTraceFunction_single
    (rho : Representation k G V) (g : G) (c : k) :
    rho.algebraTraceFunction (MonoidAlgebra.single g c) =
      c * rho.character g := by
  simp [algebraTraceFunction, character, smul_eq_mul]

@[simp]
theorem algebraTraceFunction_single_one
    (rho : Representation k G V) (g : G) :
    rho.algebraTraceFunction (MonoidAlgebra.single g 1) =
      rho.character g := by
  simp

variable {W : Type w}
variable [AddCommGroup W] [Module k W]

/-- Two group representations have the same trace function on the monoid
algebra if and only if their characters agree on every group element. -/
theorem algebraTraceFunction_eq_iff_character_eq
    (rho : Representation k G V) (sigma : Representation k G W) :
    rho.algebraTraceFunction = sigma.algebraTraceFunction ↔
      rho.character = sigma.character := by
  constructor
  · intro h
    funext g
    simpa only [algebraTraceFunction_single_one] using
      LinearMap.congr_fun h (MonoidAlgebra.single g 1)
  · intro h
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext
    intro c
    simp [congrFun h g]

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
