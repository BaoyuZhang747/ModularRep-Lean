import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.FiniteLength

/-!
# Finite length of finite-dimensional representations

The underlying `k[G]`-module of a finite-dimensional representation has
finite length.  The functor below is useful for constructing its composition
series, but no map to the exact `K₀` of all modules is defined: that target is
trivial by `ModuleCategoryKZeroTrivial.kZero_subsingleton`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

namespace ModularRep.FDRepFiniteLength

universe u

variable {k G : Type u} [Field k] [Monoid G]

/-- The underlying `k[G]`-module functor on finite-dimensional
representations. -/
noncomputable abbrev toModuleMonoidAlgebra :
    FDRep k G ⥤ ModuleCat.{u} k[G] :=
  forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra

noncomputable instance :
    PreservesFiniteLimits (toModuleMonoidAlgebra (k := k) (G := G)) :=
  comp_preservesFiniteLimits _ _

noncomputable instance :
    PreservesFiniteColimits (toModuleMonoidAlgebra (k := k) (G := G)) :=
  comp_preservesFiniteColimits _ _

/-- A finite-dimensional representation has finite length as a module over
the monoid algebra. -/
theorem asModule_isFiniteLength (V : FDRep k G) :
    IsFiniteLength k[G] (Representation.asModule V.ρ) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  constructor
  · exact isNoetherian_of_tower k
      (inferInstance : IsNoetherian k (Representation.asModule V.ρ))
  · exact isArtinian_of_tower k
      (inferInstance : IsArtinian k (Representation.asModule V.ρ))

/-- Every finite-dimensional representation admits a composition series as
a module over the monoid algebra. -/
theorem exists_compositionSeries (V : FDRep k G) :
    ∃ s : CompositionSeries
        (Submodule k[G] (Representation.asModule V.ρ)),
      s.head = ⊥ ∧ s.last = ⊤ :=
  isFiniteLength_iff_exists_compositionSeries.mp (asModule_isFiniteLength V)

end ModularRep.FDRepFiniteLength


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
