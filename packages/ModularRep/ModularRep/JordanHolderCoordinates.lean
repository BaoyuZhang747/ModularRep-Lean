import ModularRep.ExactGrothendieckGroup
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.FiniteLength

/-!
# Jordan--Hölder coordinates for finite-length modules

For a composition series, this file forms the sum of the isomorphism classes
of its simple factors in the free abelian group on module isomorphism classes.
Jordan--Hölder proves that this sum, and hence every factor multiplicity, is
independent of the chosen series with fixed endpoints.

No quotient by exact-sequence relations is taken here.  In particular, these
coordinates retain their information and do not pass through the trivial
exact `K₀` of the category of all modules.
-/

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace ModularRep.JordanHolderCoordinates

universe u

variable {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- The quotient attached to one step of a composition series. -/
abbrev compositionFactor (s : CompositionSeries (Submodule R M))
    (i : Fin s.length) : Type u :=
  s (Fin.succ i) ⧸ (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype

/-- Every step quotient in a composition series is simple. -/
theorem compositionFactor_isSimple (s : CompositionSeries (Submodule R M))
    (i : Fin s.length) : IsSimpleModule R (compositionFactor s i) := by
  exact (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)

/-- The formal sum of the isomorphism classes of the simple factors. -/
noncomputable def compositionFactorIsoSum
    (s : CompositionSeries (Submodule R M)) :
    ExactGrothendieckGroup.FreeClassGroup (ModuleCat.{u} R) :=
  ∑ i : Fin s.length,
    FreeAbelianGroup.of
      (toSkeleton (ModuleCat.of R (compositionFactor s i)))

/-- Jordan--Hölder gives equality of the formal factor sums before imposing
any exact-sequence relations. -/
theorem compositionFactorIsoSum_eq
    (s₁ s₂ : CompositionSeries (Submodule R M))
    (hhead : s₁.head = s₂.head) (hlast : s₁.last = s₂.last) :
    compositionFactorIsoSum s₁ = compositionFactorIsoSum s₂ := by
  classical
  let h := CompositionSeries.jordan_holder s₁ s₂ hhead hlast
  refine Fintype.sum_equiv h.choose _ _ ?_
  intro i
  apply congrArg FreeAbelianGroup.of
  exact congr_toSkeleton_of_iso
    (JordanHolderLattice.Iso.linearEquiv (h.choose_spec i)).toModuleIso

/-- The integer coefficient of a module isomorphism class in the formal
factor sum. -/
noncomputable def compositionCoefficient
    (s : CompositionSeries (Submodule R M))
    (X : Skeleton (ModuleCat.{u} R)) : ℤ :=
  FreeAbelianGroup.toFinsupp (compositionFactorIsoSum s) X

open scoped Classical in
theorem compositionCoefficient_eq_sum_ite
    (s : CompositionSeries (Submodule R M))
    (X : Skeleton (ModuleCat.{u} R)) :
    compositionCoefficient s X =
      ∑ i : Fin s.length,
        if toSkeleton (ModuleCat.of R (compositionFactor s i)) = X
        then 1 else 0 := by
  classical
  unfold compositionCoefficient compositionFactorIsoSum
  rw [map_sum]
  change Finsupp.applyAddHom X
      (∑ i : Fin s.length,
        FreeAbelianGroup.toFinsupp
          (FreeAbelianGroup.of
            (toSkeleton (ModuleCat.of R (compositionFactor s i))))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [FreeAbelianGroup.toFinsupp_of]
  exact Finsupp.single_apply

/-- Each coefficient is independent of the chosen composition series. -/
theorem compositionCoefficient_eq
    (s₁ s₂ : CompositionSeries (Submodule R M))
    (hhead : s₁.head = s₂.head) (hlast : s₁.last = s₂.last)
    (X : Skeleton (ModuleCat.{u} R)) :
    compositionCoefficient s₁ X = compositionCoefficient s₂ X := by
  rw [compositionCoefficient, compositionCoefficient,
    compositionFactorIsoSum_eq s₁ s₂ hhead hlast]

/-- The canonical short complex for one inclusion in a composition series
and its quotient. -/
noncomputable def compositionStepShortComplex
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk
    (Submodule.inclusion (s.step i).le)
    ((s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype).mkQ
    (by
      ext x
      simp [Submodule.inclusion])

/-- The complex for a composition-series step is short exact. -/
theorem compositionStepShortComplex_shortExact
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (compositionStepShortComplex s i).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · rw [LinearMap.exact_iff]
    change
      LinearMap.ker
          ((s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype).mkQ =
        LinearMap.range (Submodule.inclusion (s.step i).le)
    rw [Submodule.ker_mkQ, Submodule.range_inclusion]
  · exact Submodule.inclusion_injective (s.step i).le
  · exact Submodule.mkQ_surjective _

end ModularRep.JordanHolderCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
