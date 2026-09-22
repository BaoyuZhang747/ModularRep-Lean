import ModularRep.CentralIdempotentSupport
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Transport of central idempotent support

This file supplies abstract support transport intended for a later
formalisation of central character sectors.  It remains deliberately at the
level of modules and central idempotents: no Brauer character, sector, or
block theory is asserted here.

If a semilinear equivalence carries a complete family of central idempotents
to another such family, up to a permutation of its indices, then it carries
the unique support index by the same permutation.  Taking the ring
equivalence to be an automorphism gives the usual twisting situation.
-/

namespace ModularRep

namespace CompleteOrthogonalCentralIdempotents

attribute [local instance] RingHomInvPair.of_ringEquiv

variable {A A' V V' ι ι' : Type*}
variable [Ring A] [Ring A'] [AddCommGroup V] [AddCommGroup V']
variable [Module A V] [Module A' V']

/-- A semilinear equivalence transports the support predicate when it carries
the idempotent family according to the indicated permutation of indices. -/
theorem IsSupport.map_semilinear
    {e : ι → A} {e' : ι' → A'}
    (σ : A ≃+* A') (τ : ι ≃ ι')
    (f : V ≃ₛₗ[(σ : A →+* A')] V')
    (hfamily : ∀ i, σ (e i) = e' (τ i))
    {i : ι} (hi : IsSupport (V := V) e i) :
    IsSupport (V := V') e' (τ i) := by
  constructor
  · intro v'
    obtain ⟨v, rfl⟩ := f.surjective v'
    calc
      e' (τ i) • f.toFun v = σ (e i) • f.toFun v := by rw [hfamily i]
      _ = f.toFun (e i • v) := (f.toLinearMap.map_smulₛₗ (e i) v).symm
      _ = f.toFun v := congrArg f.toFun (hi.1 v)
  · intro j' hj' v'
    obtain ⟨j, rfl⟩ := τ.surjective j'
    have hji : j ≠ i := by
      intro h
      exact hj' (congrArg τ h)
    obtain ⟨v, rfl⟩ := f.surjective v'
    calc
      e' (τ j) • f.toFun v = σ (e j) • f.toFun v := by rw [hfamily j]
      _ = f.toFun (e j • v) := (f.toLinearMap.map_smulₛₗ (e j) v).symm
      _ = f.toFun 0 := congrArg f.toFun (hi.2 j hji v)
      _ = 0 := f.toLinearMap.map_zero

variable [Fintype ι] [Fintype ι']
variable [IsSimpleModule A V] [IsSimpleModule A' V']

/-- The unique support index is transported by a semilinear equivalence that
permutes the two complete central idempotent families. -/
theorem support_map_semilinear
    {e : ι → A} {e' : ι' → A'}
    (E : CompleteOrthogonalCentralIdempotents e)
    (E' : CompleteOrthogonalCentralIdempotents e')
    (σ : A ≃+* A') (τ : ι ≃ ι')
    (f : V ≃ₛₗ[(σ : A →+* A')] V')
    (hfamily : ∀ i, σ (e i) = e' (τ i)) :
    τ (E.support (V := V)) = E'.support (V := V') := by
  apply E'.support_unique
  exact IsSupport.map_semilinear σ τ f hfamily (E.support_isSupport (V := V))

end CompleteOrthogonalCentralIdempotents

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
