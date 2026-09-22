import ModularRep.CentralIdempotentSupport
import Mathlib.RepresentationTheory.Irreducible

/-!
# Central idempotent support of an irreducible representation

This file specialises the abstract support theorem to the group algebra
module attached to an irreducible representation.  It is the algebraic step
used when a complete family of central idempotents partitions irreducible
modules.  Primitivity and block theoretic interpretations are not assumed.
-/

open scoped MonoidAlgebra

namespace Representation

variable {k G V ι : Type*}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]
variable [Fintype ι]

/-- An irreducible representation has a unique support in every complete
family of central orthogonal idempotents of its group algebra. -/
theorem existsUnique_centralIdempotentSupport
    (rho : Representation k G V) [rho.IsIrreducible]
    {e : ι → k[G]} (E : ModularRep.CompleteOrthogonalCentralIdempotents e) :
    ∃! i, ModularRep.CompleteOrthogonalCentralIdempotents.IsSupport
      (V := rho.asModule) e i :=
  E.existsUnique_isSupport (V := rho.asModule)

/-- The support index of an irreducible representation for a complete family
of central orthogonal idempotents of its group algebra. -/
noncomputable def centralIdempotentSupport
    (rho : Representation k G V) [rho.IsIrreducible]
    {e : ι → k[G]} (E : ModularRep.CompleteOrthogonalCentralIdempotents e) : ι :=
  E.support (V := rho.asModule)

@[simp]
theorem centralIdempotentSupport_smul
    (rho : Representation k G V) [rho.IsIrreducible]
    {e : ι → k[G]} (E : ModularRep.CompleteOrthogonalCentralIdempotents e)
    (v : rho.asModule) :
    e (rho.centralIdempotentSupport E) • v = v :=
  E.support_smul (V := rho.asModule) v

theorem centralIdempotent_smul_eq_zero_of_ne_support
    (rho : Representation k G V) [rho.IsIrreducible]
    {e : ι → k[G]} (E : ModularRep.CompleteOrthogonalCentralIdempotents e)
    {i : ι} (hi : i ≠ rho.centralIdempotentSupport E) (v : rho.asModule) :
    e i • v = 0 :=
  E.smul_eq_zero_of_ne_support (V := rho.asModule) hi v

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
