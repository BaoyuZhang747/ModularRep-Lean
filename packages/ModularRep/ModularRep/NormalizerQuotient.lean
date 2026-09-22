import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The normaliser quotient

The local quotient of a subgroup by its copy in its normaliser.
-/

namespace ModularRep

universe v

variable {G : Type v} [Group G]

/-- The local quotient `N_G(Q) / Q`.  The subgroup `Q` is normal in its
normaliser by construction. -/
abbrev NormalizerQuotient (Q : Subgroup G) :=
  Subgroup.normalizer (Q : Set G) ⧸
    Q.subgroupOf (Subgroup.normalizer (Q : Set G))

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
