import ModularRep.PCore
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Quotients of cyclic groups by the `p`-core

This module formalises the cyclic-group special case of the
`p`-hypoelementary condition used in the even-field unipotent argument.
Mathlib has the ingredients (`IsPGroup`, `IsCyclic`, quotient groups, and
Sylow theory), while `ModularRep.PCore` supplies the project's definition of
the `p`-core.

The cyclicity theorems are valid for Mathlib's generalised `p`-group notions
at an arbitrary natural number.  Their standard finite group interpretation,
and every assertion about `p'`-order below, assumes that `p` is prime.
-/

namespace ModularRep

/-- Every quotient of a cyclic group is cyclic. -/
theorem isCyclic_quotient_of_isCyclic
    {G : Type*} [Group G] [IsCyclic G]
    (N : Subgroup G) :
    IsCyclic (G ⧸ N) :=
  isCyclic_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)

/-- A cyclic group has cyclic quotient by its `p`-core.

No finiteness hypothesis and no primality hypothesis on `p` are required.
-/
theorem isCyclic_quotient_pCore
    (p : ℕ) (G : Type*) [Group G] [IsCyclic G] :
    IsCyclic (G ⧸ pCore p G) :=
  isCyclic_quotient_of_isCyclic (pCore p G)

/-- Every subgroup of a cyclic group has cyclic quotient by its `p`-core.

This is the form directly matching the finite group application.  It is
stronger than that application because neither the ambient group nor the
subgroup is assumed finite, and `p` need not be prime.
-/
theorem isCyclic_subgroup_quotient_pCore
    {G : Type*} [Group G] [IsCyclic G]
    (p : ℕ) (H : Subgroup G) :
    IsCyclic (H ⧸ pCore p H) := by
  let _ : IsCyclic H := Subgroup.isCyclic H
  exact isCyclic_quotient_pCore p H

/-- A normal Sylow `p`-subgroup is the `p`-core. -/
theorem pCore_eq_sylow_of_normal
    {G : Type*} [Group G] {p : ℕ}
    (P : Sylow p G) [P.Normal] :
    pCore p G = (P : Subgroup G) := by
  apply le_antisymm
  · exact (pCore_isPGroup p G).le_sylow_of_normal P
  · exact normal_pSubgroup_le_pCore (G := G) p (P : Subgroup G) P.isPGroup'

/-- In a cyclic group, every Sylow `p`-subgroup is the `p`-core. -/
theorem pCore_eq_sylow_of_isCyclic
    {G : Type*} [Group G] [IsCyclic G]
    {p : ℕ} (P : Sylow p G) :
    pCore p G = (P : Subgroup G) :=
  pCore_eq_sylow_of_normal P

/-- For a finite cyclic group, the quotient by its `p`-core has order prime
to `p` (stated in the equivalent divisibility form used by Sylow theory). -/
theorem not_dvd_card_quotient_pCore_of_isCyclic
    {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} [Fact p.Prime] :
    ¬ p ∣ Nat.card (G ⧸ pCore p G) := by
  let P : Sylow p G := default
  rw [pCore_eq_sylow_of_isCyclic P, ← P.index_eq_card]
  exact P.not_dvd_index

/-- Subgroup form of `not_dvd_card_quotient_pCore_of_isCyclic`.  Together with
`isCyclic_subgroup_quotient_pCore`, this recovers both group-theoretic pieces
of the usual finite `p`-hypoelementary condition. -/
theorem not_dvd_card_subgroup_quotient_pCore_of_isCyclic
    {G : Type*} [Group G] [IsCyclic G]
    {p : ℕ} [Fact p.Prime] (H : Subgroup G) [Finite H] :
    ¬ p ∣ Nat.card (H ⧸ pCore p H) := by
  let _ : IsCyclic H := Subgroup.isCyclic H
  exact not_dvd_card_quotient_pCore_of_isCyclic

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
