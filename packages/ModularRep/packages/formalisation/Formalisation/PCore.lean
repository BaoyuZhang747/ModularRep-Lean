import Formalisation.CyclicQuotient
import Mathlib.GroupTheory.Sylow

/-!
# The largest normal `p`-subgroup

This file constructs the `p`-core of a group as the supremum of its normal
`p`-subgroups.  It then proves the precise inheritance statement used in the
manuscript: if the quotient of a group by its `p`-core is cyclic, then the same
is true for every subgroup.
-/

namespace Formalisation

variable {G : Type*} [Group G]

/-- The `p`-core of `G`, defined as the supremum of all normal `p`-subgroups. -/
def pCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  sSup {P : Subgroup G | IsPGroup p P ∧ P.Normal}

/-- The `p`-core is a `p`-group. -/
theorem pCore_isPGroup (p : ℕ) (G : Type*) [Group G] :
    IsPGroup p (pCore p G) := by
  apply Sylow.sSup_of_normal
  · intro P hP
    exact hP.1
  · intro P hP
    exact hP.2

/-- The `p`-core is normal. -/
theorem pCore_normal (p : ℕ) (G : Type*) [Group G] :
    (pCore p G).Normal := by
  apply Subgroup.sSup_normal
  intro P hP
  exact hP.2

instance pCore_normal_instance (p : ℕ) (G : Type*) [Group G] :
    (pCore p G).Normal :=
  pCore_normal p G

/-- Every normal `p`-subgroup is contained in the `p`-core. -/
theorem normal_pSubgroup_le_pCore (p : ℕ) (P : Subgroup G)
    (hP : IsPGroup p P) [P.Normal] : P ≤ pCore p G := by
  apply le_sSup
  exact ⟨hP, inferInstance⟩

/-- If `A / O_p(A)` is cyclic, then `K / O_p(K)` is cyclic for every subgroup
`K` of `A`.  This is the exact group theoretic conclusion used in the
manuscript's proof that subgroups of a `p`-hypoelementary group are again
`p`-hypoelementary. -/
theorem subgroup_quotient_pCore_isCyclic {A : Type*} [Group A] (p : ℕ)
    [IsCyclic (A ⧸ pCore p A)] (K : Subgroup A) :
    IsCyclic (K ⧸ pCore p K) := by
  apply subgroup_quotient_of_inter_le_isCyclic (pCore p A) K (pCore p K)
  apply normal_pSubgroup_le_pCore
  exact (pCore_isPGroup p A).comap_subtype

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
