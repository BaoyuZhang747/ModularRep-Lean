import Formalisation.PCore
import Mathlib.Tactic

/-!
# The group theoretic conclusion of the exact stabiliser lemma

This file formalises the final group theoretic step in the manuscript's exact
stabiliser argument.  It does not formalise the character label calculation
that produces the normal subgroup `D` or proves the hypotheses on `D`.

If a finite group `J` has a normal `2`-subgroup `D` with cyclic quotient, then
`J / O₂(J)` is cyclic.  The same conclusion holds for every subgroup of
`J`.  Here `O₂` is represented by `pCore 2`.
-/

namespace Formalisation

/-- A normal `2`-subgroup with cyclic quotient may be enlarged to the
`2`-core without destroying cyclicity of the quotient. -/
theorem quotient_twoCore_isCyclic_of_normal_twoSubgroup
    {J : Type*} [Group J] [Finite J]
    (D : Subgroup J) [D.Normal] (hD : IsPGroup 2 D)
    [IsCyclic (J ⧸ D)] :
    IsCyclic (J ⧸ pCore 2 J) := by
  apply cyclic_quotient_of_normal_supergroup D (pCore 2 J)
  exact normal_pSubgroup_le_pCore 2 D hD

/-- If `D` is a normal `2`-subgroup of `J` and `J / D` is cyclic, then every
subgroup `K` of `J` has cyclic quotient by its `2`-core.  This is the abstract
group theoretic conclusion used in `lem:exact-stabilizer`. -/
theorem exactStabilizer_subgroup_quotient_twoCore_isCyclic
    {J : Type*} [Group J] [Finite J]
    (D : Subgroup J) [D.Normal] (hD : IsPGroup 2 D)
    [IsCyclic (J ⧸ D)] (K : Subgroup J) :
    IsCyclic (K ⧸ pCore 2 K) := by
  apply subgroup_quotient_of_inter_le_isCyclic D K (pCore 2 K)
  exact normal_pSubgroup_le_pCore 2 (D.comap K.subtype) hD.comap_subtype

/-- In a finite group, a normal subgroup of order at most two is a
`2`-subgroup.  Hence the conclusion of the preceding theorem follows from the
cardinality bound used in the manuscript. -/
theorem exactStabilizer_subgroup_quotient_twoCore_isCyclic_of_card_le_two
    {J : Type*} [Group J] [Finite J]
    (D : Subgroup J) [D.Normal] (hcard : Nat.card D ≤ 2)
    [IsCyclic (J ⧸ D)] (K : Subgroup J) :
    IsCyclic (K ⧸ pCore 2 K) := by
  have hcard_pos : 0 < Nat.card D := Nat.card_pos
  have hcard_cases : Nat.card D = 1 ∨ Nat.card D = 2 := by
    omega
  have hD : IsPGroup 2 D := by
    rcases hcard_cases with hcard_one | hcard_two
    · exact IsPGroup.of_card (n := 0) (by simpa using hcard_one)
    · exact IsPGroup.of_card (n := 1) (by simpa using hcard_two)
  exact exactStabilizer_subgroup_quotient_twoCore_isCyclic D hD K

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
