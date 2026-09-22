import Mathlib.GroupTheory.Sylow

/-!
# The Sylow obstruction used in the principal `2`-block argument

The new reflection argument in Proposition 3.3 constructs a `2`-subgroup of
the relevant centraliser which properly contains the centre of a proposed
radical subgroup.  This file verifies the final group-theoretic contradiction:
a Sylow subgroup cannot have a proper `p`-subgroup overgroup.

Constructing the reflection, proving that it centralises the full wreath
product, and proving that it is outside the proposed subgroup are geometric
inputs and remain outside this lemma.
-/

namespace Formalisation.SylowObstruction

variable {p : ℕ} {G : Type*} [Group G]

/-- A Sylow `p`-subgroup has no proper overgroup which is again a
`p`-group. -/
theorem no_proper_p_overgroup (P : Sylow p G) (Q : Subgroup G)
    (hQ : IsPGroup p Q) (hPQ : (P : Subgroup G) < Q) : False := by
  have hEq : Q = (P : Subgroup G) := P.is_maximal' hQ hPQ.le
  exact hPQ.ne hEq.symm

/-- Element form used after adjoining the reflection: if a `p`-subgroup
`Q` contains the Sylow subgroup `P` and contains an element outside `P`, the
hypotheses are inconsistent. -/
theorem false_of_element_in_p_overgroup
    (P : Sylow p G) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hPQ : (P : Subgroup G) ≤ Q) {t : G}
    (htQ : t ∈ Q) (htP : t ∉ (P : Subgroup G)) : False := by
  have hne : (P : Subgroup G) ≠ Q := by
    intro h
    apply htP
    rw [h]
    exact htQ
  exact no_proper_p_overgroup P Q hQ (lt_of_le_of_ne hPQ hne)

end Formalisation.SylowObstruction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
