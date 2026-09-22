import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The inclusion step from strict quasi-isolation to quasi-isolation

This module isolates only the elementary group-theoretic implication used in
Proposition 3.9 of the manuscript.  It follows the two noncontainment notions
in Feng--Li--Zhang 2022, Section 4.3, p. 21, but does not formalise algebraic
groups, algebraic centralisers, Levi subgroups, or either complete notion of
quasi-isolation.

In the application, the setwise product of `finiteCentralizer` and
`connectedCentralizer` represents
`C_{K^{*F'}}(s) C⁰_{K*}(s)`, the ambient group centraliser represents
`C_{K*}(s)`, and `IsProperLevi` selects the proper Levi subgroups of `K*`.
The algebraic-group identifications of these abstract subgroups remain
explicit inputs.
-/

namespace ModularRep.ManuscriptVerification.StrictQuasiIsolation

variable {Carrier : Type*}

/-- A subset is contained in none of the sets selected by `IsProperLevi`.

The abstract predicate deliberately imposes no algebraic structure on the
ambient type or on the selected sets. -/
def NotContainedInProperLevi
    (X : Set Carrier) (IsProperLevi : Set Carrier → Prop) : Prop :=
  ∀ L, IsProperLevi L → ¬ X ⊆ L

/-- Noncontainment in every proper Levi is inherited by a larger subset. -/
theorem notContainedInProperLevi_mono
    {smaller larger : Set Carrier} {IsProperLevi : Set Carrier → Prop}
    (hsub : smaller ⊆ larger)
    (hsmall : NotContainedInProperLevi smaller IsProperLevi) :
    NotContainedInProperLevi larger IsProperLevi := by
  intro L hL hlarger
  exact hsmall L hL (hsub.trans hlarger)

open scoped Pointwise

variable {G : Type*} [Group G]

/-- If two subgroups lie in the centraliser of `s`, then their setwise
product also lies in that centraliser. -/
theorem centralizerProduct_subset
    {s : G} {finiteCentralizer connectedCentralizer : Subgroup G}
    (hfinite : finiteCentralizer ≤ Subgroup.centralizer {s})
    (hconnected : connectedCentralizer ≤ Subgroup.centralizer {s}) :
    (finiteCentralizer : Set G) * (connectedCentralizer : Set G) ⊆
      (Subgroup.centralizer {s} : Set G) :=
  Subgroup.mul_subset hfinite hconnected

/-- If the finite and connected centraliser factors lie in the full group
centraliser, then the noncontainment condition defining strict
quasi-isolation implies the corresponding condition for quasi-isolation.

Only subgroup multiplication, inclusion, and the noncontainment quantifiers
are checked here.  Identifying these subgroups and proper Levi subsets with
the algebraic-group objects remains an explicit semantic input. -/
theorem quasiIsolated_of_strictlyQuasiIsolated
    {s : G} {finiteCentralizer connectedCentralizer : Subgroup G}
    {IsProperLevi : Set G → Prop}
    (hfinite : finiteCentralizer ≤ Subgroup.centralizer {s})
    (hconnected : connectedCentralizer ≤ Subgroup.centralizer {s})
    (hstrict : NotContainedInProperLevi
      ((finiteCentralizer : Set G) * (connectedCentralizer : Set G))
      IsProperLevi) :
    NotContainedInProperLevi (Subgroup.centralizer {s} : Set G)
      IsProperLevi :=
  notContainedInProperLevi_mono
    (centralizerProduct_subset hfinite hconnected) hstrict

end ModularRep.ManuscriptVerification.StrictQuasiIsolation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
