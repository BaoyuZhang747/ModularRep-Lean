import ModularRep.PaperProofs.TypeBSpinPrincipalProjectiveBinding
import Mathlib.GroupTheory.Coset.Card

/-!
# Splitting and finite carriers for the higher-rank GGGR window

The lower group is the literal norm kernel in the same special Clifford
group. Finiteness and enough roots for the lower group are derived from
the stated upper realization, rather than added as independent inputs.
This supporting file proves no GGGR selection or matrix conclusion.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankGGGRCarriers

open TypeBCliffordCarriers

variable {n : ℕ} {F K : Type} [Field F] [Finite F] [Field K]
  (N : NormSource n F)

/-- The actual norm-kernel Spin group is finite once its specified
Clifford-algebra realization is finite. -/
theorem spin_finite (finiteClifford : FiniteCliffordSource n F) :
    Finite (Spin n F N) := by
  letI : Finite (SpecialClifford n F) := specialClifford_finite n F finiteClifford
  infer_instance

/-- Restrict the upper splitting scope along the literal subgroup inclusion.
No separate root-of-unity scope for an unrelated lower group is supplied. -/
def spin_roots_of_upper [Finite (SpecialClifford n F)]
    [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] :
    HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) := by
  letI : NeZero (Nat.card (SpecialClifford n F)) := ⟨Nat.card_pos.ne'⟩
  exact HasEnoughRootsOfUnity.of_dvd K
    (Subgroup.card_subgroup_dvd_card (SpinSubgroup n F N))

end ModularRep.PaperProofs.TypeBAllRankGGGRCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
