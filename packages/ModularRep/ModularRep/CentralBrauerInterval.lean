import ModularRep.GroupAlgebraCentralBrauerMapTo

/-!
# Central Brauer interval data

This file packages the full subgroup interval used by Navarro's Theorem
(4.14).  It is a kernel-only datum: establishing the interval for a concrete
group remains a separate task.
-/

namespace ModularRep

/-- A `p`-subgroup and a subgroup in the full interval
`P C_G(P) ≤ H ≤ N_G(P)`.  The join records containment of both factors. -/
structure CentralBrauerInterval
    {p : Nat} {G : Type*} [Group G]
    (P H : Subgroup G) : Prop where
  isPGroup : IsPGroup p P
  pCentralizer_le : P ⊔ centralizerOf P ≤ H
  le_normalizer : H ≤ Subgroup.normalizer (P : Set G)

namespace CentralBrauerInterval

variable {p : Nat} {G : Type*} [Group G]
variable {P H : Subgroup G}

/-- The `p`-subgroup is contained in the intermediate subgroup. -/
theorem p_le (I : CentralBrauerInterval (p := p) P H) : P ≤ H :=
  le_sup_left.trans I.pCentralizer_le

/-- The ambient centralizer is contained in the intermediate subgroup. -/
theorem centralizer_le (I : CentralBrauerInterval (p := p) P H) :
    centralizerOf P ≤ H :=
  le_sup_right.trans I.pCentralizer_le

end CentralBrauerInterval

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
