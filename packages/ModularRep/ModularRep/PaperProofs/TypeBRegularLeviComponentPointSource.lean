import ModularRep.PaperProofs.TypeBRegularLeviProductProjection

/-!
# Original geometric component data for the regular Levi

This source interface contains only a presentation of the original geometric
point subgroup and its original Frobenius. Each component is an actual
subgroup of that same H. The inverse-single equation binds the component
inclusion to that literal subgroup inclusion. It is not an input about
rational factors, supported lifts, product action images, or character orbits.

E1/U: the subgroups must be the actual simple components of the chosen
connected simply connected derived algebraic Levi, in a finite presentation
of the Frobenius cycles (including singleton cycles). The point product and
its original Frobenius equations are the standard structural input.
Sources: Malle--Testerman Proposition 12.14, p. 103; Geck--Malle Lemma 1.5.15,
pp. 63--64 and Corollary 1.5.16, p. 64; the geometric opening of the proof of
FLZ, Jordan decomposition for weights, Proposition 5.6, p. 31.
Algebraic-group authenticity and arbitrary-index presentation remain explicit
source/application obligations. No formal algebraic predicate is invented.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviComponentPointSource

open TypeBComponentCycleNormalization TypeBRegularLeviSupportedLift

variable {B C : Type} [Group B] (F : B →* B)
variable (H : Subgroup B) (hH : ∀ h ∈ H, F h ∈ H) (m : C → ℕ)

local instance : DecidableEq (Index m) := Classical.decEq (Index m)

/-- A standard original point presentation on literal component subgroups.
Only the ORIGINAL geometric automorphism has a source square; its rational
restriction and all coordinate conjugation squares are deductions. -/
structure ComponentPointData where
  component : Index m → Subgroup H
  coordinates : H ≃* ((i : Index m) → component i)
  inclusion : ∀ (i : Index m) (x : component i),
    coordinates.symm (Function.update 1 i x) = (x : H)
  cycles : CycleCoordinates m (fun i ↦ ↥(component i))
  frobenius : MulAut ((i : Index m) → component i)
  monomial : MonomialAction m (fun i ↦ ↥(component i)) cycles frobenius
  frobenius_value : ∀ h : H,
    coordinates (derivedFrobenius F H hH h) = frobenius (coordinates h)

variable (data : ComponentPointData F H hH m)

/-- The exact original component point groups, as subgroups of the original H. -/
abbrev componentGroup (i : Index m) : Type := data.component i

/-- The rational factor is the actual fixed subgroup of the computed return,
whose equality with the original Frobenius power is already checked. -/
abbrev rationalFactor (c : C) : Type :=
  TypeBRegularLeviProductProjection.Factor m
    (componentGroup F H hH m data) data.cycles c

/-- On every original element, the factor return is the original full power
at the selected first component. This equation is derived, not sourced. -/
theorem rationalFactor_return_value (c : C)
    (g : Original m (componentGroup F H hH m data)) :
    fullReturn m (componentGroup F H hH m data) data.cycles c (g (first m c)) =
      (data.frobenius ^ (m c + 1)) g (first m c) :=
  TypeBRegularLeviComponentFixedPoints.factorReturn_power_value m
    (componentGroup F H hH m data) data.cycles data.frobenius data.monomial c g

end ModularRep.PaperProofs.TypeBRegularLeviComponentPointSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
