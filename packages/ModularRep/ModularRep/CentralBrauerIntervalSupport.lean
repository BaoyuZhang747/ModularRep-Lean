import ModularRep.GroupAlgebraCentralBrauerMapTo

/-!
# Support transport for interval-valued central Brauer maps

The group algebra inclusion induced by a literal subgroup inclusion is
injective.  Consequently the centralizer-target central Brauer map and its
interval-valued version vanish, or are nonzero, simultaneously.
-/

namespace ModularRep

open MonoidAlgebra

noncomputable section

variable {k G : Type*} [CommSemiring k] [Group G]

/-- The group algebra inclusion from the centralizer into an intermediate
subgroup is injective. -/
theorem centralizerAlgebraMapTo_injective
    (P H : Subgroup G) (hCH : centralizerOf P ≤ H) :
    Function.Injective (centralizerAlgebraMapTo (k := k) P H hCH) := by
  change Function.Injective
    (MonoidAlgebra.mapDomain (R := k) (Subgroup.inclusion hCH))
  exact MonoidAlgebra.mapDomain_injective
    (Subgroup.inclusion_injective hCH)

variable {p : Nat}
variable [Finite G] [Fact p.Prime] [CharP k p]

/-- The centralizer-target map vanishes exactly when the interval-valued map
vanishes. -/
theorem centralBrauerMap_eq_zero_iff_mapTo_eq_zero
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (z : GroupAlgebraCenter k G) :
    centralBrauerMap (k := k) (p := p) P hP z = 0 ↔
      centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN z = 0 := by
  constructor
  · intro hzero
    apply Subtype.ext
    change
      ((centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN z :
          GroupAlgebraCenter k H) : k[H]) = 0
    rw [centralBrauerMapTo_apply, hzero, Subalgebra.coe_zero, map_zero]
  · intro hzero
    apply Subtype.ext
    apply centralizerAlgebraMapTo_injective (k := k) P H hCH
    calc
      centralizerAlgebraMapTo (k := k) P H hCH
          (centralBrauerMap (k := k) (p := p) P hP z) =
          ((centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN z :
              GroupAlgebraCenter k H) : k[H]) :=
        (centralBrauerMapTo_apply
          (k := k) (p := p) P H hP hCH hHN z).symm
      _ = 0 := congrArg
        (fun w : GroupAlgebraCenter k H ↦ (w : k[H])) hzero
      _ = centralizerAlgebraMapTo (k := k) P H hCH
          (0 : k[centralizerOf P]) :=
        (map_zero (centralizerAlgebraMapTo (k := k) P H hCH)).symm

/-- Equivalently, the centralizer-target map is nonzero exactly when the
interval-valued map is nonzero. -/
theorem centralBrauerMap_ne_zero_iff_mapTo_ne_zero
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (z : GroupAlgebraCenter k G) :
    centralBrauerMap (k := k) (p := p) P hP z ≠ 0 ↔
      centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN z ≠ 0 := by
  exact not_congr
    (centralBrauerMap_eq_zero_iff_mapTo_eq_zero
      (k := k) (p := p) P H hP hCH hHN z)

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
