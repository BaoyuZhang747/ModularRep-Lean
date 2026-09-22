import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import ModularRep.PGroupInvariantSum
import ModularRep.GroupAlgebraCentralFunctions

/-!
# The centralizer-target central Brauer map

Coefficient restriction from `k[G]` to `k[C_G(P)]` is not multiplicative on
arbitrary group algebra elements.  On the centre it is multiplicative when
`P` is a `p`-group and `k` has characteristic `p`; the proof is the standard
weighted orbit cancellation in the convolution coefficient.
-/

namespace ModularRep

open MonoidAlgebra
open scoped BigOperators

noncomputable section

variable {p : Nat} {k G : Type*}
variable [CommSemiring k] [Group G]

/-- The centralizer of a subgroup, as the target group for the central Brauer
map. -/
abbrev centralizerOf (P : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (P : Set G)

/-- Raw coefficient restriction to `C_G(P)`; no `p`-group claim is used. -/
def centralBrauerRestriction (P : Subgroup G) :
    GroupAlgebraCenter k G →ₗ[k] GroupAlgebraCenter k (centralizerOf P) :=
  centerCoeffRestrict (centralizerOf P)

@[simp]
theorem centralBrauerRestriction_one (P : Subgroup G) :
    centralBrauerRestriction (k := k) P 1 = 1 := by
  simp [centralBrauerRestriction]

@[simp]
theorem centralBrauerRestriction_coeff
    (P : Subgroup G) (z : GroupAlgebraCenter k G) (c : centralizerOf P) :
    ((centralBrauerRestriction (k := k) P z :
        GroupAlgebraCenter k (centralizerOf P)) :
          k[centralizerOf P]).coeff c =
      (z : k[G]).coeff (c : G) :=
  rfl

variable [Finite G] [Fact p.Prime] [CharP k p]

/-- In characteristic `p`, restriction to `C_G(P)` is multiplicative on
central elements when `P` is a `p`-group. -/
theorem centralBrauerRestriction_mul
    (P : Subgroup G) (hP : IsPGroup p P)
    (z w : GroupAlgebraCenter k G) :
    centralBrauerRestriction (k := k) P (z * w) =
      centralBrauerRestriction (k := k) P z *
        centralBrauerRestriction (k := k) P w := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : MulAction P G :=
    MulAction.compHom G
      (ConjAct.toConjAct.toMonoidHom.comp P.subtype)
  let _ : Fintype (MulAction.fixedPoints P G) := Fintype.ofFinite _
  classical
  apply Subtype.ext
  ext c
  let f : G → k := fun a ↦
    (z : k[G]).coeff a * (w : k[G]).coeff (a⁻¹ * (c : G))
  have hf : ∀ q : P, ∀ a : G, f (q • a) = f a := by
    intro q a
    have hqInvC : (q : G)⁻¹ * (c : G) = (c : G) * (q : G)⁻¹ :=
      Subgroup.mem_centralizer_iff.mp c.property
        ((q : G)⁻¹) (P.inv_mem q.property)
    have hargument :
        ((q : G) * a * (q : G)⁻¹)⁻¹ * (c : G) =
          (q : G) * (a⁻¹ * (c : G)) * (q : G)⁻¹ := by
      calc
        ((q : G) * a * (q : G)⁻¹)⁻¹ * (c : G) =
            (q : G) * (a⁻¹ * ((q : G)⁻¹ * (c : G))) := by
              simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = (q : G) * (a⁻¹ * (c : G)) * (q : G)⁻¹ := by
          rw [hqInvC]
          simp only [mul_assoc]
    change
      (z : k[G]).coeff ((q : G) * a * (q : G)⁻¹) *
          (w : k[G]).coeff (((q : G) * a * (q : G)⁻¹)⁻¹ * (c : G)) =
        (z : k[G]).coeff a * (w : k[G]).coeff (a⁻¹ * (c : G))
    rw [GroupAlgebraCenter.coeff_conjugate z (q : G) a, hargument,
      GroupAlgebraCenter.coeff_conjugate w (q : G) (a⁻¹ * (c : G))]
  have hfixed :
      MulAction.fixedPoints P G = (centralizerOf P : Set G) := by
    ext x
    change
      (∀ q : P, (q : G) * x * (q : G)⁻¹ = x) ↔
        ∀ g : G, g ∈ (P : Set G) → g * x = x * g
    constructor
    · intro hx g hg
      exact mul_inv_eq_iff_eq_mul.mp (hx ⟨g, hg⟩)
    · intro hx q
      exact mul_inv_eq_iff_eq_mul.mpr (hx q q.property)
  have hsum : (
      ∑ a : G, f a) = ∑ a : centralizerOf P, f (a : G) := by
    calc
      (∑ a : G, f a) =
          ∑ a : MulAction.fixedPoints P G, f (a : G) :=
        IsPGroup.sum_eq_sum_fixedPoints_of_invariant hP f hf
      _ = ∑ a : centralizerOf P, f (a : G) := by
        exact Fintype.sum_equiv (Equiv.setCongr hfixed)
          (fun a : MulAction.fixedPoints P G ↦ f (a : G))
          (fun a : centralizerOf P ↦ f (a : G))
          (fun _ ↦ rfl)
  change
    (((z : k[G]) * (w : k[G])).coeff (c : G)) =
      ((coeffRestrict (centralizerOf P) (z : k[G]) *
        coeffRestrict (centralizerOf P) (w : k[G])).coeff c)
  calc
    (((z : k[G]) * (w : k[G])).coeff (c : G)) =
        ∑ a : G, f a := by
      rw [MonoidAlgebra.coeff_mul_apply_left,
        Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
    _ = ∑ a : centralizerOf P, f (a : G) := hsum
    _ =
        ((coeffRestrict (centralizerOf P) (z : k[G]) *
          coeffRestrict (centralizerOf P) (w : k[G])).coeff c) := by
      rw [MonoidAlgebra.coeff_mul_apply_left,
        Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
      rfl

/-- The central Brauer map from `Z(k[G])` to `Z(k[C_G(P)])`. -/
noncomputable def centralBrauerMap
    (P : Subgroup G) (hP : IsPGroup p P) :
    GroupAlgebraCenter k G →ₐ[k] GroupAlgebraCenter k (centralizerOf P) :=
  AlgHom.ofLinearMap (centralBrauerRestriction (k := k) P)
    (centralBrauerRestriction_one (k := k) P)
    (centralBrauerRestriction_mul (k := k) (p := p) P hP)

@[simp]
theorem centralBrauerMap_apply
    (P : Subgroup G) (hP : IsPGroup p P)
    (z : GroupAlgebraCenter k G) :
    centralBrauerMap (k := k) (p := p) P hP z =
      centralBrauerRestriction (k := k) P z :=
  rfl

theorem centralBrauerMap_toLinearMap
    (P : Subgroup G) (hP : IsPGroup p P) :
    (centralBrauerMap (k := k) (p := p) P hP).toLinearMap =
      centralBrauerRestriction (k := k) P :=
  rfl

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
