import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic
import ModularRep.OddQuasiIsolation
import ModularRep.StabilizerFactorizationTransport

/-!
# Shared Type B central-cover and orbit-stabiliser deductions

This module contains the generic deductions used in both the rank-three and
higher-rank arguments at the prime `2`: the odd-order lift and centraliser
calculations for a central double cover, the Bonnafé order-four deduction,
and the promotion of a constituent-orbit factorisation to the full field
group.  It contains no rank induction or proposition-level conclusion.
-/

namespace ModularRep.PaperProofs.TypeBTwoCommon

open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

section CentralDoubleCover

variable {Ghat G : Type*} [Group Ghat] [Group G]

/-- The exact finite group data used from the simply connected symplectic
double cover of the adjoint dual group.  The concrete algebraic-group model
and the fact that its kernel has order two are external structural inputs. -/
structure CentralDoubleCover where
  projection : Ghat →* G
  surjective : Function.Surjective projection
  kernelElement : Ghat
  kernelElement_ne_one : kernelElement ≠ 1
  kernelElement_sq : kernelElement ^ 2 = 1
  kernelElement_central : kernelElement ∈ Subgroup.center Ghat
  projection_eq_one_iff : ∀ x : Ghat,
    projection x = 1 ↔ x = 1 ∨ x = kernelElement

namespace CentralDoubleCover

variable (C : CentralDoubleCover (Ghat := Ghat) (G := G))

theorem kernelElement_mem_kernel : C.projection C.kernelElement = 1 :=
  (C.projection_eq_one_iff C.kernelElement).2 (Or.inr rfl)

theorem orderOf_kernelElement : orderOf C.kernelElement = 2 := by
  have hdiv : orderOf C.kernelElement ∣ 2 :=
    orderOf_dvd_of_pow_eq_one C.kernelElement_sq
  have hneZero : orderOf C.kernelElement ≠ 0 := by
    intro hzero
    rw [hzero] at hdiv
    norm_num at hdiv
  have hpos : 0 < orderOf C.kernelElement := Nat.pos_of_ne_zero hneZero
  have hne : orderOf C.kernelElement ≠ 1 := by
    intro h
    apply C.kernelElement_ne_one
    exact orderOf_eq_one_iff.mp h
  have hle : orderOf C.kernelElement ≤ 2 :=
    Nat.le_of_dvd (by decide) hdiv
  omega

theorem kernelElement_commutes (x : Ghat) :
    Commute C.kernelElement x := by
  rw [commute_iff_eq]
  exact (Subgroup.mem_center_iff.mp C.kernelElement_central x).symm

/-- Multiplication by the nontrivial kernel element changes an odd-order
lift into an element of twice that order. -/
theorem orderOf_kernelElement_mul_of_odd
    {x : Ghat} (hx : Odd (orderOf x)) :
    orderOf (C.kernelElement * x) = 2 * orderOf x := by
  calc
    orderOf (C.kernelElement * x) =
        orderOf C.kernelElement * orderOf x :=
      (C.kernelElement_commutes x).orderOf_mul_eq_mul_orderOf_of_coprime
        (by
          rw [C.orderOf_kernelElement]
          exact hx.coprime_two_left)
    _ = 2 * orderOf x := by rw [C.orderOf_kernelElement]

/-- An element of odd order in the quotient has exactly one lift of odd
order.  Neither existence nor uniqueness of that lift is assumed. -/
theorem existsUnique_odd_order_lift
    {s : G} (hs : Odd (orderOf s)) :
    ∃! shat : Ghat, C.projection shat = s ∧ Odd (orderOf shat) := by
  obtain ⟨x, hx⟩ := C.surjective s
  let m := orderOf s
  have hm : Odd m := hs
  have hxpow_kernel : C.projection (x ^ m) = 1 := by
    rw [map_pow, hx, pow_orderOf_eq_one]
  rcases (C.projection_eq_one_iff (x ^ m)).1 hxpow_kernel with hxpow | hxpow
  · have horder_dvd : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxpow
    have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hm horder_dvd
    refine ⟨x, ⟨hx, hxodd⟩, ?_⟩
    intro y hy
    have hxy_kernel : C.projection (y * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hy.1, hx, mul_inv_cancel]
    rcases (C.projection_eq_one_iff (y * x⁻¹)).1 hxy_kernel with hxy | hxy
    · simpa only [mul_inv_eq_one] using hxy
    · have hyx : y = C.kernelElement * x := by
        calc
          y = (y * x⁻¹) * x := by group
          _ = C.kernelElement * x := by rw [hxy]
      have horder := C.orderOf_kernelElement_mul_of_odd hxodd
      rw [← hyx] at horder
      have hnotEven : ¬ Even (orderOf y) := Nat.not_even_iff_odd.mpr hy.2
      apply False.elim
      apply hnotEven
      refine ⟨orderOf x, ?_⟩
      omega
  · let y := C.kernelElement * x
    have hyprojection : C.projection y = s := by
      simp only [y, map_mul, C.kernelElement_mem_kernel, one_mul, hx]
    have hzpow : C.kernelElement ^ m = C.kernelElement := by
      obtain ⟨k, hk⟩ := hm
      calc
        C.kernelElement ^ m =
            C.kernelElement ^ (2 * k + 1) := by rw [hk]
        _ = (C.kernelElement ^ 2) ^ k * C.kernelElement := by
          rw [pow_add, pow_mul, pow_one]
        _ = C.kernelElement := by rw [C.kernelElement_sq, one_pow, one_mul]
    have hypow : y ^ m = 1 := by
      dsimp only [y]
      rw [(C.kernelElement_commutes x).mul_pow, hzpow, hxpow,
        show C.kernelElement * C.kernelElement = 1 by
          simpa only [pow_two] using C.kernelElement_sq]
    have hyorder_dvd : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hypow
    have hyodd : Odd (orderOf y) := Odd.of_dvd_nat hm hyorder_dvd
    refine ⟨y, ⟨hyprojection, hyodd⟩, ?_⟩
    intro y' hy'
    have hyy_kernel : C.projection (y' * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hy'.1, hyprojection, mul_inv_cancel]
    rcases (C.projection_eq_one_iff (y' * y⁻¹)).1 hyy_kernel with hyy | hyy
    · simpa only [mul_inv_eq_one] using hyy
    · have hy'eq : y' = C.kernelElement * y := by
        calc
          y' = (y' * y⁻¹) * y := by group
          _ = C.kernelElement * y := by rw [hyy]
      have horder := C.orderOf_kernelElement_mul_of_odd hyodd
      rw [← hy'eq] at horder
      have hnotEven : ¬ Even (orderOf y') := Nat.not_even_iff_odd.mpr hy'.2
      apply False.elim
      apply hnotEven
      refine ⟨orderOf y, ?_⟩
      omega

/-- If an element centralises the projection of an odd-order lift, it already
centralises the lift.  The other possible lift of the conjugate would be the
kernel-element multiple, whose order is twice as large. -/
theorem commute_of_projection_commute
    {x shat : Ghat} (hOdd : Odd (orderOf shat))
    (hcomm : Commute (C.projection x) (C.projection shat)) :
    Commute x shat := by
  let commutator := x * shat * x⁻¹ * shat⁻¹
  have hcommutator_kernel : C.projection commutator = 1 := by
    simp only [commutator, map_mul, map_inv]
    rw [hcomm.eq]
    group
  rcases (C.projection_eq_one_iff commutator).1 hcommutator_kernel with hc | hc
  · rw [commute_iff_eq]
    dsimp only [commutator] at hc
    calc
      x * shat =
          (x * shat * x⁻¹ * shat⁻¹) * (shat * x) := by group
      _ = 1 * (shat * x) := by rw [hc]
      _ = shat * x := one_mul _
  · have hconj : x * shat * x⁻¹ = C.kernelElement * shat := by
      calc
        x * shat * x⁻¹ = commutator * shat := by
          simp only [commutator]
          group
        _ = C.kernelElement * shat := by rw [hc]
    have hsemiconj : SemiconjBy x shat (C.kernelElement * shat) := by
      change x * shat = (C.kernelElement * shat) * x
      calc
        x * shat = (x * shat * x⁻¹) * x := by group
        _ = (C.kernelElement * shat) * x := by rw [hconj]
    have horders : orderOf shat = orderOf (C.kernelElement * shat) :=
      hsemiconj.orderOf_eq x
    rw [C.orderOf_kernelElement_mul_of_odd hOdd] at horders
    obtain ⟨k, hk⟩ := hOdd
    omega

/-- The group-theoretic content of the centraliser comparison for an odd-order
element: for the odd-order lift, the inverse image of the centraliser downstairs
is exactly the centraliser upstairs.  Connectedness of the latter centraliser
is deliberately left to Steinberg's theorem as an external algebraic-group
input. -/
theorem projection_commute_iff_commute
    {s : G} {shat x : Ghat} (hProjection : C.projection shat = s)
    (hOdd : Odd (orderOf shat)) :
    Commute (C.projection x) s ↔ Commute x shat := by
  rw [← hProjection]
  constructor
  · exact C.commute_of_projection_commute hOdd
  · intro h
    exact h.map C.projection

/-- Source-shaped form of Bonnafé's order bound for lifts of quasi-isolated
parameters through the central double cover. -/
def BonnafeOrderFourProjectionInterface
    (IsQuasiIsolated : G → Prop) : Prop :=
  ∀ {s : G} {shat : Ghat}, IsQuasiIsolated s →
    C.projection shat = s → orderOf shat ∣ 4

/-- The central-double-cover odd-label deduction for a nonprincipal block.
Lean chooses the unique odd-order lift,
applies the external order-four bound to that lift, and derives the
contradiction with nonprincipality through the external identity-label
theorem.  Neither the lift nor the conclusion is assumed. -/
theorem nonprincipal_label_not_quasiIsolated
    {Block : Type*}
    {IsQuasiIsolated : G → Prop} {IsAssociated : Block → G → Prop}
    {IsPrincipalBlock : Block → Prop}
    (bonnafe : C.BonnafeOrderFourProjectionInterface IsQuasiIsolated)
    (identityPrincipal :
      ModularRep.TypeBQuasiIsolation.IdentityLabelPrincipalBlockInterface
        IsAssociated IsPrincipalBlock)
    {b : Block} {s : G} (hAssociated : IsAssociated b s)
    (hOdd : Odd (orderOf s)) (hNonprincipal : ¬ IsPrincipalBlock b) :
    ¬ IsQuasiIsolated s := by
  intro hQuasi
  obtain ⟨shat, hProjection, hShatOdd⟩ :=
    (C.existsUnique_odd_order_lift hOdd).exists
  have hShat : shat = 1 :=
    ModularRep.TypeBQuasiIsolation.eq_one_of_odd_order_of_orderOf_dvd_four
      hShatOdd (bonnafe hQuasi hProjection)
  have hs : s = 1 := by rw [← hProjection, hShat, map_one]
  apply hNonprincipal
  apply identityPrincipal
  simpa only [hs] using hAssociated

end CentralDoubleCover

end CentralDoubleCover

section OrbitStabilizer

variable {A E Theta Psi : Type*}
variable [Group A] [Group E]
variable [MulAction A Theta] [MulAction E Theta]
variable [MulAction A Psi] [MulAction E Psi]

/-- Elementwise form of setwise stability of the `A`-orbit of `theta`. -/
def OrbitSetwiseStable (theta : Theta) (e : E) : Prop :=
  ∀ x : Theta,
    x ∈ MulAction.orbit A theta ↔ e • x ∈ MulAction.orbit A theta

/-- Compatibility of the two actions implies that carrying `theta` back
into its `A`-orbit stabilises the entire orbit setwise. -/
theorem orbitSetwiseStable_of_smul_mem_orbit
    (phi : E →* MulAut A)
    (compat : Formalisation.SemidirectActionCompatible
      (X := Theta) phi)
    (theta : Theta) (e : E)
    (he : e • theta ∈ MulAction.orbit A theta) :
    OrbitSetwiseStable (A := A) theta e := by
  rw [MulAction.mem_orbit_iff] at he
  obtain ⟨b, hb⟩ := he
  have hforward : ∀ y : Theta,
      y ∈ MulAction.orbit A theta →
        e • y ∈ MulAction.orbit A theta := by
    intro y hy
    rw [MulAction.mem_orbit_iff] at hy ⊢
    obtain ⟨a, rfl⟩ := hy
    refine ⟨(phi e) a * b, ?_⟩
    calc
      ((phi e) a * b) • theta =
          (phi e) a • (b • theta) := mul_smul _ _ _
      _ = (phi e) a • (e • theta) := by rw [hb]
      _ = e • (a • theta) := (compat e a theta).symm
  have heinv : e⁻¹ • theta ∈ MulAction.orbit A theta := by
    rw [MulAction.mem_orbit_iff]
    refine ⟨((phi e⁻¹) b)⁻¹, ?_⟩
    have hreturn : (phi e⁻¹) b • (e⁻¹ • theta) = theta := by
      calc
        (phi e⁻¹) b • (e⁻¹ • theta) = e⁻¹ • (b • theta) := by
          rw [compat]
        _ = e⁻¹ • (e • theta) := by rw [hb]
        _ = theta := inv_smul_smul e theta
    calc
      ((phi e⁻¹) b)⁻¹ • theta =
          ((phi e⁻¹) b)⁻¹ • ((phi e⁻¹) b • (e⁻¹ • theta)) := by
            rw [hreturn]
      _ = e⁻¹ • theta := inv_smul_smul _ _
  intro y
  constructor
  · exact hforward y
  · intro hey
    have hinv_forward : ∀ z : Theta,
        z ∈ MulAction.orbit A theta →
          e⁻¹ • z ∈ MulAction.orbit A theta := by
      intro z hz
      rw [MulAction.mem_orbit_iff] at hz ⊢
      obtain ⟨a, rfl⟩ := hz
      rw [MulAction.mem_orbit_iff] at heinv
      obtain ⟨c, hc⟩ := heinv
      refine ⟨(phi e⁻¹) a * c, ?_⟩
      calc
        ((phi e⁻¹) a * c) • theta =
            (phi e⁻¹) a • (c • theta) := mul_smul _ _ _
        _ = (phi e⁻¹) a • (e⁻¹ • theta) := by rw [hc]
        _ = e⁻¹ • (a • theta) := (compat e⁻¹ a theta).symm
    simpa only [inv_smul_smul] using hinv_forward (e • y) hey

/-- The equality `(D_O)_psi = D_psi` in Proposition 4.13, written without
introducing subgroup carriers.  Clifford return forces every field element
fixing `psi` to stabilise the constituent orbit, and the converse implication
is tautological. -/
theorem field_fix_iff_orbitSetwiseStable_and_field_fix
    (phi : E →* MulAut A)
    (compatTheta : Formalisation.SemidirectActionCompatible
      (X := Theta) phi)
    (theta : Theta) (psi : Psi) (e : E)
    (constituentReturn : ∀ a : A, ∀ e : E,
      a • (e • psi) = psi →
        e • theta ∈ MulAction.orbit A theta) :
    e • psi = psi ↔
      OrbitSetwiseStable (A := A) theta e ∧ e • psi = psi := by
  constructor
  · intro he
    refine ⟨orbitSetwiseStable_of_smul_mem_orbit phi compatTheta theta e ?_, he⟩
    exact constituentReturn 1 e (by simpa only [one_smul] using he)
  · exact And.right

/-- The deduction at the end of the Levi-orbit construction in Proposition
4.13.  A factorisation known over the setwise orbit stabiliser extends to the
full field group because Clifford theory forces every combined stabiliser
element into that orbit stabiliser. -/
theorem productStabilizerFactorization_of_orbit_stabilizer
    (phi : E →* MulAut A)
    (compatTheta : Formalisation.SemidirectActionCompatible
      (X := Theta) phi)
    (theta : Theta) (psi : Psi)
    (constituentReturn : ∀ a : A, ∀ e : E,
      a • (e • psi) = psi →
        e • theta ∈ MulAction.orbit A theta)
    (localFactorization : ∀ a : A, ∀ e : E,
      OrbitSetwiseStable (A := A) theta e →
        (a • (e • psi) = psi ↔ a • psi = psi ∧ e • psi = psi)) :
    ProductStabilizerFactorization (D := A) (E := E) psi := by
  intro a e
  constructor
  · intro hfix
    exact (localFactorization a e
      (orbitSetwiseStable_of_smul_mem_orbit phi compatTheta theta e
        (constituentReturn a e hfix))).1 hfix
  · rintro ⟨ha, he⟩
    rw [he, ha]

end OrbitStabilizer

end ModularRep.PaperProofs.TypeBTwoCommon


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
