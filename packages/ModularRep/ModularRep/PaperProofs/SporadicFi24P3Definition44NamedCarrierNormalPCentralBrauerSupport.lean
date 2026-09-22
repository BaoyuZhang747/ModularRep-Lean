import ModularRep.GroupAlgebraCentralBrauerMap
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPSubgroupKernel

/-! Normal p-subgroups have nonzero Brauer restriction on every nonzero
central idempotent. The proof uses a fixed vector in the idempotent's image
and cancellation of nontrivial conjugation orbits in characteristic p. -/

noncomputable section
open scoped MonoidAlgebra BigOperators
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPCentralBrauerSupport

open ModularRep
open SporadicFi24P3Definition44NamedCarrierNormalPSubgroupKernel

variable {p : ℕ} {k G : Type*}
variable [Field k] [CharP k p] [Fact p.Prime] [Group G] [Finite G]

theorem central_mul_eq_zero_of_normal_p_fixed
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (z : GroupAlgebraCenter k G) (v : k[G])
    (hv : ∀ q : P, MonoidAlgebra.single (q : G) (1 : k) * v = v)
    (hz : centralBrauerRestriction P z = 0) :
    (z : k[G]) * v = 0 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : MulAction P G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp P.subtype)
  let _ : Fintype (MulAction.fixedPoints P G) := Fintype.ofFinite _
  have hvCoeff : ∀ q : P, ∀ x : G,
      v.coeff ((q : G) * x) = v.coeff x := by
    intro q x
    have hc := congrArg (fun w : k[G] => w.coeff ((q : G) * x)) (hv q)
    simpa only [MonoidAlgebra.coeff_single_mul_apply, one_mul,
      inv_mul_cancel_left] using hc.symm
  have hfixed : MulAction.fixedPoints P G = (centralizerOf P : Set G) := by
    ext x
    change (∀ q : P, (q : G) * x * (q : G)⁻¹ = x) ↔
      ∀ g : G, g ∈ (P : Set G) → g * x = x * g
    constructor
    · intro hx g hg
      exact mul_inv_eq_iff_eq_mul.mp (hx ⟨g, hg⟩)
    · intro hx q
      exact mul_inv_eq_iff_eq_mul.mpr (hx q q.property)
  ext x
  let f : G → k := fun a => (z : k[G]).coeff a * v.coeff (a⁻¹ * x)
  have hf : ∀ q : P, ∀ a : G, f (q • a) = f a := by
    intro q a
    have ht : a⁻¹ * (q : G)⁻¹ * a ∈ P := by
      simpa only [inv_inv] using
        (inferInstance : P.Normal).conj_mem (q : G)⁻¹ (P.inv_mem q.property) a⁻¹
    have harg : ((q : G) * a * (q : G)⁻¹)⁻¹ * x =
        (q : G) * ((a⁻¹ * (q : G)⁻¹ * a) * (a⁻¹ * x)) := by group
    change (z : k[G]).coeff ((q : G) * a * (q : G)⁻¹) *
      v.coeff (((q : G) * a * (q : G)⁻¹)⁻¹ * x) =
        (z : k[G]).coeff a * v.coeff (a⁻¹ * x)
    rw [GroupAlgebraCenter.coeff_conjugate z (q : G) a, harg,
      hvCoeff q, hvCoeff ⟨_, ht⟩]
  have hsum : (∑ a : G, f a) = ∑ a : centralizerOf P, f (a : G) := by
    calc
      (∑ a : G, f a) = ∑ a : MulAction.fixedPoints P G, f (a : G) :=
        IsPGroup.sum_eq_sum_fixedPoints_of_invariant hP f hf
      _ = ∑ a : centralizerOf P, f (a : G) :=
        Fintype.sum_equiv (Equiv.setCongr hfixed)
          (fun a : MulAction.fixedPoints P G => f (a : G))
          (fun a : centralizerOf P => f (a : G)) (fun _ => rfl)
  calc
    (((z : k[G]) * v).coeff x) = ∑ a : G, f a := by
      rw [MonoidAlgebra.coeff_mul_apply_left,
        Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    _ = ∑ a : centralizerOf P, f (a : G) := hsum
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have ha : (z : k[G]).coeff (a : G) = 0 := by
        change ((centralBrauerRestriction P z :
          GroupAlgebraCenter k (centralizerOf P)) : k[centralizerOf P]).coeff a = 0
        rw [hz]
        rfl
      change (z : k[G]).coeff (a : G) * v.coeff ((a : G)⁻¹ * x) = 0
      rw [ha, zero_mul]

theorem exists_nonzero_fixed_in_central_idempotent
    (P : Subgroup G) (hP : IsPGroup p P)
    (e : k[G]) (he : IsIdempotentElem e) (hc : IsMulCentral e) (hne : e ≠ 0) :
    ∃ v : k[G], v ≠ 0 ∧ e * v = v ∧
      ∀ q : P, MonoidAlgebra.single (q : G) (1 : k) * v = v := by
  let W : Submodule k k[G] := {
    carrier := {v | e * v = v}
    zero_mem' := mul_zero e
    add_mem' := by
      intro v w hv hw
      change e * (v + w) = v + w
      rw [mul_add, hv, hw]
    smul_mem' := by
      intro a v hv
      change e * (a • v) = a • v
      rw [mul_smul_comm, hv] }
  let : Nontrivial W :=
    ⟨⟨⟨e, he.eq⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  let L := Representation.leftRegular k G
  have hL (g : G) (v : k[G]) :
      L g v = MonoidAlgebra.single g (1 : k) * v := by
    rw [← L.asAlgebraHom_single_one g]
    exact Representation.asAlgebraHom_ofMulAction_smul_eq_mul _ _
  have hstable : ∀ g : G, W ≤ W.comap (L g) := by
    intro g v hv
    change e * (L g v) = L g v
    rw [hL, hc.left_comm, hv]
  let rho : Representation k G W := L.subrepresentation W hstable
  have hf : Representation.invariants (rho.comp P.subtype) ≠ ⊥ :=
    invariants_ne_bot_of_isPGroup (Fact.out : p.Prime) hP (rho.comp P.subtype)
  obtain ⟨v, hv, hnv⟩ := (Submodule.ne_bot_iff _).mp hf
  refine ⟨v.1, ?_, v.2, ?_⟩
  · intro h
    exact hnv (Subtype.ext h)
  · intro q
    have hfix := congrArg Subtype.val (hv q)
    change L (q : G) v.1 = v.1 at hfix
    rwa [hL] at hfix

theorem normal_p_central_idempotent_restriction_ne_zero
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (z : GroupAlgebraCenter k G)
    (he : IsIdempotentElem (z : k[G])) (hne : (z : k[G]) ≠ 0) :
    centralBrauerRestriction P z ≠ 0 := by
  have hc : IsMulCentral (z : k[G]) :=
    Set.mem_center_iff.mp
      (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp z.property))
  obtain ⟨v, hv, hev, hfixed⟩ :=
    exists_nonzero_fixed_in_central_idempotent P hP (z : k[G]) he hc hne
  intro hz
  exact hv (hev.symm.trans (central_mul_eq_zero_of_normal_p_fixed P hP z v hfixed hz))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPCentralBrauerSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
