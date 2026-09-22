import ModularRep.GroupAlgebraCentralBrauerMap
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPSubgroupKernel
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A central element with zero Brauer restriction acts as zero whenever
the p-subgroup lies in the representation kernel. The argument is weighted
conjugacy-orbit cancellation, applied to the actual operator sum. -/

noncomputable section
open scoped MonoidAlgebra BigOperators
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPKernelCentralAction
open ModularRep
open SporadicFi24P3Definition44NamedCarrierNormalPSubgroupKernel
attribute [local instance] Fintype.ofFinite

theorem sum_eq_sum_fixedPoints_of_invariant_module
    {p : ℕ} {k P A V : Type*}
    [Field k] [CharP k p] [Fact p.Prime]
    [Group P] [Fintype A] [MulAction P A]
    [AddCommGroup V] [Module k V]
    (hP : IsPGroup p P) (f : A → V)
    (hf : ∀ q : P, ∀ a : A, f (q • a) = f a) :
    (∑ a : A, f a) = ∑ a : MulAction.fixedPoints P A, f (a : A) := by
  classical
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k _).mp
  intro ell
  rw [map_sub]
  apply sub_eq_zero.mpr
  simpa only [map_sum] using
    IsPGroup.sum_eq_sum_fixedPoints_of_invariant hP (fun a => ell (f a))
      (fun q a => congrArg ell (hf q a))

theorem central_action_eq_zero_of_p_kernel
    {p : ℕ} {k G V : Type*}
    [Field k] [CharP k p] [Fact p.Prime] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (P : Subgroup G) (hP : IsPGroup p P)
    (rho : Representation k G V) (hker : P ≤ rho.ker)
    (z : GroupAlgebraCenter k G)
    (hz : centralBrauerRestriction P z = 0) :
    rho.asAlgebraHom z.val = 0 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : MulAction P G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp P.subtype)
  let _ : Fintype (MulAction.fixedPoints P G) := Fintype.ofFinite _
  have hfixed : MulAction.fixedPoints P G = (centralizerOf P : Set G) := by
    ext x
    change (∀ q : P, (q : G) * x * (q : G)⁻¹ = x) ↔
      ∀ g : G, g ∈ (P : Set G) → g * x = x * g
    constructor
    · intro hx g hg
      exact mul_inv_eq_iff_eq_mul.mp (hx ⟨g, hg⟩)
    · intro hx q
      exact mul_inv_eq_iff_eq_mul.mpr (hx q q.property)
  let f : G → Module.End k V := fun a => (z : k[G]).coeff a • rho a
  have hf : ∀ q : P, ∀ a : G, f (q • a) = f a := by
    intro q a
    have hq : rho (q : G) = 1 := MonoidHom.mem_ker.mp (hker q.property)
    have hqi : rho (q : G)⁻¹ = 1 := MonoidHom.mem_ker.mp (hker (P.inv_mem q.property))
    change (z : k[G]).coeff ((q : G) * a * (q : G)⁻¹) •
      rho ((q : G) * a * (q : G)⁻¹) = (z : k[G]).coeff a • rho a
    rw [GroupAlgebraCenter.coeff_conjugate z (q : G) a,
      map_mul, map_mul, hq, hqi, one_mul, mul_one]
  have hsum : (∑ a : G, f a) = ∑ a : centralizerOf P, f (a : G) := by
    calc
      (∑ a : G, f a) = ∑ a : MulAction.fixedPoints P G, f (a : G) :=
        sum_eq_sum_fixedPoints_of_invariant_module (k := k) hP f hf
      _ = ∑ a : centralizerOf P, f (a : G) :=
        Fintype.sum_equiv (Equiv.setCongr hfixed)
          (fun a : MulAction.fixedPoints P G => f (a : G))
          (fun a : centralizerOf P => f (a : G)) (fun _ => rfl)
  calc
    rho.asAlgebraHom z.val = ∑ a : G, f a := by
      rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply,
        Finsupp.sum_fintype _ _ (fun a => zero_smul k (rho a))]
    _ = ∑ a : centralizerOf P, f (a : G) := hsum
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have ha : (z : k[G]).coeff (a : G) = 0 := by
        change ((centralBrauerRestriction P z :
          GroupAlgebraCenter k (centralizerOf P)) : k[centralizerOf P]).coeff a = 0
        rw [hz]
        rfl
      change (z : k[G]).coeff (a : G) • rho (a : G) = 0
      rw [ha, zero_smul]

theorem central_action_eq_zero_of_normal_p
    {p : ℕ} {k G V : Type*}
    [Field k] [CharP k p] [Fact p.Prime] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Nontrivial V]
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (rho : Representation k G V) (hirr : rho.IsIrreducible)
    (z : GroupAlgebraCenter k G)
    (hz : centralBrauerRestriction P z = 0) :
    rho.asAlgebraHom z.val = 0 :=
  central_action_eq_zero_of_p_kernel P hP rho
    (normal_subgroup_le_ker_of_invariants_ne_bot rho P hirr
      (invariants_ne_bot_of_isPGroup (Fact.out : p.Prime) hP (rho.comp P.subtype))) z hz

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPKernelCentralAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
