import Mathlib.Algebra.CharP.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import ModularRep.PaperProofs.TypeBCentralKernelBrauerInflation

/-! The normal p-subgroup kernel theorem is proved by fixed vectors.
The additive span of one finite orbit is a finite elementary abelian
p-group, so p-group fixed-point counting supplies a nonzero invariant. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPSubgroupKernel

open ModularRep

universe u

theorem invariants_ne_bot_of_isPGroup
    {p : ℕ} {k G V : Type*}
    [Field k] [CharP k p] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Nontrivial V]
    (hp : p.Prime) (hG : IsPGroup p G) (rho : Representation k G V) :
    rho.invariants ≠ ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let s : Set V := Set.range (fun g : G => rho g v)
  let A : AddSubgroup V := AddSubgroup.closure s
  let : Finite s := (Set.finite_range (fun g : G => rho g v)).to_subtype
  let : AddGroup.FG A := AddGroup.closure_finite_fg s
  have hkillV (w : V) : p • w = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k p w, CharP.cast_eq_zero k p, zero_smul]
  have hkillA (a : A) : p • a = 0 := by
    apply Subtype.ext
    change p • (a : V) = 0
    exact hkillV a
  have htorsion : IsAddTorsion A := by
    intro a
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p, hp.pos, hkillA a⟩
  let : Finite A := AddCommGroup.finite_of_fg_isAddTorsion A htorsion
  have hvA : v ∈ A := by
    apply AddSubgroup.subset_closure
    refine ⟨1, ?_⟩
    simp
  let : Nontrivial A := ⟨⟨⟨v, hvA⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hAp : IsPGroup p (Multiplicative A) := by
    intro a
    refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    change (p ^ 1) • a.toAdd = 0
    simpa only [pow_one] using hkillA a.toAdd
  have hcardA : p ∣ Nat.card A := by
    have hdvd : p ∣ Nat.card (Multiplicative A) :=
      hAp.card_eq_or_dvd.resolve_left
        (Finite.one_lt_card : 1 < Nat.card (Multiplicative A)).ne'
    rwa [Nat.card_congr Multiplicative.toAdd] at hdvd
  have hstable (g : G) : A ≤ A.comap (rho g).toAddMonoidHom := by
    change AddSubgroup.closure s ≤ _
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨h, rfl⟩
    change rho g (rho h v) ∈ A
    have heq : rho g (rho h v) = rho (g * h) v :=
      (congrArg (fun T : Module.End k V => T v) (map_mul rho g h)).symm
    rw [heq]
    exact AddSubgroup.subset_closure ⟨g * h, rfl⟩
  let : MulAction G A := {
    smul := fun g a => ⟨rho g a.1, hstable g a.2⟩
    one_smul := by
      intro a
      apply Subtype.ext
      exact congrArg (fun T : Module.End k V => T (a : V)) (map_one rho)
    mul_smul := by
      intro g h a
      apply Subtype.ext
      exact congrArg (fun T : Module.End k V => T (a : V)) (map_mul rho g h) }
  have hzero : (0 : A) ∈ MulAction.fixedPoints G A := by
    intro g
    apply Subtype.ext
    exact map_zero (rho g)
  obtain ⟨w, hw, hne⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point A hcardA hzero
  intro hbot
  have hwmem : (w : V) ∈ rho.invariants := by
    intro g
    exact congrArg Subtype.val (hw g)
  rw [hbot, Submodule.mem_bot] at hwmem
  apply hne
  apply Subtype.ext
  exact hwmem.symm

theorem normal_subgroup_le_ker_of_invariants_ne_bot
    {k X V : Type*} [Field k] [Group X] [AddCommGroup V] [Module k V]
    (rho : Representation k X V) (R : Subgroup X) [R.Normal]
    (hirr : Representation.IsIrreducible rho)
    (hfixed : Representation.invariants (rho.comp R.subtype) ≠ ⊥) : R ≤ rho.ker := by
  let : Representation.IsIrreducible rho := hirr
  let W : Subrepresentation rho := {
    toSubmodule := Representation.invariants (rho.comp R.subtype)
    apply_mem_toSubmodule := by
      intro g v hv
      exact Representation.le_comap_invariants rho R g hv }
  have htop : W = ⊤ := by
    rcases eq_bot_or_eq_top W with hbot | htop
    · exact (hfixed (congrArg Subrepresentation.toSubmodule hbot)).elim
    · exact htop
  intro x hx
  apply MonoidHom.mem_ker.mpr
  apply LinearMap.ext
  intro v
  change rho x v = v
  have hv : v ∈ Representation.invariants (rho.comp R.subtype) := by
    change v ∈ W
    rw [htop]
    trivial
  exact hv ⟨x, hx⟩

theorem navarro232Principle (p : ℕ) (k : Type u)
    [Field k] [CharP k p] [IsAlgClosed k] :
    TypeBCentralKernelBrauerInflation.Navarro232Principle p k := by
  intro X _ _ R _ hp hR U hU
  let : Representation.IsIrreducible U.ρ := hU
  let : Nontrivial U :=
    IsSimpleModule.nontrivial (MonoidAlgebra k X) (Representation.asModule U.ρ)
  exact normal_subgroup_le_ker_of_invariants_ne_bot U.ρ R hU
    (invariants_ne_bot_of_isPGroup hp hR (U.ρ.comp R.subtype))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPSubgroupKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
