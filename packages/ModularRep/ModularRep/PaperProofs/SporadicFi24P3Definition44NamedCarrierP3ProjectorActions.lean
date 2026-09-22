import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrdinaryProjector
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The selected norm makes its ordinary projector act as identity. Once
idempotence is proved, unequal irreducible degrees force zero action. -/

noncomputable section
open scoped BigOperators MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorActions
open ModularRep
open SporadicFi24P3Definition44NamedCarrierP3OrdinaryProjector

theorem ordinaryProjector_action_one_and_idempotent_of_norm
    {K G V : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K G V) [rho.IsIrreducible]
    (hnorm : (∑ g : G, rho.character g * rho.character g⁻¹) = (Nat.card G : K)) :
    rho.asAlgebraHom (ordinaryProjector rho) = 1 ∧
      IsIdempotentElem (ordinaryProjector rho) := by
  let : Nontrivial rho.asModule := IsSimpleModule.nontrivial K[G] rho.asModule
  let : Nontrivial V := rho.asModuleEquiv.symm.toEquiv.nontrivial
  have hN : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card G : K) := invertibleOfNonzero hN
  have horth := Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho rho
  rw [hnorm, inv_mul_cancel₀ hN] at horth
  have hEnd : Module.finrank K (Representation.IntertwiningMap rho rho) = 1 := by
    apply Nat.cast_injective (R := K)
    simpa only [Nat.cast_one] using horth.symm
  have hsplit : Function.Surjective
      (algebraMap K (Representation.IntertwiningMap rho rho)) := by
    let : Nontrivial (Representation.IntertwiningMap rho rho) :=
      Module.nontrivial_of_finrank_eq_succ hEnd
    intro f
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (1 : Representation.IntertwiningMap rho rho) one_ne_zero).mp hEnd f
    refine ⟨c, ?_⟩
    rw [Representation.IntertwiningMap.algebraMap_apply]
    exact hc
  have hc : IsMulCentral (ordinaryProjector rho) :=
    Set.mem_center_iff.mp
      (Semigroup.mem_center_iff.mpr
        (Subalgebra.mem_center_iff.mp (ordinaryProjectorInCenter rho).property))
  have hnorm' : (∑ g : G, rho.character g⁻¹ * rho.character g) = (Nat.card G : K) := by
    simpa only [mul_comm] using hnorm
  have ht : rho.algebraTraceFunction (ordinaryProjector rho) = (Module.finrank K V : K) := by
    change rho.algebraTraceFunction
      (characterSum rho ((Module.finrank K V : K) / (Nat.card G : K))) = _
    rw [characterSum_trace, hnorm']
    exact div_mul_cancel₀ _ hN
  have ha := central_action_one_of_trace rho hsplit (ordinaryProjector rho) hc ht
  exact ⟨ha, ordinaryProjector_idempotent_of_action_one rho ha⟩

theorem action_zero_of_idempotent_trace
    {K G W : Type*} [Field K] [CharZero K] [Monoid G]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (sigma : Representation K G W) (e : K[G])
    (he : IsIdempotentElem e) (ht : sigma.algebraTraceFunction e = 0) :
    sigma.asAlgebraHom e = 0 := by
  apply LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (he.map sigma.asAlgebraHom)
  exact ht

theorem ordinaryProjector_action_zero_of_finrank_ne
    {K G V W : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (rho : Representation K G V) (sigma : Representation K G W)
    [rho.IsIrreducible] [sigma.IsIrreducible]
    (he : IsIdempotentElem (ordinaryProjector rho))
    (hne : Module.finrank K V ≠ Module.finrank K W) :
    sigma.asAlgebraHom (ordinaryProjector rho) = 0 := by
  let : IsEmpty (Representation.Equiv rho sigma) :=
    ⟨fun E => hne E.toLinearEquiv.finrank_eq⟩
  have hN : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card G : K) := invertibleOfNonzero hN
  have horth : (Nat.card G : K)⁻¹ *
      ∑ g : G, sigma.character g * rho.character g⁻¹ = 0 := by
    simpa only [Module.finrank_zero_of_subsingleton, Nat.cast_zero] using
      Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho sigma
  have hsum : (∑ g : G, sigma.character g * rho.character g⁻¹) = 0 :=
    (mul_eq_zero.mp horth).resolve_left (inv_ne_zero hN)
  have hsum' : (∑ g : G, rho.character g⁻¹ * sigma.character g) = 0 := by
    simpa only [mul_comm] using hsum
  apply action_zero_of_idempotent_trace sigma _ he
  change sigma.algebraTraceFunction
    (characterSum rho ((Module.finrank K V : K) / (Nat.card G : K))) = 0
  rw [characterSum_trace, hsum', mul_zero]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3ProjectorActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
