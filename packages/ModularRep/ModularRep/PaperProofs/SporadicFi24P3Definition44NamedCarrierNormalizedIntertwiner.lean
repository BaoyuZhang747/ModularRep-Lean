import ModularRep.CyclicExtension
import ModularRep.CentralAction
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.Group

/-!
An invariant irreducible representation has a conjugating operator whose square
is the action of the square of the ambient element. This is the index-two
specialization of the normalization in Navarro, Theorem 8.12, p. 163.
-/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedIntertwiner

open Representation
open scoped MonoidAlgebra

variable {k H V : Type*} [Field k] [IsAlgClosed k] [Group H]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {N : Subgroup H} [N.Normal]

theorem exists_normalized_conjugating_operator
    (rho : Representation k N V) (hirr : rho.IsIrreducible)
    (t : H) (ht2 : t * t ∈ N)
    (hinvariant : ConjugationInvariant N rho) :
    ∃ U : Module.End k V,
      (∀ n : N, U * rho n = rho (MulAut.conjNormal t n) * U) ∧
      U * U = rho ⟨t * t, ht2⟩ := by
  let _ : rho.IsIrreducible := hirr
  let _ : Nontrivial V := IsSimpleModule.nontrivial k[N] rho.asModule
  obtain ⟨e⟩ := hinvariant t
  let T : Module.End k V := e.symm.toLinearMap
  let q : N := ⟨t * t, ht2⟩
  have hT (n : N) : T * rho n = rho (MulAut.conjNormal t n) * T :=
    e.symm.isIntertwining' n
  have hconj (n : N) :
      MulAut.conjNormal t (MulAut.conjNormal t n) = q * n * q⁻¹ := by
    apply Subtype.ext
    change t * (t * (n : H) * t⁻¹) * t⁻¹ =
      (t * t) * (n : H) * (t * t)⁻¹
    group
  have hTT (n : N) :
      (T * T) * rho n = rho (q * n * q⁻¹) * (T * T) := by
    calc
      (T * T) * rho n = T * (T * rho n) := mul_assoc _ _ _
      _ = T * (rho (MulAut.conjNormal t n) * T) := by rw [hT]
      _ = (T * rho (MulAut.conjNormal t n)) * T := (mul_assoc _ _ _).symm
      _ = (rho (MulAut.conjNormal t (MulAut.conjNormal t n)) * T) * T := by
        rw [hT]
      _ = rho (q * n * q⁻¹) * (T * T) := by rw [hconj, mul_assoc]
  let C : IntertwiningMap rho rho :=
    { toLinearMap := rho q⁻¹ * (T * T)
      isIntertwining' n := by
        change (rho q⁻¹ * (T * T)) * rho n = rho n * (rho q⁻¹ * (T * T))
        calc
          _ = rho q⁻¹ * ((T * T) * rho n) := mul_assoc _ _ _
          _ = rho q⁻¹ * (rho (q * n * q⁻¹) * (T * T)) := by rw [hTT]
          _ = rho (q⁻¹ * (q * n * q⁻¹)) * (T * T) := by
            rw [← mul_assoc, ← map_mul]
          _ = rho (n * q⁻¹) * (T * T) := by congr 2; group
          _ = rho n * (rho q⁻¹ * (T * T)) := by rw [map_mul, mul_assoc] }
  let c : k := (scalarIntertwiningEquiv rho).symm C
  have hC : C.toLinearMap = c • (1 : Module.End k V) := by
    have h := congrArg IntertwiningMap.toLinearMap
      ((scalarIntertwiningEquiv rho).apply_symm_apply C).symm
    simpa only [scalarIntertwiningEquiv_toLinearMap, c, Module.End.one_eq_id] using h
  have hCin : Function.Injective C.toLinearMap :=
    (rho.apply_bijective q⁻¹).1.comp (e.symm.injective.comp e.symm.injective)
  have hc : c ≠ 0 := by
    intro hc
    have hz : C.toLinearMap = 0 := by rw [hC, hc, zero_smul]
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    apply hCin
    simp only [hz, LinearMap.zero_apply]
  have hTTc : T * T = c • rho q := by
    have h := congrArg (fun f : Module.End k V => rho q * f) hC
    change rho q * (rho q⁻¹ * (T * T)) = rho q * (c • 1) at h
    simpa only [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul,
      mul_smul_comm, mul_one] using h
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (by decide : 0 < 2)
  refine ⟨a • T, ?_, ?_⟩
  · intro n
    simpa only [smul_mul_assoc, mul_smul_comm] using congrArg (fun f => a • f) (hT n)
  · calc
      (a • T) * (a • T) = (a * a) • (T * T) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = (a ^ 2 * c) • rho q := by rw [← pow_two, hTTc, smul_smul]
      _ = rho q := by rw [ha, inv_mul_cancel₀ hc, one_smul]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedIntertwiner


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
