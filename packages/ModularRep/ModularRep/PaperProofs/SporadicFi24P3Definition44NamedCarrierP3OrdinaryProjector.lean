import ModularRep.GroupAlgebraCentralFunctions
import ModularRep.ModularTraceFunction

/-! The ordinary character sum and its product coefficients. The trace
identity proves that the sum annihilates the kernel of the same representation;
no splitting or modular reduction assumption is used here. -/

noncomputable section
open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrdinaryProjector

open ModularRep

variable {K G V W : Type*}
variable [Field K] [Group G] [Fintype G]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

def characterSum (rho : Representation K G V) (q : K) : K[G] :=
  ∑ g : G, MonoidAlgebra.single g (q * rho.character g⁻¹)

@[simp]
theorem characterSum_coeff (rho : Representation K G V) (q : K) (x : G) :
    (characterSum rho q).coeff x = q * rho.character x⁻¹ := by
  classical
  simp [characterSum, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem characterSum_mem_center
    (rho : Representation K G V) (q : K) :
    characterSum rho q ∈ GroupAlgebraCenter K G := by
  classical
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, mul_add, ha, hb]
  | single h r =>
      ext x
      simp only [MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply, characterSum_coeff,
        mul_inv_rev, inv_inv]
      rw [rho.char_mul_comm h x⁻¹]
      exact mul_comm _ _

theorem characterSum_mul_coeff
    (rho : Representation K G V) (q : K) (a : K[G]) (h : G) :
    (characterSum rho q * a).coeff h =
      q * rho.algebraTraceFunction
        (MonoidAlgebra.single h⁻¹ 1 * a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [mul_add, MonoidAlgebra.coeff_add,
        Finsupp.add_apply, map_add, ha, hb]
  | single g r =>
      simp only [MonoidAlgebra.coeff_mul_single_apply,
        characterSum_coeff, mul_inv_rev, inv_inv,
        MonoidAlgebra.single_mul_single, one_mul,
        Representation.algebraTraceFunction_single]
      rw [rho.char_mul_comm h⁻¹ g, mul_assoc,
        mul_comm (rho.character (h⁻¹ * g)) r]

theorem characterSum_mul_eq_zero_of_action_eq_zero
    (rho : Representation K G V) (q : K) (a : K[G])
    (ha : rho.asAlgebraHom a = 0) :
    characterSum rho q * a = 0 := by
  ext h
  change (characterSum rho q * a).coeff h = 0
  rw [characterSum_mul_coeff]
  change q * LinearMap.trace K V
    (rho.asAlgebraHom (MonoidAlgebra.single h⁻¹ 1 * a)) = 0
  rw [map_mul, ha, mul_zero, map_zero, mul_zero]

theorem characterSum_trace
    (rho : Representation K G V) (sigma : Representation K G W) (q : K) :
    sigma.algebraTraceFunction (characterSum rho q) =
      q * ∑ g : G, rho.character g⁻¹ * sigma.character g := by
  unfold characterSum
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Representation.algebraTraceFunction_single, mul_assoc]

def ordinaryProjector (rho : Representation K G V) : K[G] :=
  characterSum rho ((Module.finrank K V : K) / (Nat.card G : K))

@[simp]
theorem ordinaryProjector_coeff (rho : Representation K G V) (x : G) :
    (ordinaryProjector rho).coeff x =
      ((Module.finrank K V : K) / (Nat.card G : K)) * rho.character x⁻¹ :=
  characterSum_coeff rho _ x

def ordinaryProjectorInCenter (rho : Representation K G V) :
    GroupAlgebraCenter K G :=
  ⟨ordinaryProjector rho, characterSum_mem_center rho _⟩

omit [Fintype G] in
theorem central_action_scalar_of_surjective
    (rho : Representation K G V)
    (hsplit : Function.Surjective
      (algebraMap K (Representation.IntertwiningMap rho rho)))
    (e : K[G]) (he : IsMulCentral e) :
    ∃ t : K, rho.asAlgebraHom e = t • (1 : Module.End K V) := by
  let f : Representation.IntertwiningMap rho rho :=
    { toLinearMap := rho.asAlgebraHom e
      isIntertwining' g := by
        change rho.asAlgebraHom e * rho g = rho g * rho.asAlgebraHom e
        rw [← rho.asAlgebraHom_of, ← map_mul, ← map_mul]
        exact congrArg rho.asAlgebraHom (he.comm _).eq }
  obtain ⟨t, ht⟩ := hsplit f
  refine ⟨t, ?_⟩
  have h := congrArg Representation.IntertwiningMap.toLinearMap ht.symm
  rw [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul] at h
  exact h

omit [Fintype G] in
theorem central_action_one_of_trace
    [FiniteDimensional K V] [Nontrivial V] [CharZero K]
    (rho : Representation K G V)
    (hsplit : Function.Surjective
      (algebraMap K (Representation.IntertwiningMap rho rho)))
    (e : K[G]) (he : IsMulCentral e)
    (htrace : rho.algebraTraceFunction e = (Module.finrank K V : K)) :
    rho.asAlgebraHom e = 1 := by
  obtain ⟨t, ht⟩ := central_action_scalar_of_surjective rho hsplit e he
  have hd : (Module.finrank K V : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Module.finrank_pos)
  have h := congrArg (LinearMap.trace K V) ht
  simp only [map_smul, LinearMap.trace_one, smul_eq_mul] at h
  change LinearMap.trace K V (rho.asAlgebraHom e) = _ at htrace
  have ht1 : t = 1 :=
    mul_right_cancel₀ hd (h.symm.trans (htrace.trans (one_mul _).symm))
  simpa only [ht1, one_smul] using ht

theorem ordinaryProjector_idempotent_of_action_one
    (rho : Representation K G V)
    (ha : rho.asAlgebraHom (ordinaryProjector rho) = 1) :
    IsIdempotentElem (ordinaryProjector rho) := by
  have hz := characterSum_mul_eq_zero_of_action_eq_zero rho
    ((Module.finrank K V : K) / (Nat.card G : K))
    (ordinaryProjector rho - 1) (by rw [map_sub, ha, map_one, sub_self])
  change ordinaryProjector rho * (ordinaryProjector rho - 1) = 0 at hz
  exact sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using hz)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrdinaryProjector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
