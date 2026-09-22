import ModularRep.ModularSystem
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Ring.GeomSum

/-!
# Prime-to-characteristic integral roots retain their order under reduction

The reduction map is the actual residue homomorphism of the prescribed
modular system. A root of order dividing m that reduces to one is one:
its geometric sum reduces to the nonzero scalar m, and the domain identity
`sum * (z - 1) = z ^ m - 1` then forces `z - 1 = 0`.

This proves preservation of primitive roots and injectivity on the actual
integral roots of unity. No root equivalence, root-lifting existence,
coefficient field embedding or character compatibility is assumed here.
Completeness and local-unit arguments are unnecessary for this direction.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBModularRootReduction

open ModularRep

universe uK uO uk

variable {ell m : ℕ} {K : Type uK} {O : Type uO} {k : Type uk}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  (Msys : ModularSystem ell K O k)

include Msys in
/-- The exponent is nonzero in the actual residue field. -/
theorem residue_natCast_ne_zero (hm : m.Coprime ell) : (m : k) ≠ 0 := by
  letI := Msys.charP
  intro hzero
  exact (Msys.prime.coprime_iff_not_dvd.mp hm.symm)
    ((CharP.cast_eq_zero_iff k ell m).mp hzero)

/-- The prime-to-residue-characteristic torsion kernel is trivial. -/
theorem eq_one_of_pow_eq_one_of_residue_eq_one (hm : m.Coprime ell)
    {z : O} (hz : z ^ m = 1) (hresidue : Msys.residue z = 1) : z = 1 := by
  have hsum : (∑ i ∈ Finset.range m, z ^ i) ≠ 0 := by
    intro hzero
    have h := congrArg Msys.residue hzero
    have hmzero : (m : k) = 0 := by
      simpa only [map_sum, map_pow, hresidue, one_pow, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
    exact residue_natCast_ne_zero Msys hm hmzero
  have hmul : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hz, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hsum)

/-- Every integral primitive root of prime-to-ell order reduces to a
primitive root of exactly the same order in the identified residue field. -/
theorem isPrimitiveRoot_residue (hm : m.Coprime ell) {z : O}
    (hz : IsPrimitiveRoot z m) : IsPrimitiveRoot (Msys.residue z) m := by
  refine ⟨?_, ?_⟩
  · simpa only [map_pow, map_one] using congrArg Msys.residue hz.pow_eq_one
  · intro j hj
    apply hz.dvd_of_pow_eq_one j
    apply eq_one_of_pow_eq_one_of_residue_eq_one Msys hm
    · rw [← pow_mul, Nat.mul_comm j m, pow_mul, hz.pow_eq_one, one_pow]
    · simpa only [map_pow] using hj

/-- The primitive-root statement on the actual integral unit carrier. -/
theorem isPrimitiveRoot_residue_unit (hm : m.Coprime ell) (u : Oˣ)
    (hu : IsPrimitiveRoot (u : O) m) :
    IsPrimitiveRoot (Msys.residue (u : O)) m :=
  isPrimitiveRoot_residue Msys hm hu

/-- Two integral units of order dividing m with the same reduction agree. -/
theorem unit_eq_of_residue_eq_of_pow_eq_one (hm : m.Coprime ell)
    {u v : Oˣ} (hu : u ^ m = 1) (hv : v ^ m = 1)
    (hresidue : Msys.residue (u : O) = Msys.residue (v : O)) : u = v := by
  have hpow : ((u * v⁻¹ : Oˣ) : O) ^ m = 1 := by
    change (((u * v⁻¹) ^ m : Oˣ) : O) = 1
    rw [mul_pow, inv_pow, hu, hv]
    simp only [inv_one, mul_one, Units.val_one]
  have hres : Msys.residue ((u * v⁻¹ : Oˣ) : O) = 1 := by
    change Msys.residue ((u : O) * ((v⁻¹ : Oˣ) : O)) = 1
    rw [map_mul, hresidue, ← map_mul, Units.mul_inv, map_one]
  have heq : (u * v⁻¹ : Oˣ) = 1 :=
    Units.ext (eq_one_of_pow_eq_one_of_residue_eq_one Msys hm hpow hres)
  exact mul_inv_eq_one.mp heq

/-- Reduction is injective on the actual subgroup of integral m-th roots.
There is no assumed or constructed surjectivity in this statement. -/
theorem residue_injective_rootsOfUnity (hm : m.Coprime ell) :
    Function.Injective
      (fun z : rootsOfUnity m O => Msys.residue ((z : Oˣ) : O)) := by
  intro x y hxy
  apply Subtype.ext
  exact unit_eq_of_residue_eq_of_pow_eq_one Msys hm
    ((mem_rootsOfUnity m (x : Oˣ)).mp x.property)
    ((mem_rootsOfUnity m (y : Oˣ)).mp y.property) hxy

end ModularRep.PaperProofs.TypeBModularRootReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
