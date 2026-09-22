import ModularRep.PaperProofs.TypeBIntegralCyclotomicRoot
import ModularRep.PaperProofs.TypeBModularRootReduction
import Mathlib.RingTheory.Henselian

/-!
# Coherent roots from the actual complete modular system

Hensel lifting for X^m - 1 makes the actual residue map bijective on
integral roots of positive order prime to the residue characteristic.
The fraction-field inclusion is bijective on integral roots of every
positive order. Their composition gives the cross-characteristic root
equivalence, with uniqueness and coherence under order divisibility.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBModularCommonRootBinding

open ModularRep Polynomial

universe uK uO uk

variable {ell m n : ℕ} {K : Type uK} {O : Type uO} {k : Type uk}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  (Msys : ModularSystem ell K O k)

/-- Every existing residue root of prime-to-ell order lifts to an integral
root of the same defining power equation. -/
theorem exists_integral_lift (hm : 0 < m) (hc : m.Coprime ell)
    {z : k} (hz : z ^ m = 1) :
    ∃ a : O, a ^ m = 1 ∧ Msys.residue a = z := by
  letI := Msys.isDiscreteValuationRing
  letI := Msys.isAdicComplete
  let P : O[X] := X ^ m - C (1 : O)
  obtain ⟨a₀, ha₀⟩ := Msys.residue_surjective z
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hm.ne'] at hz
    exact zero_ne_one hz
  have hroot : P.eval a₀ ∈ IsLocalRing.maximalIdeal O := by
    change P.eval a₀ ∈ Msys.maximalIdeal
    apply (Msys.residue_eq_zero_iff (P.eval a₀)).mp
    simp only [P, eval_sub, eval_pow, eval_X, eval_C, eval_one,
      map_sub, map_pow, map_one, ha₀, hz, sub_self]
  have hderivative : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
        (P.derivative.eval a₀)) := by
    apply (MulEquiv.isUnit_map Msys.residueEquiv.toMulEquiv).mp
    change IsUnit (Msys.residue (P.derivative.eval a₀))
    rw [isUnit_iff_ne_zero]
    simpa only [P, derivative_sub, derivative_X_pow, derivative_C,
      sub_zero, eval_mul, eval_C, eval_natCast, eval_pow, eval_X, map_mul,
      map_natCast, map_pow, ha₀] using
      mul_ne_zero
        (TypeBModularRootReduction.residue_natCast_ne_zero Msys hc)
        (pow_ne_zero (m - 1) hz0)
  obtain ⟨a, ha, hdiff⟩ := HenselianRing.is_henselian
    (I := IsLocalRing.maximalIdeal O) P
    (monic_X_pow_sub_C (1 : O) hm.ne') a₀ hroot hderivative
  have hpow : a ^ m = 1 := by
    apply sub_eq_zero.mp
    simpa only [IsRoot.def, P, eval_sub, eval_pow, eval_X, eval_C] using ha
  have hresidue : Msys.residue a = Msys.residue a₀ := by
    apply sub_eq_zero.mp
    simpa only [map_sub] using
      (Msys.residue_eq_zero_iff (a - a₀)).mpr hdiff
  exact ⟨a, hpow, hresidue.trans ha₀⟩

/-- Surjectivity of the literal residue homomorphism on root subgroups. -/
theorem residue_roots_surjective (hm : 0 < m) (hc : m.Coprime ell) :
    Function.Surjective (restrictRootsOfUnity Msys.residue m) := by
  letI : NeZero m := ⟨hm.ne'⟩
  intro z
  obtain ⟨a, ha, hresidue⟩ := exists_integral_lift Msys hm hc
    ((mem_rootsOfUnity' m (z : kˣ)).mp z.property)
  refine ⟨rootsOfUnity.mkOfPowEq a ha, ?_⟩
  apply rootsOfUnity.coe_injective
  exact hresidue

/-- Bijectivity uses Hensel existence and the checked torsion-kernel proof. -/
theorem residue_roots_bijective (hm : 0 < m) (hc : m.Coprime ell) :
    Function.Bijective (restrictRootsOfUnity Msys.residue m) := by
  refine ⟨?_, residue_roots_surjective Msys hm hc⟩
  intro x y hxy
  apply TypeBModularRootReduction.residue_injective_rootsOfUnity Msys hc
  exact congrArg (fun z : rootsOfUnity m k => ((z : kˣ) : k)) hxy

include Msys in
/-- Every ordinary root is integral, and the actual fraction-field map
is injective. -/
theorem algebraMap_roots_bijective (hm : 0 < m) :
    Function.Bijective (restrictRootsOfUnity (algebraMap O K) m) := by
  letI := Msys.isFractionRing
  letI : NeZero m := ⟨hm.ne'⟩
  constructor
  · intro x y hxy
    apply rootsOfUnity.coe_injective
    apply IsFractionRing.injective O K
    exact congrArg (fun z : rootsOfUnity m K => ((z : Kˣ) : K)) hxy
  · intro z
    have hz : ((z : Kˣ) : K) ^ m = 1 :=
      (mem_rootsOfUnity' m (z : Kˣ)).mp z.property
    obtain ⟨a, ha⟩ := TypeBIntegralCyclotomicRoot.exists_integral_root Msys hm hz
    have hpow : a ^ m = 1 := by
      apply IsFractionRing.injective O K
      rw [map_pow, ha, hz, map_one]
    refine ⟨rootsOfUnity.mkOfPowEq a hpow, ?_⟩
    apply rootsOfUnity.coe_injective
    exact ha

/-- The equivalence induced by the prescribed residue homomorphism. -/
def residueRootEquiv (hm : 0 < m) (hc : m.Coprime ell) :
    rootsOfUnity m O ≃* rootsOfUnity m k :=
  MulEquiv.ofBijective (restrictRootsOfUnity Msys.residue m)
    (residue_roots_bijective Msys hm hc)

/-- The equivalence induced by the prescribed fraction-field inclusion. -/
def ordinaryRootEquiv (hm : 0 < m) :
    rootsOfUnity m O ≃* rootsOfUnity m K :=
  MulEquiv.ofBijective (restrictRootsOfUnity (algebraMap O K) m)
    (algebraMap_roots_bijective Msys hm)

/-- The common-root convention is the inverse of actual reduction. -/
def rootEquiv (hm : 0 < m) (hc : m.Coprime ell) :
    rootsOfUnity m k ≃* rootsOfUnity m K :=
  (residueRootEquiv Msys hm hc).symm.trans (ordinaryRootEquiv Msys hm)

/-- An integral root and its residue have exactly corresponding values. -/
theorem rootEquiv_residue (hm : 0 < m) (hc : m.Coprime ell)
    (z : rootsOfUnity m O) :
    rootEquiv Msys hm hc (restrictRootsOfUnity Msys.residue m z) =
      restrictRootsOfUnity (algebraMap O K) m z := by
  change ordinaryRootEquiv Msys hm
      ((residueRootEquiv Msys hm hc).symm (residueRootEquiv Msys hm hc z)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The integral-root square on the actual coefficient fields. -/
theorem rootEquiv_integral (hm : 0 < m) (hc : m.Coprime ell)
    (z : rootsOfUnity m O) :
    (((rootEquiv Msys hm hc (restrictRootsOfUnity Msys.residue m z)) : Kˣ) : K) =
      algebraMap O K ((z : Oˣ) : O) :=
  congrArg (fun w : rootsOfUnity m K => ((w : Kˣ) : K))
    (rootEquiv_residue Msys hm hc z)

/-- The unique integral lift on the actual root subgroup. -/
def integralLift (hm : 0 < m) (hc : m.Coprime ell)
    (z : rootsOfUnity m k) : rootsOfUnity m O :=
  (residueRootEquiv Msys hm hc).symm z

/-- Reduction of the constructed integral lift is the original root. -/
theorem integralLift_residue (hm : 0 < m) (hc : m.Coprime ell)
    (z : rootsOfUnity m k) :
    restrictRootsOfUnity Msys.residue m (integralLift Msys hm hc z) = z :=
  (residueRootEquiv Msys hm hc).apply_symm_apply z

/-- The ordinary value is the image of that same integral lift. -/
theorem integralLift_ordinary (hm : 0 < m) (hc : m.Coprime ell)
    (z : rootsOfUnity m k) :
    restrictRootsOfUnity (algebraMap O K) m (integralLift Msys hm hc z) =
      rootEquiv Msys hm hc z := rfl

/-- Equality of residues determines the integral lift uniquely. -/
theorem integralLift_unique (hm : 0 < m) (hc : m.Coprime ell)
    (z : rootsOfUnity m k) (a : rootsOfUnity m O)
    (ha : restrictRootsOfUnity Msys.residue m a = z) :
    a = integralLift Msys hm hc z := by
  apply (residue_roots_bijective Msys hm hc).injective
  exact ha.trans (integralLift_residue Msys hm hc z).symm

/-- The actual integral-root square uniquely determines the equivalence. -/
theorem rootEquiv_unique (hm : 0 < m) (hc : m.Coprime ell)
    (e : rootsOfUnity m k ≃* rootsOfUnity m K)
    (he : ∀ z : rootsOfUnity m O,
      e (restrictRootsOfUnity Msys.residue m z) =
        restrictRootsOfUnity (algebraMap O K) m z) :
    e = rootEquiv Msys hm hc := by
  apply MulEquiv.ext
  intro z
  obtain ⟨a, rfl⟩ := residue_roots_surjective Msys hm hc z
  exact (he a).trans (rootEquiv_residue Msys hm hc a).symm

/-- Dividing-order inclusions commute with the constructed equivalences. -/
theorem rootEquiv_coherent (hm : 0 < m) (hn : 0 < n)
    (hmc : m.Coprime ell) (hnc : n.Coprime ell) (hdiv : m ∣ n)
    (z : rootsOfUnity m k) :
    Subgroup.inclusion (rootsOfUnity_le_of_dvd hdiv) (rootEquiv Msys hm hmc z) =
      rootEquiv Msys hn hnc
        (Subgroup.inclusion (rootsOfUnity_le_of_dvd hdiv) z) := by
  obtain ⟨a, rfl⟩ := residue_roots_surjective Msys hm hmc z
  rw [rootEquiv_residue]
  have hresidue :
      Subgroup.inclusion (rootsOfUnity_le_of_dvd hdiv)
          (restrictRootsOfUnity Msys.residue m a) =
        restrictRootsOfUnity Msys.residue n
          (Subgroup.inclusion (rootsOfUnity_le_of_dvd hdiv) a) := rfl
  rw [hresidue, rootEquiv_residue]
  rfl

/-- Coherence expressed directly in the ordinary value field. -/
theorem rootEquiv_coherent_value (hm : 0 < m) (hn : 0 < n)
    (hmc : m.Coprime ell) (hnc : n.Coprime ell) (hdiv : m ∣ n)
    (z : rootsOfUnity m k) :
    (((rootEquiv Msys hm hmc z) : Kˣ) : K) =
      (((rootEquiv Msys hn hnc
        (Subgroup.inclusion (rootsOfUnity_le_of_dvd hdiv) z)) : Kˣ) : K) :=
  congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K))
    (rootEquiv_coherent Msys hm hn hmc hnc hdiv z)

end ModularRep.PaperProofs.TypeBModularCommonRootBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
