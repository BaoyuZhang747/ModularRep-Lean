import ModularRep.CyclotomicRootSumReflection
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Cyclotomic-order specialisation for root-sum determinants

This file reflects a zero determinant from characteristic zero to
characteristic `p`.  Both root-sum matrices are
obtained from a single matrix over the integral cyclotomic order
`Z[X] / (Phi_n)`.  The characteristic-zero specialisation is injective, so a
zero determinant there forces the common determinant to vanish before the
modular specialisation is applied.
-/

noncomputable section

open Polynomial
open scoped Matrix

universe u v

namespace ModularRep.CyclotomicDeterminantSpecialization

open CyclotomicRootSumReflection

/-- The integral cyclotomic order `Z[zeta_n]`, presented as an adjoined root. -/
abbrev CyclotomicOrder (n : ℕ) := AdjoinRoot (cyclotomic n ℤ)

/-- Evaluation of the integral cyclotomic order at a primitive `n`th root in
an arbitrary field. -/
noncomputable def cyclotomicSpecialization
    {F : Type u} [Field F] {n : ℕ} (hn : 0 < n)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta n) :
    CyclotomicOrder n →+* F :=
  AdjoinRoot.lift (Int.castRingHom F) zeta (by
    simpa only [eval₂_eq_eval_map, map_cyclotomic, IsRoot.def] using
      hzeta.isRoot_cyclotomic hn)

@[simp]
theorem cyclotomicSpecialization_root
    {F : Type u} [Field F] {n : ℕ} (hn : 0 < n)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta n) :
    cyclotomicSpecialization hn hzeta
        (AdjoinRoot.root (cyclotomic n ℤ)) = zeta := by
  exact AdjoinRoot.lift_root _

/-- In characteristic zero, evaluation at a primitive root embeds the integral
cyclotomic order. -/
theorem cyclotomicSpecialization_injective
    {K : Type v} [Field K] [CharZero K] {n : ℕ} (hn : 0 < n)
    {zeta : K} (hzeta : IsPrimitiveRoot zeta n) :
    Function.Injective (cyclotomicSpecialization hn hzeta) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih P =>
      rw [AdjoinRoot.mk_eq_zero]
      have hP : aeval zeta P = 0 := by
        rw [aeval_def, show algebraMap ℤ K = Int.castRingHom K by
          exact RingHom.ext_int _ _]
        simpa only [cyclotomicSpecialization, AdjoinRoot.lift_mk] using hx
      rw [cyclotomic_eq_minpoly hzeta hn]
      exact (minpoly.isIntegrallyClosed_dvd_iff
        (hzeta.isIntegral hn) P).mp hP

/-- A matrix over the integral cyclotomic order has zero determinant after
modular specialisation whenever it has zero determinant at a primitive root
in characteristic zero. -/
theorem det_eq_zero_of_cyclotomicSpecializations
    {k : Type u} {K : Type v} [Field k] [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) {zeta_k : k} {zeta_K : K}
    (hk : IsPrimitiveRoot zeta_k n) (hK : IsPrimitiveRoot zeta_K n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (CyclotomicOrder n))
    (hzero : Matrix.det
      ((cyclotomicSpecialization hn hK).mapMatrix M) = 0) :
    Matrix.det ((cyclotomicSpecialization hn hk).mapMatrix M) = 0 := by
  have hcommon : M.det = 0 := by
    apply (cyclotomicSpecialization_injective hn hK)
    rw [map_zero, RingHom.map_det]
    exact hzero
  rw [← RingHom.map_det, hcommon, map_zero]

/-- Equivalently, a nonzero determinant after modular specialisation remains
nonzero at the corresponding characteristic-zero primitive root. -/
theorem det_ne_zero_of_cyclotomicSpecializations
    {k : Type u} {K : Type v} [Field k] [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) {zeta_k : k} {zeta_K : K}
    (hk : IsPrimitiveRoot zeta_k n) (hK : IsPrimitiveRoot zeta_K n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (CyclotomicOrder n))
    (hne : Matrix.det
      ((cyclotomicSpecialization hn hk).mapMatrix M) ≠ 0) :
    Matrix.det ((cyclotomicSpecialization hn hK).mapMatrix M) ≠ 0 := by
  contrapose! hne
  exact det_eq_zero_of_cyclotomicSpecializations hn hk hK M hne

/-- A finite sum of powers of the universal cyclotomic root. -/
noncomputable def cyclotomicRootSum {n : ℕ} (a : Multiset ℕ) :
    CyclotomicOrder n :=
  (a.map fun e ↦ AdjoinRoot.root (cyclotomic n ℤ) ^ e).sum

@[simp]
theorem cyclotomicSpecialization_cyclotomicRootSum
    {F : Type u} [Field F] {n : ℕ} (hn : 0 < n)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta n) (a : Multiset ℕ) :
    cyclotomicSpecialization hn hzeta (cyclotomicRootSum a) =
      (a.map fun e ↦ zeta ^ e).sum := by
  rw [cyclotomicRootSum, map_multiset_sum]
  simp only [Multiset.map_map, Function.comp_apply, map_pow,
    cyclotomicSpecialization_root]

/-- A matrix whose entries are universal finite sums of powers of the
cyclotomic root. -/
noncomputable def cyclotomicRootSumMatrix
    {n : ℕ} {ι : Type*} (a : ι → ι → Multiset ℕ) :
    Matrix ι ι (CyclotomicOrder n) :=
  fun i j ↦ cyclotomicRootSum (a i j)

theorem mapMatrix_cyclotomicRootSumMatrix
    {F : Type u} [Field F] {n : ℕ} (hn : 0 < n)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → Multiset ℕ) :
    (cyclotomicSpecialization hn hzeta).mapMatrix
        (cyclotomicRootSumMatrix a) =
      fun i j ↦ ((a i j).map fun e ↦ zeta ^ e).sum := by
  ext i j
  exact cyclotomicSpecialization_cyclotomicRootSum hn hzeta (a i j)

/-- Determinant nonvanishing for a matrix of root sums passes from a
primitive root in arbitrary characteristic to the corresponding primitive
root in characteristic zero. -/
theorem rootSumMatrix_det_ne_zero_transfer
    {k : Type u} {K : Type v} [Field k] [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n) {zeta_k : k} {zeta_K : K}
    (hk : IsPrimitiveRoot zeta_k n) (hK : IsPrimitiveRoot zeta_K n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → Multiset ℕ)
    (hne : Matrix.det
      (fun i j ↦ ((a i j).map fun e ↦ zeta_k ^ e).sum) ≠ 0) :
    Matrix.det
      (fun i j ↦ ((a i j).map fun e ↦ zeta_K ^ e).sum) ≠ 0 := by
  let M : Matrix ι ι (CyclotomicOrder n) := cyclotomicRootSumMatrix a
  have h := det_ne_zero_of_cyclotomicSpecializations hn hk hK M
  rw [mapMatrix_cyclotomicRootSumMatrix] at h
  rw [mapMatrix_cyclotomicRootSumMatrix] at h
  exact h hne

/-- Determinant nonvanishing transfers for matrices whose entries are sums
of `n`th roots of unity related by a multiplicative equivalence.  This is the
form needed for evaluation matrices of Brauer root sums. -/
theorem rootMultisetMatrix_det_ne_zero_transfer
    {k : Type u} {K : Type v} [Field k] [Field K] [CharZero K]
    {n : ℕ} (hn : 0 < n)
    (iota : rootsOfUnity n k ≃* rootsOfUnity n K)
    {zeta : k} (hk : IsPrimitiveRoot zeta n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → Multiset (rootsOfUnity n k))
    (hne : Matrix.det
      (fun i j ↦ (a i j).map
        (fun z ↦ (((z : rootsOfUnity n k) : kˣ) : k)) |>.sum) ≠ 0) :
    Matrix.det
      (fun i j ↦ (a i j).map
        (fun z ↦ (((iota z : rootsOfUnity n K) : Kˣ) : K)) |>.sum) ≠ 0 := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let zetaK : K :=
    (((iota (primitiveRootOfUnity hk) : rootsOfUnity n K) : Kˣ) : K)
  let exponents : ι → ι → Multiset ℕ :=
    fun i j ↦ (a i j).map (rootExponent hk)
  have hK : IsPrimitiveRoot zetaK n :=
    image_primitive_isPrimitive iota hk
  have hsource :
      (fun i j ↦ (a i j).map
          (fun z ↦ (((z : rootsOfUnity n k) : kˣ) : k)) |>.sum) =
        fun i j ↦ ((exponents i j).map fun e ↦ zeta ^ e).sum := by
    funext i j
    simp only [exponents, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    exact (pow_rootExponent hk z).symm
  have htarget :
      (fun i j ↦ (a i j).map
          (fun z ↦ (((iota z : rootsOfUnity n K) : Kˣ) : K)) |>.sum) =
        fun i j ↦ ((exponents i j).map fun e ↦ zetaK ^ e).sum := by
    funext i j
    simp only [exponents, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    exact congrArg
      (fun w : rootsOfUnity n K ↦ (((w : Kˣ) : K)))
      (image_root_eq_image_primitive_pow iota hk z)
  rw [hsource] at hne
  rw [htarget]
  exact rootSumMatrix_det_ne_zero_transfer hn hk hK exponents hne

end ModularRep.CyclotomicDeterminantSpecialization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
