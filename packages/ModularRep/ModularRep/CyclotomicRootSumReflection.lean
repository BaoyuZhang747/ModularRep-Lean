import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

open Polynomial

namespace ModularRep.CyclotomicRootSumReflection

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [CharZero K]

/-- An integral polynomial relation at a primitive root in characteristic zero
remains a relation at every primitive root of the same order in any field. -/
theorem eval₂_int_eq_zero_of_primitiveRoots
    {n : ℕ} (hn : 0 < n) {zeta_k : k} {zeta_K : K}
    (hk : IsPrimitiveRoot zeta_k n) (hK : IsPrimitiveRoot zeta_K n)
    (P : ℤ[X]) (hP : aeval zeta_K P = 0) :
    aeval zeta_k P = 0 := by
  have hdvd : cyclotomic n ℤ ∣ P := by
    rw [cyclotomic_eq_minpoly hK hn]
    exact (minpoly.isIntegrallyClosed_dvd_iff (hK.isIntegral hn) P).mp hP
  apply aeval_eq_zero_of_dvd_aeval_eq_zero hdvd
  simpa only [aeval_def, eval₂_eq_eval_map, map_cyclotomic, IsRoot.def] using
    hk.isRoot_cyclotomic hn

/-- Equality of two finite sums of powers of a primitive root in
characteristic zero is reflected by a primitive root of the same order in
any field.  The two sums may have different finite index types. -/
theorem sum_pow_eq_of_sum_pow_eq
    {n : ℕ} (hn : 0 < n) {zeta_k : k} {zeta_K : K}
    (hk : IsPrimitiveRoot zeta_k n) (hK : IsPrimitiveRoot zeta_K n)
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℕ) (b : J → ℕ)
    (h : (∑ i, zeta_K ^ a i) = ∑ j, zeta_K ^ b j) :
    (∑ i, zeta_k ^ a i) = ∑ j, zeta_k ^ b j := by
  let P : ℤ[X] := (∑ i, X ^ a i) - ∑ j, X ^ b j
  have hP : aeval zeta_K P = 0 := by
    simp [P, h]
  have hkP := eval₂_int_eq_zero_of_primitiveRoots hn hk hK P hP
  exact sub_eq_zero.mp (by simpa [P] using hkP)

/-- Multiset form of `sum_pow_eq_of_sum_pow_eq`. -/
theorem multiset_sum_pow_eq_of_sum_pow_eq
    {n : ℕ} (hn : 0 < n) {zeta_k : k} {zeta_K : K}
    (hk : IsPrimitiveRoot zeta_k n) (hK : IsPrimitiveRoot zeta_K n)
    (a b : Multiset ℕ)
    (h : (a.map fun i ↦ zeta_K ^ i).sum =
      (b.map fun i ↦ zeta_K ^ i).sum) :
    (a.map fun i ↦ zeta_k ^ i).sum =
      (b.map fun i ↦ zeta_k ^ i).sum := by
  let P : ℤ[X] := (a.map fun i ↦ X ^ i).sum -
    (b.map fun i ↦ X ^ i).sum
  have hP : aeval zeta_K P = 0 := by
    simp only [P, aeval_def, eval₂_sub, eval₂_multiset_sum,
      Multiset.map_map, Function.comp_apply, eval₂_pow, eval₂_X]
    exact sub_eq_zero.mpr h
  have hkP := eval₂_int_eq_zero_of_primitiveRoots hn hk hK P hP
  simp only [P, aeval_def, eval₂_sub, eval₂_multiset_sum,
    Multiset.map_map, Function.comp_apply, eval₂_pow, eval₂_X] at hkP
  exact sub_eq_zero.mp hkP

section RootExponents

variable {n : ℕ} [NeZero n]

/-- The exponent, relative to a chosen primitive root, of an `n`th root of
unity. -/
noncomputable def rootExponent {zeta : k} (hk : IsPrimitiveRoot zeta n)
    (z : rootsOfUnity n k) : ℕ :=
  Classical.choose <| hk.eq_pow_of_pow_eq_one <|
    (mem_rootsOfUnity' n (z : kˣ)).mp z.prop

theorem rootExponent_lt {zeta : k} (hk : IsPrimitiveRoot zeta n)
    (z : rootsOfUnity n k) : rootExponent hk z < n :=
  (Classical.choose_spec <| hk.eq_pow_of_pow_eq_one <|
    (mem_rootsOfUnity' n (z : kˣ)).mp z.prop).1

theorem pow_rootExponent {zeta : k} (hk : IsPrimitiveRoot zeta n)
    (z : rootsOfUnity n k) :
    zeta ^ rootExponent hk z = ((z : kˣ) : k) :=
  (Classical.choose_spec <| hk.eq_pow_of_pow_eq_one <|
    (mem_rootsOfUnity' n (z : kˣ)).mp z.prop).2

/-- The primitive root, packaged as an element of `rootsOfUnity`. -/
noncomputable def primitiveRootOfUnity {zeta : k}
    (hk : IsPrimitiveRoot zeta n) : rootsOfUnity n k :=
  hk.toRootsOfUnity

theorem primitiveRootOfUnity_isPrimitive {zeta : k}
    (hk : IsPrimitiveRoot zeta n) :
    IsPrimitiveRoot (primitiveRootOfUnity hk) n := by
  rw [← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff]
  exact hk

theorem root_eq_primitiveRootOfUnity_pow {zeta : k}
    (hk : IsPrimitiveRoot zeta n) (z : rootsOfUnity n k) :
    z = primitiveRootOfUnity hk ^ rootExponent hk z := by
  apply rootsOfUnity.coe_injective
  simpa [primitiveRootOfUnity, IsPrimitiveRoot.toRootsOfUnity,
    rootsOfUnity.coe_pow] using
    (pow_rootExponent hk z).symm

end RootExponents

section RootSums

variable {n : ℕ} [NeZero n]

omit [CharZero K] in
theorem image_root_eq_image_primitive_pow
    (iota : rootsOfUnity n k ≃* rootsOfUnity n K)
    {zeta : k} (hk : IsPrimitiveRoot zeta n)
    (z : rootsOfUnity n k) :
    iota z = iota (primitiveRootOfUnity hk) ^ rootExponent hk z := by
  calc
    iota z = iota (primitiveRootOfUnity hk ^ rootExponent hk z) :=
      congrArg iota (root_eq_primitiveRootOfUnity_pow hk z)
    _ = iota (primitiveRootOfUnity hk) ^ rootExponent hk z :=
      map_pow iota (primitiveRootOfUnity hk) _

omit [CharZero K] in
theorem image_primitive_isPrimitive
    (iota : rootsOfUnity n k ≃* rootsOfUnity n K)
    {zeta : k} (hk : IsPrimitiveRoot zeta n) :
    IsPrimitiveRoot
      (((iota (primitiveRootOfUnity hk) : rootsOfUnity n K) : Kˣ) : K) n := by
  rw [IsPrimitiveRoot.coe_units_iff,
    IsPrimitiveRoot.coe_submonoidClass_iff]
  exact (primitiveRootOfUnity_isPrimitive hk).map_of_injective iota.injective

/-- Equality of finite sums after applying a multiplicative equivalence of
`n`th roots from an arbitrary field to a characteristic zero field implies
equality of the original sums.  A primitive `n`th root in the source is the
only existence input. -/
theorem multiset_sum_coe_eq_of_image_sum_eq
    (iota : rootsOfUnity n k ≃* rootsOfUnity n K)
    {zeta : k} (hk : IsPrimitiveRoot zeta n)
    (a b : Multiset (rootsOfUnity n k))
    (h : (a.map fun z ↦ (((iota z : rootsOfUnity n K) : Kˣ) : K)).sum =
      (b.map fun z ↦ (((iota z : rootsOfUnity n K) : Kˣ) : K)).sum) :
    (a.map fun z ↦ (((z : rootsOfUnity n k) : kˣ) : k)).sum =
      (b.map fun z ↦ (((z : rootsOfUnity n k) : kˣ) : k)).sum := by
  let zeta_K : K :=
    (((iota (primitiveRootOfUnity hk) : rootsOfUnity n K) : Kˣ) : K)
  let ea : Multiset ℕ := a.map (rootExponent hk)
  let eb : Multiset ℕ := b.map (rootExponent hk)
  have haK :
      (a.map fun z ↦ (((iota z : rootsOfUnity n K) : Kˣ) : K)).sum =
        (ea.map fun e ↦ zeta_K ^ e).sum := by
    congr 1
    simp only [ea, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z hz
    exact congrArg (fun w : rootsOfUnity n K ↦ (((w : Kˣ) : K)))
      (image_root_eq_image_primitive_pow iota hk z)
  have hbK :
      (b.map fun z ↦ (((iota z : rootsOfUnity n K) : Kˣ) : K)).sum =
        (eb.map fun e ↦ zeta_K ^ e).sum := by
    congr 1
    simp only [eb, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z hz
    exact congrArg (fun w : rootsOfUnity n K ↦ (((w : Kˣ) : K)))
      (image_root_eq_image_primitive_pow iota hk z)
  have hpowK : (ea.map fun e ↦ zeta_K ^ e).sum =
      (eb.map fun e ↦ zeta_K ^ e).sum := by
    rw [← haK, ← hbK]
    exact h
  have hpowk := multiset_sum_pow_eq_of_sum_pow_eq (NeZero.pos n) hk
    (image_primitive_isPrimitive iota hk) ea eb hpowK
  have hak :
      (a.map fun z ↦ (((z : rootsOfUnity n k) : kˣ) : k)).sum =
        (ea.map fun e ↦ zeta ^ e).sum := by
    congr 1
    simp only [ea, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z hz
    exact (pow_rootExponent hk z).symm
  have hbk :
      (b.map fun z ↦ (((z : rootsOfUnity n k) : kˣ) : k)).sum =
        (eb.map fun e ↦ zeta ^ e).sum := by
    congr 1
    simp only [eb, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z hz
    exact (pow_rootExponent hk z).symm
  rw [hak, hbk]
  exact hpowk

end RootSums

section AlgebraicallyClosedSource

variable {p n : ℕ} [CharP k p] [IsAlgClosed k]

/-- The root-sum reflection theorem in the form supplied by a coefficient
prime and an algebraically closed modular field. -/
theorem multiset_sum_coe_eq_of_image_sum_eq_isAlgClosed
    (hp : p.Prime) (hcop : n.Coprime p)
    (iota : rootsOfUnity n k ≃* rootsOfUnity n K)
    (a b : Multiset (rootsOfUnity n k))
    (h : (a.map fun z ↦ (((iota z : rootsOfUnity n K) : Kˣ) : K)).sum =
      (b.map fun z ↦ (((iota z : rootsOfUnity n K) : Kˣ) : K)).sum) :
    (a.map fun z ↦ (((z : rootsOfUnity n k) : kˣ) : k)).sum =
      (b.map fun z ↦ (((z : rootsOfUnity n k) : kˣ) : k)).sum := by
  have hnot : ¬p ∣ n := hp.coprime_iff_not_dvd.mp hcop.symm
  let _ : NeZero (n : k) := ⟨by
    intro hzero
    exact hnot ((CharP.cast_eq_zero_iff k p n).mp hzero)⟩
  let _ : NeZero n := NeZero.of_neZero_natCast k
  obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.prim (M := k) (n := n)
  exact multiset_sum_coe_eq_of_image_sum_eq iota hzeta a b h

end AlgebraicallyClosedSource

end ModularRep.CyclotomicRootSumReflection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
