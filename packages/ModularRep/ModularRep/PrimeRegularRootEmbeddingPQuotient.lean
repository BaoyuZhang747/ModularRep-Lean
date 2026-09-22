import ModularRep.BrauerCharacterCommonRootCompatibility
import Mathlib.GroupTheory.PGroup

/-!
# Root lifts across a normal p-subgroup

A normal p-subgroup does not change the prime-to-p part of the group order.
Consequently a prescribed quotient root embedding gives an ambient embedding
with the identical field-level lift. No new existence or root-agreement
assumption is introduced.
-/

noncomputable section

namespace ModularRep.PrimeRegularRootEmbeddingPQuotient

universe u v w x

private noncomputable def liftForExponent
    {k : Type u} {K : Type v} [Field k] [Field K]
    (n : Nat) (e : rootsOfUnity n k ≃* rootsOfUnity n K) : k → K :=
  Function.extend
    (fun zeta : rootsOfUnity n k ↦ (((zeta : kˣ) : k)))
    (fun zeta ↦ (((e zeta : rootsOfUnity n K) : Kˣ) : K))
    (fun _ ↦ 0)

private theorem liftForExponent_transport
    {k : Type u} {K : Type v} [Field k] [Field K]
    {m n : Nat} (h : m = n)
    (e : rootsOfUnity m k ≃* rootsOfUnity m K) :
    liftForExponent n (h ▸ e) = liftForExponent m e := by
  subst n
  rfl

/-- Reuse the root correspondence when the two required exponents agree. -/
def transport
    {p : Nat} {k : Type u} {K : Type v} {G : Type w} {H : Type x}
    [Field k] [Field K] [Group G] [Finite G] [Group H] [Finite H]
    (iota : PrimeRegularRootEmbedding p k K G)
    (h : primeRegularExponent p G = primeRegularExponent p H) :
    PrimeRegularRootEmbedding p k K H where
  prime := iota.prime
  toMulEquiv := h ▸ iota.toMulEquiv

theorem transport_lift
    {p : Nat} {k : Type u} {K : Type v} {G : Type w} {H : Type x}
    [Field k] [Field K] [Group G] [Finite G] [Group H] [Finite H]
    (iota : PrimeRegularRootEmbedding p k K G)
    (h : primeRegularExponent p G = primeRegularExponent p H) (z : k) :
    (transport iota h).lift z = iota.lift z := by
  change liftForExponent (primeRegularExponent p H)
      (h ▸ iota.toMulEquiv) z =
    liftForExponent (primeRegularExponent p G) iota.toMulEquiv z
  exact congrFun (liftForExponent_transport h iota.toMulEquiv) z

/-- This is just the cardinality formula and the prime-to-p part of p^a. -/
theorem exponent_quotient_eq
    {p : Nat} {G : Type w} [Group G] [Finite G]
    (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) :
    primeRegularExponent p (G ⧸ N) = primeRegularExponent p G := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hN.exists_card_eq
  change ordCompl[p] (Nat.card (G ⧸ N)) = ordCompl[p] (Nat.card G)
  rw [N.card_eq_card_quotient_mul_card_subgroup, Nat.ordCompl_mul,
    ha, Nat.ordCompl_self_pow hp, mul_one]

/-- Inflate the prescribed quotient root convention, keeping its lift. -/
def ofPQuotient
    {p : Nat} {k : Type u} {K : Type v} {G : Type w}
    [Field k] [Field K] [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (iota : PrimeRegularRootEmbedding p k K (G ⧸ N)) :
    PrimeRegularRootEmbedding p k K G :=
  transport iota (exponent_quotient_eq iota.prime N hN)

theorem ofPQuotient_lift
    {p : Nat} {k : Type u} {K : Type v} {G : Type w}
    [Field k] [Field K] [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (iota : PrimeRegularRootEmbedding p k K (G ⧸ N)) (z : k) :
    (ofPQuotient N hN iota).lift z = iota.lift z :=
  transport_lift iota (exponent_quotient_eq iota.prime N hN) z

end ModularRep.PrimeRegularRootEmbeddingPQuotient



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
