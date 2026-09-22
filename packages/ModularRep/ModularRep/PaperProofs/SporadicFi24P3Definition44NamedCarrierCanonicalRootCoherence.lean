import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-! The canonical local reduction uses the restriction of the original
root convention. These are deductions about computed tables, with no
root-agreement source field. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [Group X] [Finite X]

private theorem root_eq_of_table_eq (i j : PrimeRegularRootEmbedding p k K X)
    (h : i.toMulEquiv = j.toMulEquiv) : i = j := by
  cases i
  cases j
  cases h
  rfl

private theorem restrict_table_cast {a b m : ℕ} (h : a = b)
    (table : rootsOfUnity m k ≃* rootsOfUnity m K) (ha : a ∣ m) (hb : b ∣ m) :
    Eq.ndrec (motive := fun n : ℕ => rootsOfUnity n k ≃* rootsOfUnity n K)
      (PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv ha table) h =
        PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv hb table := by
  subst b
  rfl

theorem ofPQuotient_quotientRoot (iota : PrimeRegularRootEmbedding p k K X)
    (R : Subgroup X) [R.Normal] (hR : IsPGroup p R) :
    PrimeRegularRootEmbeddingPQuotient.ofPQuotient R hR (quotientRoot iota R) = iota := by
  apply root_eq_of_table_eq
  change Eq.ndrec
    (motive := fun n : ℕ => rootsOfUnity n k ≃* rootsOfUnity n K)
    (PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv (quotientExponent_dvd R) iota.toMulEquiv)
    (PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq iota.prime R hR) = iota.toMulEquiv
  calc
    _ = PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv
        (dvd_refl (primeRegularExponent p X)) iota.toMulEquiv :=
      restrict_table_cast
        (PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq iota.prime R hR)
        iota.toMulEquiv (quotientExponent_dvd R) (dvd_refl _)
    _ = iota.toMulEquiv := by
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rfl

theorem ofCommonRoot_alongMulEquiv
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (hp : p.Prime) {m : ℕ}
    (table : rootsOfUnity m k ≃* rootsOfUnity m K)
    (hG : primeRegularExponent p G ∣ m) (hH : primeRegularExponent p H ∣ m)
    (e : G ≃* H) :
    (PrimeRegularRootEmbedding.ofCommonRoot hp table hG).alongMulEquiv e =
      PrimeRegularRootEmbedding.ofCommonRoot hp table hH := by
  apply root_eq_of_table_eq
  change Eq.ndrec
    (motive := fun n : ℕ => rootsOfUnity n k ≃* rootsOfUnity n K)
    (PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv hG table)
    (congrArg (fun n : ℕ => ordCompl[p] n) (Nat.card_congr e.toEquiv)) =
      PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv hH table
  exact restrict_table_cast _ table hG hH

variable [CharP k p] [IsAlgClosed k] [CharZero K] [Fintype X]

omit [CharP k p] [IsAlgClosed k] in
theorem normalizerRootAt_eq_subgroupRoot (iota : PrimeRegularRootEmbedding p k K X)
    (W : CharacterWeight p K X) :
    normalizerRootAt iota W = subgroupRoot iota (Subgroup.normalizer (W.subgroup : Set X)) :=
  ofPQuotient_quotientRoot (subgroupRoot iota (Subgroup.normalizer (W.subgroup : Set X)))
    (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set X)))
    W.radical.isPGroup.comap_subtype

theorem subgroupRoot_compatible (iota : PrimeRegularRootEmbedding p k K X) (N : Subgroup X)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k X V) :
    Representation.BrauerRootLiftCompatibleAlong rho iota (subgroupRoot iota N) N.subtype := by
  have hN : primeRegularExponent p N ∣ primeRegularExponent p X := by
    simpa only [primeRegularExponent] using
      Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card N) p
  simpa only [subgroupRoot, commonRoot_self] using
    Representation.brauerRootLiftCompatibleAlong_of_commonRoot rho N.subtype
      iota.prime iota.toMulEquiv (dvd_refl _) hN

theorem canonicalNormalizerRoot_compatible (iota : PrimeRegularRootEmbedding p k K X)
    (W : CharacterWeight p K X) (source : CanonicalRawReduction iota W)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k X V) :
    Representation.BrauerRootLiftCompatibleAlong rho iota source.normalizerRoot
      (Subgroup.normalizer (W.subgroup : Set X)).subtype := by
  rw [source.normalizerRoot_eq, normalizerRootAt_eq_subgroupRoot]
  exact subgroupRoot_compatible iota _ rho

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
