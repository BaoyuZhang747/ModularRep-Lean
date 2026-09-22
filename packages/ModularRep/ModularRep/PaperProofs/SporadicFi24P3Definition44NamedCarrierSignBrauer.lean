import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNegatedCharpoly

/-! The actual quotient-sign twist has the expected Brauer character.
Only roots of unity are lifted multiplicatively; the total lift is never
treated as additive. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignBrauer

open SporadicFi24P3Definition44NamedCarrierQuotientSignAlgebra
open SporadicFi24P3Definition44NamedCarrierNegatedCharpoly

def quotientSignCharacter
    {K G : Type*} [Field K] [Group G]
    (N : Subgroup G) [N.Normal] (hindex : N.index = 2) :
    (G ⧸ N) →* Kˣ :=
  QuotientGroup.lift N (quotientSign (k := K) N hindex) (by
    intro g hg
    exact quotientSign_mem N hindex g hg)

@[simp] theorem quotientSignCharacter_mk
    {K G : Type*} [Field K] [Group G]
    (N : Subgroup G) [N.Normal] (hindex : N.index = 2) (g : G) :
    quotientSignCharacter (K := K) N hindex (QuotientGroup.mk' N g) =
      quotientSign (k := K) N hindex g := rfl

theorem liftRoot_neg_one
    {p : ℕ} {k K G : Type*} [Field k] [Field K] [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) (h2 : (2 : k) ≠ 0)
    (z : rootsOfUnity (primeRegularExponent p G) k)
    (hz : ((z : kˣ) : k) = -1) : iota.liftRoot z = -1 := by
  have hzsq : z ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change ((z : kˣ) : k) ^ 2 = 1
    rw [hz]
    ring
  have himage : iota.toMulEquiv z ^ 2 = 1 := by
    rw [← map_pow, hzsq, map_one]
  have hs : iota.liftRoot z ^ 2 = 1 :=
    congrArg (fun w : rootsOfUnity (primeRegularExponent p G) K => ((w : Kˣ) : K)) himage
  rcases sq_eq_one_iff.mp hs with h | h
  · have he : iota.toMulEquiv z = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact h
    have hz1 : z = 1 := iota.toMulEquiv.injective (he.trans (map_one _).symm)
    have hn : (-1 : k) = 1 := hz.symm.trans
      (congrArg (fun w : rootsOfUnity (primeRegularExponent p G) k => ((w : kˣ) : k)) hz1)
    exfalso
    apply h2
    calc
      (2 : k) = 1 - (-1) := by ring
      _ = 0 := by rw [hn]; ring
  · exact h

theorem lift_neg_of_roots
    {p : ℕ} {k K G : Type*} [Field k] [Field K] [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) (h2 : (2 : k) ≠ 0)
    (zminus z : rootsOfUnity (primeRegularExponent p G) k)
    (hminus : ((zminus : kˣ) : k) = -1) :
    iota.lift (-((z : kˣ) : k)) = -iota.lift ((z : kˣ) : k) := by
  have hmul : (((zminus * z : rootsOfUnity (primeRegularExponent p G) k) : kˣ) : k) =
      -((z : kˣ) : k) := by
    change ((zminus : kˣ) : k) * ((z : kˣ) : k) = _
    rw [hminus, neg_one_mul]
  rw [← hmul, iota.lift_coe, iota.lift_coe]
  change (((iota.toMulEquiv (zminus * z) : rootsOfUnity (primeRegularExponent p G) K) : Kˣ) : K) = _
  rw [map_mul]
  change iota.liftRoot zminus * iota.liftRoot z = _
  rw [liftRoot_neg_one iota h2 zminus hminus, neg_one_mul]

theorem brauerCharacter_sign_twist
    {p : ℕ} {k K G V : Type*}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (iota : PrimeRegularRootEmbedding p k K G) (h2 : (2 : k) ≠ 0)
    (N : Subgroup G) (hindex : N.index = 2)
    (rho : Representation k G V) (g : PrimeRegularElement (G := G) p) :
    (rho.linearCharacterTwist (quotientSign (k := k) N hindex)).brauerCharacterOfRootEmbedding iota g =
      (quotientSign (k := K) N hindex g.val : K) * rho.brauerCharacterOfRootEmbedding iota g := by
  classical
  rw [Representation.brauerCharacterOfRootEmbedding_apply,
    Representation.brauerCharacterOfRootEmbedding_apply]
  change (((((quotientSign (k := k) N hindex g.val : k) • rho g.val).charpoly.roots).map
    iota.lift).sum) = _
  by_cases hg : g.val ∈ N
  · simp only [quotientSign_mem N hindex g.val hg,
      Units.val_one, one_smul, one_mul]
  · have hp : (-1 : k) ^ primeRegularExponent p G = 1 := by
      have hm := congrArg (fun x : G => (quotientSign (k := k) N hindex x : k))
        (g.pow_primeRegularExponent_eq_one iota.prime)
      simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one,
        quotientSign_not_mem N hindex g.val hg, Units.val_neg] using hm
    let : NeZero (primeRegularExponent p G) := ⟨(primeRegularExponent_pos p G).ne'⟩
    let zminus : rootsOfUnity (primeRegularExponent p G) k := rootsOfUnity.mkOfPowEq (-1) hp
    have hlift : ∀ a ∈ (rho g.val).charpoly.roots, iota.lift (-a) = -iota.lift a := by
      intro a ha
      exact lift_neg_of_roots iota h2 zminus (rho.charpolyRootAsRootOfUnity iota g ⟨a, ha⟩) rfl
    simp only [quotientSign_not_mem N hindex g.val hg,
      Units.val_neg, Units.val_one, neg_one_smul, neg_one_mul]
    rw [roots_charpoly_neg, Multiset.map_map]
    calc
      _ = ((rho g.val).charpoly.roots.map (fun a => -iota.lift a)).sum := by
        congr 1
        apply Multiset.map_congr rfl
        exact hlift
      _ = -((rho g.val).charpoly.roots.map iota.lift).sum := by
        exact Multiset.sum_map_neg

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignBrauer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
