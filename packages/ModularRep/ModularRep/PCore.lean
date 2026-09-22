import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The largest normal `p`-subgroup

This file constructs `O_p(G)` as the supremum of the normal `p`-subgroups of
`G`.  Mathlib supplies the Sylow-theoretic closure result needed to prove that
the supremum is again a `p`-group.
-/

namespace ModularRep

variable {G : Type*} [Group G]

/-- The `p`-core of a group: the largest normal `p`-subgroup. -/
def pCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  sSup {P : Subgroup G | IsPGroup p P ∧ P.Normal}

/-- The `p`-core is a `p`-group. -/
theorem pCore_isPGroup (p : ℕ) (G : Type*) [Group G] :
    IsPGroup p (pCore p G) := by
  apply Sylow.sSup_of_normal
  · intro P hP
    exact hP.1
  · intro P hP
    exact hP.2

/-- The `p`-core is normal. -/
theorem pCore_normal (p : ℕ) (G : Type*) [Group G] :
    (pCore p G).Normal := by
  apply Subgroup.sSup_normal
  intro P hP
  exact hP.2

instance pCore_normal_instance (p : ℕ) (G : Type*) [Group G] :
    (pCore p G).Normal :=
  pCore_normal p G

/-- Every normal `p`-subgroup is contained in the `p`-core. -/
theorem normal_pSubgroup_le_pCore (p : ℕ) (P : Subgroup G)
    (hP : IsPGroup p P) [P.Normal] : P ≤ pCore p G := by
  apply le_sSup
  exact ⟨hP, inferInstance⟩

/-- Triviality of the `p`-core is invariant under group equivalence. -/
theorem pCore_eq_bot_of_mulEquiv {H : Type*} [Group H]
    (p : ℕ) (e : G ≃* H) (hH : pCore p H = ⊥) :
    pCore p G = ⊥ := by
  have hmap_le : (pCore p G).map e.toMonoidHom ≤ pCore p H := by
    let _ : ((pCore p G).map e.toMonoidHom).Normal :=
      (pCore_normal p G).map e.toMonoidHom e.surjective
    exact normal_pSubgroup_le_pCore p _
      ((pCore_isPGroup p G).map e.toMonoidHom)
  have hmap_eq : (pCore p G).map e.toMonoidHom = ⊥ := by
    apply le_bot_iff.mp
    simpa only [hH] using hmap_le
  exact ((pCore p G).map_eq_bot_iff_of_injective e.injective).mp hmap_eq

/-- A simple group which is not a `p`-group has trivial `p`-core. -/
theorem pCore_eq_bot_of_isSimpleGroup_of_not_isPGroup
    (p : ℕ) [IsSimpleGroup G] (hG : ¬ IsPGroup p G) :
    pCore p G = ⊥ := by
  rcases (pCore_normal p G).eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · exfalso
    apply hG
    let e : pCore p G ≃* G :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    exact (pCore_isPGroup p G).of_equiv e

/-- If a distinct prime divides the order of a finite group, that group is
not a `p`-group. -/
theorem not_isPGroup_of_prime_dvd_card
    [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (hqG : q ∣ Nat.card G) :
    ¬ IsPGroup p G := by
  intro hG
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hcard⟩ := hG.exists_card_eq
  have hqpow : q ∣ p ^ n := by
    rw [← hcard]
    exact hqG
  apply hqp
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp
    (hq.dvd_of_dvd_pow hqpow)

/-- Restricting the quotient map by the `p`-core to a subgroup has kernel
the intersection with that `p`-core. -/
theorem ker_quotientMap_pCore_restrict {A : Type*} [Group A]
    (p : ℕ) (K : Subgroup A) :
    ((QuotientGroup.mk' (pCore p A)).comp K.subtype).ker =
      (pCore p A).comap K.subtype := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- If `A / O_p(A)` is cyclic, then the quotient of a subgroup by its
intersection with `O_p(A)` is cyclic. -/
theorem subgroup_quotient_inter_pCore_isCyclic
    {A : Type*} [Group A] (p : ℕ) [IsCyclic (A ⧸ pCore p A)]
    (K : Subgroup A) :
    IsCyclic (K ⧸ (pCore p A).comap K.subtype) := by
  let f : K →* A ⧸ pCore p A :=
    (QuotientGroup.mk' (pCore p A)).comp K.subtype
  have hker : f.ker = (pCore p A).comap K.subtype := by
    simpa [f] using ker_quotientMap_pCore_restrict p K
  have hcyclic : IsCyclic (K ⧸ f.ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift f)
      (QuotientGroup.kerLift_injective f)
  exact (QuotientGroup.quotientMulEquivOfEq hker).isCyclic.mp hcyclic

/-- The `p`-hypoelementary condition is inherited by subgroups: if
`A / O_p(A)` is cyclic, then `K / O_p(K)` is cyclic for every `K ≤ A`. -/
theorem subgroup_quotient_pCore_isCyclic
    {A : Type*} [Group A] (p : ℕ) [IsCyclic (A ⧸ pCore p A)]
    (K : Subgroup A) : IsCyclic (K ⧸ pCore p K) := by
  let I : Subgroup K := (pCore p A).comap K.subtype
  have hI : I ≤ pCore p K := by
    apply normal_pSubgroup_le_pCore
    exact (pCore_isPGroup p A).comap_subtype
  let hIQ : I ≤ (pCore p K).comap (MonoidHom.id K) := by
    simpa using hI
  let f : K ⧸ I →* K ⧸ pCore p K :=
    QuotientGroup.map I (pCore p K) (MonoidHom.id K) hIQ
  let _ : IsCyclic (K ⧸ I) := by
    simpa [I] using subgroup_quotient_inter_pCore_isCyclic p K
  apply isCyclic_of_surjective f
  apply QuotientGroup.map_surjective_of_surjective I (pCore p K)
    (MonoidHom.id K)
  simpa using QuotientGroup.mk'_surjective (pCore p K)

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
