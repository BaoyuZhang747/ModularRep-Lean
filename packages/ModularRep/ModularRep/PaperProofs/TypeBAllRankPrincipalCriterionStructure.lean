import ModularRep.PaperProofs.TypeBIndexTwoAmbientCommutator

/-!
# Outer commutativity for the principal criterion

The actual index-two quotient and the abelian field group kill the two
coordinates of every ambient commutator. The natural action then sends
that commutator to an inner automorphism of the original base group.
Thus the full outer group is abelian once this same action is surjective.
-/

noncomputable section
set_option autoImplicit false

open scoped commutatorElement

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionStructure

open TypeBCriterionHypotheses TypeBIndexTwoAmbientCommutator

variable {M E : Type} [Group M] [Group E] [IsMulCommutative E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field) (indexTwo : G.index = 2)

include action indexTwo in
/-- Both actual quotient coordinates of an ambient commutator vanish. -/
theorem ambient_commutator_mem (a b : Ambient field) :
    ⁅a, b⁆ ∈ embeddedG G field := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclic (M ⧸ G) :=
    isCyclic_of_prime_card (G.index_eq_card.symm.trans indexTwo)
  have right_mem : ⁅a, b⁆ ∈ (SemidirectProduct.rightHom (φ := field)).ker := by
    change SemidirectProduct.rightHom ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have left_mem : ⁅a, b⁆ ∈ embeddedM field := by
    change ⁅a, b⁆ ∈ (SemidirectProduct.inl (φ := field)).range
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact right_mem
  obtain ⟨m, hm⟩ := left_mem
  have projected : ambientQuotient G field action indexTwo ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have hmG : m ∈ G := by
    apply (QuotientGroup.eq_one_iff m).mp
    change QuotientGroup.mk' G m = 1
    rw [← hm, ambientQuotient_inl] at projected
    exact projected
  exact ⟨⟨m, hmG⟩, hm⟩

include indexTwo in
/-- Surjectivity of the prescribed natural action suffices; no separate
outer-group commutativity source is needed. -/
theorem outer_abelian
    (surjective : Function.Surjective action.hom) :
    IsMulCommutative (OuterAutomorphism G) := by
  apply IsMulCommutative.of_comm
  intro x y
  obtain ⟨alpha, rfl⟩ := QuotientGroup.mk'_surjective (innerAutomorphisms G) x
  obtain ⟨beta, rfl⟩ := QuotientGroup.mk'_surjective (innerAutomorphisms G) y
  obtain ⟨a, rfl⟩ := surjective alpha
  obtain ⟨b, rfl⟩ := surjective beta
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement, ← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff (action.hom ⁅a, b⁆)).mpr
  obtain ⟨g, hg⟩ := ambient_commutator_mem G field action indexTwo a b
  have base_action : action.hom (baseEmbedding G field g) = MulAut.conj g := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [action.value]
    simp [baseEmbedding, MulAut.conj_apply]
  rw [← hg, base_action]
  exact ⟨g, rfl⟩

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionStructure


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
