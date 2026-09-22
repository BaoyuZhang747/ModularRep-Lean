import ModularRep.PaperProofs.TypeBSpinDiagonalFieldQuotient
import ModularRep.PaperProofs.TypeBGlobalExtensionBinding
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!+# Index-two base quotients and actual ambient inertias

The natural action preserves the actual normal subgroup. Every induced
automorphism of its order-two quotient is the identity. This controls the
commutators with the canonical left factor of the semidirect product.

Consequently that left factor normalizes every subgroup containing the
embedded base. Actual Brauer inertias therefore agree at all left-factor
conjugates, with the existing inverse right-twist convention. No field
fixation or commutativity of the field actor is assumed.
-/

noncomputable section
set_option autoImplicit false

open scoped commutatorElement

namespace ModularRep.PaperProofs.TypeBIndexTwoAmbientCommutator

open ModularRep TypeBCriterionHypotheses

section Groups

variable {M E : Type} [Group M] [Group E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

include action

/-- The literal natural action proves preservation of the same subgroup. -/
theorem field_map (e : E) : G.map (field e).toMonoidHom = G := by
  have preserves (d : E) (g : G) : field d g.1 ∈ G := by
    have value : (action.hom (SemidirectProduct.inr d) g : M) = field d g.1 := by
      simpa using action.value (SemidirectProduct.inr d) g
    exact value ▸ (action.hom (SemidirectProduct.inr d) g).property
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact preserves e ⟨g, hg⟩
  · intro g hg
    refine ⟨field e⁻¹ g, preserves e⁻¹ ⟨g, hg⟩, ?_⟩
    rw [map_inv]
    exact (field e).apply_symm_apply g

/-- Descent of the given field automorphism to the actual quotient. -/
def quotientFieldAutomorphism (e : E) : MulAut (M ⧸ G) :=
  QuotientGroup.congr G G (field e) (field_map G field action e)

/-- A group of order two has no nonidentity automorphism. -/
theorem quotientFieldAutomorphism_eq_one (indexTwo : G.index = 2) (e : E) :
    quotientFieldAutomorphism G field action e = 1 :=
  TypeBSpinDiagonalFieldQuotient.mulAut_eq_one_of_card_two
    (G.index_eq_card.symm.trans indexTwo) (quotientFieldAutomorphism G field action e)

/-- The original element and its actual field transform have the same coset. -/
theorem projection_field (indexTwo : G.index = 2) (e : E) (m : M) :
    QuotientGroup.mk' G (field e m) = QuotientGroup.mk' G m := by
  calc
    QuotientGroup.mk' G (field e m) =
        quotientFieldAutomorphism G field action e (QuotientGroup.mk' G m) := rfl
    _ = QuotientGroup.mk' G m := by
      rw [quotientFieldAutomorphism_eq_one G field action indexTwo e]
      rfl

/-- The actual quotient of the left coordinate, using derived invariance. -/
def ambientQuotient (indexTwo : G.index = 2) : Ambient field →* M ⧸ G where
  toFun a := QuotientGroup.mk' G a.left
  map_one' := map_one (QuotientGroup.mk' G)
  map_mul' a b := by
    change QuotientGroup.mk' G (a.left * field a.right b.left) =
      QuotientGroup.mk' G a.left * QuotientGroup.mk' G b.left
    rw [map_mul, projection_field G field action indexTwo]

@[simp]
theorem ambientQuotient_inl (indexTwo : G.index = 2) (m : M) :
    ambientQuotient G field action indexTwo (SemidirectProduct.inl m) =
      QuotientGroup.mk' G m := rfl

/-- Every commutator with the actual left factor belongs to the embedded base. -/
theorem commutator_inl_mem (indexTwo : G.index = 2)
    (a : Ambient field) (m : M) :
    ⁅a, SemidirectProduct.inl (φ := field) m⁆ ∈ embeddedG G field := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclic (M ⧸ G) :=
    isCyclic_of_prime_card (G.index_eq_card.symm.trans indexTwo)
  have right_mem :
      ⁅a, SemidirectProduct.inl (φ := field) m⁆ ∈
        (SemidirectProduct.rightHom (φ := field)).ker := by
    change SemidirectProduct.rightHom ⁅a, SemidirectProduct.inl (φ := field) m⁆ = 1
    rw [map_commutatorElement]
    simp only [SemidirectProduct.rightHom_inl, commutatorElement_one_right]
  have left_mem :
      ⁅a, SemidirectProduct.inl (φ := field) m⁆ ∈ embeddedM field := by
    change _ ∈ (SemidirectProduct.inl (φ := field)).range
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact right_mem
  obtain ⟨t, ht⟩ := left_mem
  have projected : ambientQuotient G field action indexTwo
      ⁅a, SemidirectProduct.inl (φ := field) m⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have htG : t ∈ G := by
    apply (QuotientGroup.eq_one_iff t).mp
    change QuotientGroup.mk' G t = 1
    rw [← ht, ambientQuotient_inl] at projected
    exact projected
  exact ⟨⟨t, htG⟩, ht⟩

/-- The bound concerns the actual ambient group and its canonical left image. -/
theorem commutator_embeddedM_le (indexTwo : G.index = 2) :
    ⁅(⊤ : Subgroup (Ambient field)), embeddedM field⁆ ≤ embeddedG G field := by
  apply Subgroup.commutator_le.mpr
  intro a _ m hm
  obtain ⟨t, rfl⟩ := hm
  exact commutator_inl_mem G field action indexTwo a t

/-- The relative commutator is in both the inertia and the left factor. -/
theorem commutator_le_intersection (indexTwo : G.index = 2)
    (I : Subgroup (Ambient field)) (base_le : embeddedG G field ≤ I) :
    ⁅I, embeddedM field⁆ ≤ I ⊓ embeddedM field := by
  have bound : ⁅I, embeddedM field⁆ ≤ embeddedG G field :=
    (Subgroup.commutator_mono le_top le_rfl).trans
      (commutator_embeddedM_le G field action indexTwo)
  apply bound.trans
  apply le_inf base_le
  rintro _ ⟨g, rfl⟩
  exact ⟨g.1, rfl⟩

/-- The entire left factor normalizes every subgroup containing the base. -/
theorem embeddedM_le_normalizer (indexTwo : G.index = 2)
    (I : Subgroup (Ambient field)) (base_le : embeddedG G field ≤ I) :
    embeddedM field ≤ Subgroup.normalizer (I : Set (Ambient field)) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mpr
    ((commutator_le_intersection G field action indexTwo I base_le).trans inf_le_left)

/-- The same given action has equal stabilizers at every left-factor conjugate. -/
theorem stabilizer_inl_eq (indexTwo : G.index = 2)
    {X : Type} [MulAction (Ambient field) X] (x : X)
    (base_le : embeddedG G field ≤ MulAction.stabilizer (Ambient field) x) (m : M) :
    MulAction.stabilizer (Ambient field) (SemidirectProduct.inl (φ := field) m • x) =
      MulAction.stabilizer (Ambient field) x := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (embeddedM_le_normalizer G field action indexTwo _ base_le ⟨m, rfl⟩)

/-- The natural action restricts to literal conjugation on the whole left factor. -/
theorem naturalAction_inl (m : M) :
    action.hom (SemidirectProduct.inl (φ := field) m) =
      MulAut.conjNormal (H := G) m := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  change (action.hom (SemidirectProduct.inl (φ := field) m) g : M) =
    m * (g : M) * m⁻¹
  simpa only [SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    map_one, MulAut.one_apply] using action.value (SemidirectProduct.inl m) g

end Groups

section Brauer

variable {ell : ℕ} {k K M E : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field) (indexTwo : G.index = 2)
variable (iota : PrimeRegularRootEmbedding ell k K G)

include indexTwo

/-- The common-inertia commutator bound for each actual Brauer character. -/
theorem brauerInertia_commutator_le (phi : IBr iota) :
    ⁅brauerInertia G field action iota phi, embeddedM field⁆ ≤
      brauerInertia G field action iota phi ⊓ embeddedM field :=
  commutator_le_intersection G field action indexTwo _
    (TypeBGlobalExtensionBinding.base_le_brauerInertia G field action iota phi)

/-- All literal left-factor conjugates have the same full ambient inertia.
The inverse conjugation is exactly the existing right-action convention. -/
theorem brauerInertia_conjugate_eq (phi : IBr iota) (m : M) :
    brauerInertia G field action iota
        (IrreducibleBrauerCharacter.twist iota phi (MulAut.conjNormal (H := G) m⁻¹)) =
      brauerInertia G field action iota phi := by
  letI : MulAction (Ambient field) (IBr iota) :=
    CyclicOuterLemma37Concrete.rightAutomorphismAction action.hom
  have equality := stabilizer_inl_eq G field action indexTwo phi
    (TypeBGlobalExtensionBinding.base_le_brauerInertia G field action iota phi) m
  change brauerInertia G field action iota
    (IrreducibleBrauerCharacter.twist iota phi
      (action.hom ((SemidirectProduct.inl (φ := field) m)⁻¹))) = _ at equality
  rw [← map_inv, naturalAction_inl G field action] at equality
  exact equality

end Brauer

end ModularRep.PaperProofs.TypeBIndexTwoAmbientCommutator


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
