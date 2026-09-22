import ModularRep.PaperProofs.TypeBRankThreeProductWeightCoordinates
import ModularRep.PaperProofs.OddTwoWeightGroupEquiv

/-!
# Conjugacy classes of literal product weights

Inner conjugation acts in the original product coordinates. The ordinary
character values and the raw inverse laws therefore identify the actual
conjugacy relation with coordinatewise conjugacy. The resulting equivalence
uses only the same uniform ordinary quotient source as the raw coordinates.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs.TypeBRankThreeProductWeightConjugacy

open ModularRep CharacterWeight
open TypeBRankThreeProductRadical TypeBRankThreeProductRadicalQuotient
open TypeBRankThreeProductOrdinarySource TypeBRankThreeProductRawWeight
open TypeBRankThreeProductWeightCoordinates

universe u

section Classes

variable {p : ℕ} {K G : Type u} [Field K] [CharZero K]
variable [Group G] [Finite G]

/-- The existing two quotient projections on a raw character weight. -/
def rawClass (W : CharacterWeight p K G) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) :=
  Quotient.mk'' (Quotient.mk'' W)

private theorem map_conj_eq_rightTwist (W : CharacterWeight p K G) (g : G) :
    W.mapGroupEquiv (MulAut.conj g) = W.rightTwist (MulAut.conj g⁻¹) := by
  have inverse : (MulAut.conj g⁻¹).symm = MulAut.conj g := by
    apply MulEquiv.ext
    intro x
    simp only [MulAut.conj_symm_apply, inv_inv, MulAut.conj_apply]
  rw [← inverse]
  exact mapGroupEquiv_mulAut_symm W (MulAut.conj g⁻¹)

/-- Actual ambient conjugation does not change the existing class. -/
theorem rawClass_map_conj (W : CharacterWeight p K G) (g : G) :
    rawClass (W.mapGroupEquiv (MulAut.conj g)) = rawClass W := by
  apply Quotient.sound
  refine ⟨g, ?_⟩
  change (Quotient.mk'' (W.rightTwist (MulAut.conj g⁻¹)) :
    CharacterWeight.IsoClass (p := p) (K := K) (G := G)) =
      Quotient.mk'' (W.mapGroupEquiv (MulAut.conj g))
  exact congrArg Quotient.mk'' (map_conj_eq_rightTwist W g).symm

/-- Equality in the two actual quotients is raw equality after an inner map. -/
theorem rawClass_eq_iff (W V : CharacterWeight p K G) :
    rawClass W = rawClass V ↔ ∃ g : G, W = V.mapGroupEquiv (MulAut.conj g) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    change (Quotient.mk'' (V.rightTwist (MulAut.conj g⁻¹)) :
      CharacterWeight.IsoClass (p := p) (K := K) (G := G)) = Quotient.mk'' W at hg
    have equality : V.rightTwist (MulAut.conj g⁻¹) = W :=
      CharacterWeight.eq_of_isomorphic (Quotient.exact hg)
    exact ⟨g, equality.symm.trans (map_conj_eq_rightTwist V g).symm⟩
  · rintro ⟨g, rfl⟩
    exact rawClass_map_conj V g

/-- Every existing conjugacy class has a raw representative. -/
theorem rawClass_surjective : Function.Surjective (rawClass (p := p) (K := K) (G := G)) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro w
  refine Quotient.inductionOn w ?_
  intro W
  exact ⟨W, rfl⟩

/-- A choice is used only to present the already defined quotient. -/
def rawRepresentative
    (c : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    CharacterWeight p K G :=
  Classical.choose (rawClass_surjective c)

@[simp] theorem rawClass_representative
    (c : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    rawClass (rawRepresentative c) = c :=
  Classical.choose_spec (rawClass_surjective c)

end Classes

variable {I K : Type u} (H : I → Type u) [Fintype I]
variable [∀ i, Group (H i)] [∀ i, Finite (H i)]
variable [Field K] [CharZero K]
variable [HasEnoughRootsOfUnity K (Nat.card (∀ i, H i))]
variable {p : ℕ} (hp : Nat.Prime p)
variable (ordinary : ∀ Q : ∀ i, Subgroup (H i),
  ExternalProductSource (fun i => NormalizerQuotient (Q i)) p hp
    (quotientProductRoots (K := K) H Q))

/-- The image of the actual subgroup product is the product of the inner images. -/
theorem pi_map_conjugation (Q : ∀ i, Subgroup (H i)) (g : ∀ i, H i) :
    Subgroup.pi Set.univ (fun i => (Q i).map (MulAut.conj (g i)).toMonoidHom) =
      (Subgroup.pi Set.univ Q).map (MulAut.conj g).toMonoidHom := by
  apply Subgroup.ext
  intro x
  simp only [Subgroup.mem_pi, Set.mem_univ, forall_const, Subgroup.mem_map_equiv,
    MulAut.conj_symm_apply, Pi.mul_apply, Pi.inv_apply]

/-- The same normalizer map conjugates each original coordinate. -/
def conjugationNormalizer (Q : ∀ i, Subgroup (H i)) (g : ∀ i, H i) :
    Subgroup.normalizer (Subgroup.pi Set.univ Q : Set (∀ i, H i)) ≃*
      Subgroup.normalizer
        (Subgroup.pi Set.univ
          (fun i => (Q i).map (MulAut.conj (g i)).toMonoidHom) : Set (∀ i, H i)) :=
  (normalizerPiEquiv H Q).trans
    ((MulEquiv.piCongrRight (fun i => normalizerEquiv (MulAut.conj (g i)) (Q i))).trans
      (normalizerPiEquiv H
        (fun i => (Q i).map (MulAut.conj (g i)).toMonoidHom)).symm)

@[simp] theorem conjugationNormalizer_value (Q : ∀ i, Subgroup (H i)) (g : ∀ i, H i)
    (n : Subgroup.normalizer (Subgroup.pi Set.univ Q : Set (∀ i, H i))) :
    (conjugationNormalizer H Q g n).val = MulAut.conj g n.val := by
  funext i
  rfl

/-- The raw product commutes with the actual coordinate inner maps. -/
theorem rawProduct_map_conjugation (W : ∀ i, CharacterWeight p K (H i))
    (g : ∀ i, H i) :
    (rawProductMap H hp ordinary W).mapGroupEquiv (MulAut.conj g) =
      rawProductMap H hp ordinary (fun i => (W i).mapGroupEquiv (MulAut.conj (g i))) := by
  apply mapGroupEquiv_eq_of_normalizer_coordinates
    (rawProductMap H hp ordinary W) (MulAut.conj g)
    (rawProductMap H hp ordinary (fun i => (W i).mapGroupEquiv (MulAut.conj (g i))))
    (pi_map_conjugation H (fun i => (W i).subgroup) g)
    (conjugationNormalizer H (fun i => (W i).subgroup) g)
  · intro n
    exact conjugationNormalizer_value H (fun i => (W i).subgroup) g n
  · intro n
    simp only [rawProductMap, rawProduct_localCharacter_mk]
    change (∏ i, ((W i).mapGroupEquiv (MulAut.conj (g i))).localCharacter
      (QuotientGroup.mk (normalizerEquiv (MulAut.conj (g i)) (W i).subgroup
        (normalizerPiEquiv H (fun j => (W j).subgroup) n i)))) =
      ∏ i, (W i).localCharacter
        (QuotientGroup.mk (normalizerPiEquiv H (fun j => (W j).subgroup) n i))
    apply Finset.prod_congr rfl
    intro i _
    exact mapGroupEquiv_normalizer_values (W i) (MulAut.conj (g i))
      (normalizerPiEquiv H (fun j => (W j).subgroup) n i)

/-- Product conjugacy is exactly coordinatewise conjugacy of the original weights. -/
theorem rawProduct_class_eq_iff (W V : ∀ i, CharacterWeight p K (H i)) :
    rawClass (rawProductMap H hp ordinary W) = rawClass (rawProductMap H hp ordinary V) ↔
      ∀ i, rawClass (W i) = rawClass (V i) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (rawClass_eq_iff _ _).mp h
    have coordinates : W = fun i => (V i).mapGroupEquiv (MulAut.conj (g i)) :=
      rawProduct_injective H hp ordinary
        (hg.trans (rawProduct_map_conjugation H hp ordinary V g))
    intro i
    rw [congrFun coordinates i]
    exact rawClass_map_conj (V i) (g i)
  · intro h
    choose g hg using fun i => (rawClass_eq_iff (W i) (V i)).mp (h i)
    have coordinates : W = fun i => (V i).mapGroupEquiv (MulAut.conj (g i)) :=
      funext hg
    apply (rawClass_eq_iff _ _).mpr
    refine ⟨g, ?_⟩
    rw [coordinates]
    exact (rawProduct_map_conjugation H hp ordinary V g).symm

/-- The quotient map is constructed from raw representatives and their literal product. -/
def classProductMap
    (w : ∀ i, CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H i)) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := ∀ i, H i) :=
  rawClass (rawProductMap H hp ordinary (fun i => rawRepresentative (w i)))

/-- The map on classes is independent of all representative choices. -/
theorem classProductMap_apply (W : ∀ i, CharacterWeight p K (H i)) :
    classProductMap H hp ordinary (fun i => rawClass (W i)) =
      rawClass (rawProductMap H hp ordinary W) := by
  apply (rawProduct_class_eq_iff H hp ordinary _ _).mpr
  intro i
  exact rawClass_representative (rawClass (W i))

theorem classProductMap_injective : Function.Injective (classProductMap H hp ordinary) := by
  intro w v h
  have coordinates := (rawProduct_class_eq_iff H hp ordinary _ _).mp h
  funext i
  exact (rawClass_representative (w i)).symm.trans
    ((coordinates i).trans (rawClass_representative (v i)))

theorem classProductMap_surjective : Function.Surjective (classProductMap H hp ordinary) := by
  intro c
  obtain ⟨W, rfl⟩ := rawClass_surjective c
  refine ⟨fun i => rawClass (rawCoordinates H hp ordinary W i), ?_⟩
  rw [classProductMap_apply, rawProduct_coordinates]

/-- Actual conjugacy classes are equivalent to the product of the actual factor classes. -/
def classProductEquiv :
    (∀ i, CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H i)) ≃
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := ∀ i, H i) :=
  Equiv.ofBijective (classProductMap H hp ordinary)
    ⟨classProductMap_injective H hp ordinary, classProductMap_surjective H hp ordinary⟩

@[simp] theorem classProductEquiv_apply (W : ∀ i, CharacterWeight p K (H i)) :
    classProductEquiv H hp ordinary (fun i => rawClass (W i)) =
      rawClass (rawProductMap H hp ordinary W) :=
  classProductMap_apply H hp ordinary W

/-- The inverse is the class of each intrinsic raw coordinate. -/
theorem classProductEquiv_symm_apply (W : CharacterWeight p K (∀ i, H i)) :
    (classProductEquiv H hp ordinary).symm (rawClass W) =
      fun i => rawClass (rawCoordinates H hp ordinary W i) := by
  apply (classProductEquiv H hp ordinary).injective
  rw [Equiv.apply_symm_apply, classProductEquiv_apply, rawProduct_coordinates]

end ModularRep.PaperProofs.TypeBRankThreeProductWeightConjugacy


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
