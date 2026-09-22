import ModularRep.RadicalSubgroup
import Mathlib.GroupTheory.Nilpotent

/-!
# Literal product coordinates for radical subgroups

A radical subgroup of a finite direct product equals the product of its
coordinate images. The proof uses the normalizer condition in a finite
p-group. The normalizer identification retains the original coordinates.
No character, block, or representation source occurs in these deductions.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRankThreeProductRadical

open ModularRep
open scoped BigOperators

universe u v

variable {C : Type u} (H : C → Type v) [∀ c, Group (H c)]

/-- Projection to the specified original factor. -/
def projection (c : C) : ((d : C) → H d) →* H c where
  toFun x := x c
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of a literal subgroup product is the specified subgroup. -/
theorem map_pi_projection (R : ∀ c, Subgroup (H c)) (c : C) :
    (Subgroup.pi Set.univ R).map (projection H c) = R c := by
  classical
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    change y c = x at hxy
    rw [← hxy]
    exact (Subgroup.mem_pi Set.univ).mp hy c (Set.mem_univ c)
  · intro hx
    apply Subgroup.mem_map.mpr
    refine ⟨Pi.mulSingle c x, ?_, ?_⟩
    · exact (Subgroup.mulSingle_mem_pi c x).mpr (fun _ => hx)
    · exact Pi.mulSingle_eq_same c x

/-- The normalizer of the product is the product of the actual normalizers. -/
theorem normalizer_pi (R : ∀ c, Subgroup (H c)) :
    Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c)) =
      Subgroup.pi Set.univ (fun c => Subgroup.normalizer (R c : Set (H c))) := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    apply (Subgroup.mem_pi Set.univ).mpr
    intro c _
    have hc := (Subgroup.le_normalizer_map
      (H := Subgroup.pi Set.univ R) (projection H c))
      (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [map_pi_projection H R c] at hc
    change g c ∈ Subgroup.normalizer (R c : Set (H c)) at hc
    exact hc
  · intro hg
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      apply (Subgroup.mem_pi Set.univ).mpr
      intro c hc
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.mem_pi Set.univ).mp hg c hc) (x c)).mp ((Subgroup.mem_pi Set.univ).mp hx c hc)
    · intro hx
      apply (Subgroup.mem_pi Set.univ).mpr
      intro c hc
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.mem_pi Set.univ).mp hg c hc) (x c)).mpr ((Subgroup.mem_pi Set.univ).mp hx c hc)

/-- The coordinate equivalence for the same normalizer subgroup. -/
def normalizerPiEquiv (R : ∀ c, Subgroup (H c)) :
    Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c)) ≃*
      ((c : C) → Subgroup.normalizer (R c : Set (H c))) where
  toFun n c := ⟨n.val c, by
    have hn : n.val ∈ Subgroup.pi Set.univ
        (fun d => Subgroup.normalizer (R d : Set (H d))) :=
      Eq.mp (congrArg (fun S : Subgroup ((d : C) → H d) => n.val ∈ S)
        (normalizer_pi H R)) n.property
    exact (Subgroup.mem_pi Set.univ).mp hn c (Set.mem_univ c)⟩
  invFun n := ⟨fun c => (n c).val, by
    rw [normalizer_pi H R]
    exact (Subgroup.mem_pi Set.univ).mpr (fun c _ => (n c).property)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext (fun _ => Subtype.ext rfl)
  map_mul' _ _ := rfl

@[simp] theorem normalizerPiEquiv_value (R : ∀ c, Subgroup (H c))
    (n : Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c)))
    (c : C) :
    (normalizerPiEquiv H R n c).val = n.val c := rfl

/-- The product of the literal projection images of a subgroup. -/
def coordinateHull (Q : Subgroup ((c : C) → H c)) : Subgroup ((c : C) → H c) :=
  Subgroup.pi Set.univ (fun c => Q.map (projection H c))

@[simp] theorem mem_coordinateHull (Q : Subgroup ((c : C) → H c))
    (x : (c : C) → H c) :
    x ∈ coordinateHull H Q ↔ ∀ c, x c ∈ Q.map (projection H c) := by
  simp only [coordinateHull, Subgroup.mem_pi, Set.mem_univ, forall_const]

theorem le_coordinateHull (Q : Subgroup ((c : C) → H c)) :
    Q ≤ coordinateHull H Q := by
  intro x hx
  apply (mem_coordinateHull H Q x).mpr
  intro c
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

/-- Every normalizing element normalizes the product of projection images. -/
theorem normalizer_le_coordinateHull_normalizer (Q : Subgroup ((c : C) → H c)) :
    Subgroup.normalizer (Q : Set ((c : C) → H c)) ≤
      Subgroup.normalizer (coordinateHull H Q : Set ((c : C) → H c)) := by
  intro g hg
  rw [coordinateHull, normalizer_pi H]
  apply (Subgroup.mem_pi Set.univ).mpr
  intro c _
  exact (Subgroup.le_normalizer_map (H := Q) (projection H c))
    (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

private theorem finitePi_isPGroup [Fintype C] {p : ℕ}
    (hH : ∀ c, IsPGroup p (H c)) : IsPGroup p ((c : C) → H c) := by
  classical
  intro x
  choose n hn using fun c => (hH c).exists_pow_pow_eq_one (x c)
  refine ⟨∑ c, n c, ?_⟩
  funext c
  change x c ^ p ^ (∑ d, n d) = 1
  apply orderOf_dvd_iff_pow_eq_one.mp
  apply (orderOf_dvd_iff_pow_eq_one.mpr (hn c)).trans
  exact Nat.pow_dvd_pow p
    (Finset.single_le_sum (fun d _ => Nat.zero_le (n d)) (Finset.mem_univ c))

/-- A finite coordinate hull of a p-subgroup is a p-group. -/
theorem coordinateHull_isPGroup [Fintype C] {p : ℕ}
    (Q : Subgroup ((c : C) → H c)) (hQ : IsPGroup p Q) :
    IsPGroup p (coordinateHull H Q) := by
  let f : coordinateHull H Q →* ((c : C) → Q.map (projection H c)) :=
    { toFun := fun x c => ⟨x.val c, (mem_coordinateHull H Q x.val).mp x.property c⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext c
    exact congrArg Subtype.val (congrFun hxy c)
  exact (finitePi_isPGroup (fun c => Q.map (projection H c))
    (fun c => hQ.map (projection H c))).of_injective f hf

section NormalizedOvergroup

variable {G : Type v} [Group G] [Finite G] {p : ℕ}

/-- A radical subgroup cannot have a larger p-overgroup normalized by its
own normalizer. -/
theorem radical_eq_of_normalized_pGroup (hp : p.Prime)
    {Q R : Subgroup G} (hQ : IsRadicalSubgroup p Q)
    (hQR : Q ≤ R) (hR : IsPGroup p R)
    (hnormalizes : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (R : Set G)) : Q = R := by
  let N := Subgroup.normalizer (Q : Set G)
  letI : (R.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormalizes
  have hcore : R.subgroupOf N ≤ pCore p N :=
    normal_pSubgroup_le_pCore p _ hR.comap_subtype
  have hintersection : N.subgroupOf R = Q.subgroupOf R := by
    apply Subgroup.ext
    intro x
    change x.val ∈ N ↔ x.val ∈ Q
    constructor
    · intro hx
      have hc : (⟨x.val, hx⟩ : N) ∈ pCore p N := hcore x.property
      rw [hQ.eq_normalizerPCore]
      exact Subgroup.mem_map.mpr ⟨⟨x.val, hx⟩, hc, rfl⟩
    · intro hx
      exact Q.le_normalizer hx
  have hself : Subgroup.normalizer (Q.subgroupOf R : Set R) = Q.subgroupOf R := by
    rw [← Subgroup.subgroupOf_normalizer_eq hQR]
    exact hintersection
  letI : Fact p.Prime := ⟨hp⟩
  letI : Group.IsNilpotent R := hR.isNilpotent
  have htop : Q.subgroupOf R = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := R))) (Q.subgroupOf R) hself
  exact le_antisymm hQR (Subgroup.subgroupOf_eq_top.mp htop)

end NormalizedOvergroup

/-- Every radical subgroup of a finite product splits by its original
coordinate projection images. -/
theorem radical_eq_coordinateHull [Fintype C] [∀ c, Finite (H c)]
    {p : ℕ} (hp : p.Prime) (Q : Subgroup ((c : C) → H c))
    (hQ : IsRadicalSubgroup p Q) : Q = coordinateHull H Q :=
  radical_eq_of_normalized_pGroup hp hQ (le_coordinateHull H Q)
    (coordinateHull_isPGroup H Q hQ.isPGroup)
    (normalizer_le_coordinateHull_normalizer H Q)

/-- Membership in a radical subgroup is equivalent to membership in each
of its actual projection images. -/
theorem radical_mem_iff [Fintype C] [∀ c, Finite (H c)]
    {p : ℕ} (hp : p.Prime) (Q : Subgroup ((c : C) → H c))
    (hQ : IsRadicalSubgroup p Q) (x : (c : C) → H c) :
    x ∈ Q ↔ ∀ c, x c ∈ Q.map (projection H c) := by
  conv_lhs => rw [radical_eq_coordinateHull H hp Q hQ]
  exact mem_coordinateHull H Q x

end ModularRep.PaperProofs.TypeBRankThreeProductRadical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
