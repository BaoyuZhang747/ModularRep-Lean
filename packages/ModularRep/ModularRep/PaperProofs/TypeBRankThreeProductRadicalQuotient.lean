import ModularRep.PaperProofs.TypeBRankThreeProductRadical
import ModularRep.RadicalTransport
import ModularRep.NormalizerQuotient

/-!
# Product p-cores and the radical coordinate criterion

The p-core of a finite product is the product of the actual p-cores.
The original normalizer coordinates then give the radical criterion and
radicality of each coordinate image. All maps retain their literal values.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRankThreeProductRadicalQuotient

open ModularRep TypeBRankThreeProductRadical
open scoped BigOperators

universe u v

variable {C : Type u} (H : C → Type v) [∀ c, Group (H c)]

/-- The coordinate identification of a literal subgroup product. -/
def subgroupPiEquiv (R : ∀ c, Subgroup (H c)) :
    Subgroup.pi Set.univ R ≃* ((c : C) → R c) where
  toFun x c := ⟨x.val c, (Subgroup.mem_pi Set.univ).mp x.property c (Set.mem_univ c)⟩
  invFun x := ⟨fun c => (x c).val, (Subgroup.mem_pi Set.univ).mpr (fun c _ => (x c).property)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext (fun _ => Subtype.ext rfl)
  map_mul' _ _ := rfl

@[simp] theorem subgroupPiEquiv_value (R : ∀ c, Subgroup (H c))
    (x : Subgroup.pi Set.univ R) (c : C) :
    (subgroupPiEquiv H R x c).val = x.val c := rfl

private theorem projection_surjective (c : C) :
    Function.Surjective (projection H c) := by
  classical
  intro x
  exact ⟨Pi.mulSingle c x, Pi.mulSingle_eq_same c x⟩

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

/-- The p-core of the actual finite product has exactly the coordinate p-cores. -/
theorem pCore_pi [Fintype C] (p : ℕ) :
    pCore p ((c : C) → H c) =
      Subgroup.pi Set.univ (fun c => pCore p (H c)) := by
  apply le_antisymm
  · intro x hx
    apply (Subgroup.mem_pi Set.univ).mpr
    intro c _
    letI : ((pCore p ((d : C) → H d)).map (projection H c)).Normal :=
      (pCore_normal p ((d : C) → H d)).map
        (projection H c) (projection_surjective H c)
    have hle := normal_pSubgroup_le_pCore p
      ((pCore p ((d : C) → H d)).map (projection H c))
      ((pCore_isPGroup p ((d : C) → H d)).map (projection H c))
    exact hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  · let R := Subgroup.pi Set.univ (fun c => pCore p (H c))
    letI : R.Normal := Subgroup.normalizer_eq_top_iff.mp (by
      change Subgroup.normalizer
        (Subgroup.pi Set.univ (fun c => pCore p (H c)) : Set ((c : C) → H c)) = ⊤
      rw [normalizer_pi H]
      simp only [Subgroup.normalizer_eq_top, Subgroup.pi_top])
    apply normal_pSubgroup_le_pCore p R
    exact (finitePi_isPGroup (fun c => pCore p (H c))
      (fun c => pCore_isPGroup p (H c))).of_equiv
      (subgroupPiEquiv H (fun c => pCore p (H c))).symm

/-- The p-core inside a product normalizer is read in the original coordinates. -/
theorem normalizer_pCore_mem_iff [Fintype C] (p : ℕ)
    (R : ∀ c, Subgroup (H c))
    (n : Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c))) :
    n ∈ pCore p (Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c))) ↔
      ∀ c, normalizerPiEquiv H R n c ∈ pCore p (Subgroup.normalizer (R c : Set (H c))) := by
  rw [← pCore_comap_equiv p (normalizerPiEquiv H R),
    pCore_pi (fun c => Subgroup.normalizer (R c : Set (H c))) p]
  simp only [Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, forall_const]
  rfl

/-- The image of the normalizer p-core is a product of the actual local images. -/
theorem normalizerPCore_pi [Fintype C] (p : ℕ) (R : ∀ c, Subgroup (H c)) :
    normalizerPCore p (Subgroup.pi Set.univ R) =
      Subgroup.pi Set.univ (fun c => normalizerPCore p (R c)) := by
  classical
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    apply (Subgroup.mem_pi Set.univ).mpr
    intro c _
    exact Subgroup.mem_map.mpr ⟨normalizerPiEquiv H R n c,
      (normalizer_pCore_mem_iff H p R n).mp hn c, rfl⟩
  · intro hx
    have coordinates : ∀ c, ∃ n : Subgroup.normalizer (R c : Set (H c)),
        n ∈ pCore p (Subgroup.normalizer (R c : Set (H c))) ∧ n.val = x c := by
      intro c
      exact Subgroup.mem_map.mp ((Subgroup.mem_pi Set.univ).mp hx c (Set.mem_univ c))
    choose n hn hvalue using coordinates
    apply Subgroup.mem_map.mpr
    refine ⟨(normalizerPiEquiv H R).symm n, ?_, ?_⟩
    · apply (normalizer_pCore_mem_iff H p R _).mpr
      intro c
      simpa only [MulEquiv.apply_symm_apply] using hn c
    · funext c
      exact hvalue c

/-- A literal product is radical exactly when every specified factor is radical. -/
theorem radical_pi_iff [Fintype C] (p : ℕ) (R : ∀ c, Subgroup (H c)) :
    IsRadicalSubgroup p (Subgroup.pi Set.univ R) ↔
      ∀ c, IsRadicalSubgroup p (R c) := by
  constructor
  · intro h c
    change Subgroup.pi Set.univ R = normalizerPCore p (Subgroup.pi Set.univ R) at h
    rw [normalizerPCore_pi H p R] at h
    have hc := congrArg (fun Q : Subgroup ((d : C) → H d) => Q.map (projection H c)) h
    change R c = normalizerPCore p (R c)
    simpa only [map_pi_projection] using hc
  · intro h
    change Subgroup.pi Set.univ R = normalizerPCore p (Subgroup.pi Set.univ R)
    rw [normalizerPCore_pi H p R]
    apply congrArg (Subgroup.pi Set.univ)
    funext c
    exact h c

/-- Projection of a radical subgroup of a finite product is radical. -/
theorem radical_projection [Fintype C] [∀ c, Finite (H c)]
    {p : ℕ} (hp : p.Prime) (Q : Subgroup ((c : C) → H c))
    (hQ : IsRadicalSubgroup p Q) (c : C) :
    IsRadicalSubgroup p (Q.map (projection H c)) := by
  have hhull : IsRadicalSubgroup p (coordinateHull H Q) :=
    Eq.mp (congrArg (fun R : Subgroup ((d : C) → H d) => IsRadicalSubgroup p R)
      (radical_eq_coordinateHull H hp Q hQ)) hQ
  exact (radical_pi_iff H p (fun d => Q.map (projection H d))).mp hhull c

/-- The subgroup divided out in the normalizer has the same coordinate images. -/
theorem normalizerSubgroup_map (R : ∀ c, Subgroup (H c)) :
    ((Subgroup.pi Set.univ R).subgroupOf
      (Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c)))).map
        (normalizerPiEquiv H R).toMonoidHom =
      Subgroup.pi Set.univ (fun c => (R c).subgroupOf
        (Subgroup.normalizer (R c : Set (H c)))) := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  apply Subgroup.ext
  intro x
  rfl

/-- The actual coordinate quotient projections on the same product normalizer. -/
def quotientCoordinateHom (R : ∀ c, Subgroup (H c)) :
    Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c)) →*
      ((c : C) → NormalizerQuotient (R c)) where
  toFun n c := QuotientGroup.mk (normalizerPiEquiv H R n c)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem quotientCoordinateHom_value (R : ∀ c, Subgroup (H c))
    (n : Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c)))
    (c : C) :
    quotientCoordinateHom H R n c = QuotientGroup.mk (normalizerPiEquiv H R n c) := rfl

/-- Every tuple of local quotient elements has an actual normalizer lift. -/
theorem quotientCoordinateHom_surjective (R : ∀ c, Subgroup (H c)) :
    Function.Surjective (quotientCoordinateHom H R) := by
  classical
  intro x
  have lifts : ∀ c, ∃ n : Subgroup.normalizer (R c : Set (H c)),
      (QuotientGroup.mk n : NormalizerQuotient (R c)) = x c := by
    intro c
    exact QuotientGroup.mk'_surjective
      ((R c).subgroupOf (Subgroup.normalizer (R c : Set (H c)))) (x c)
  choose n hn using lifts
  refine ⟨(normalizerPiEquiv H R).symm n, ?_⟩
  funext c
  change QuotientGroup.mk (normalizerPiEquiv H R ((normalizerPiEquiv H R).symm n) c) = x c
  rw [MulEquiv.apply_symm_apply]
  exact hn c

/-- Its kernel is the literal product subgroup inside its normalizer. -/
theorem quotientCoordinateHom_ker (R : ∀ c, Subgroup (H c)) :
    (quotientCoordinateHom H R).ker =
      (Subgroup.pi Set.univ R).subgroupOf
        (Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c))) := by
  apply Subgroup.ext
  intro n
  rw [MonoidHom.mem_ker]
  constructor
  · intro hn
    change n.val ∈ Subgroup.pi Set.univ R
    apply (Subgroup.mem_pi Set.univ).mpr
    intro c _
    have hc : (QuotientGroup.mk (normalizerPiEquiv H R n c) :
        NormalizerQuotient (R c)) = 1 := congrFun hn c
    exact (QuotientGroup.eq_one_iff (normalizerPiEquiv H R n c)).mp hc
  · intro hn
    change n.val ∈ Subgroup.pi Set.univ R at hn
    funext c
    apply (QuotientGroup.eq_one_iff (normalizerPiEquiv H R n c)).mpr
    exact (Subgroup.mem_pi Set.univ).mp hn c (Set.mem_univ c)

/-- The normalizer quotient is identified with the actual coordinate quotients. -/
def normalizerQuotientPiEquiv (R : ∀ c, Subgroup (H c)) :
    NormalizerQuotient (Subgroup.pi Set.univ R) ≃*
      ((c : C) → NormalizerQuotient (R c)) :=
  (QuotientGroup.quotientMulEquivOfEq (quotientCoordinateHom_ker H R).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quotientCoordinateHom H R)
      (quotientCoordinateHom_surjective H R))

/-- The quotient equivalence preserves each original quotient projection. -/
@[simp] theorem normalizerQuotientPiEquiv_mk (R : ∀ c, Subgroup (H c))
    (n : Subgroup.normalizer (Subgroup.pi Set.univ R : Set ((c : C) → H c)))
    (c : C) :
    normalizerQuotientPiEquiv H R (QuotientGroup.mk n) c =
      QuotientGroup.mk (normalizerPiEquiv H R n c) := rfl

end ModularRep.PaperProofs.TypeBRankThreeProductRadicalQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
