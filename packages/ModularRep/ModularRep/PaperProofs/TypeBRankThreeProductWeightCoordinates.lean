import ModularRep.PaperProofs.TypeBRankThreeProductRawWeight

/-!
# Intrinsic coordinates of a raw product weight

The inverse projects the actual radical subgroup, transports its local
character along the proved subgroup equality and the coordinate quotient
equivalence, and factors that character by the prescribed ordinary product.
The forward and inverse maps are deductions from the same ordinary source
family.  No conjugacy quotient, block assignment or matching is used here.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs.TypeBRankThreeProductWeightCoordinates

open OrdinaryIrreducibleCharacter
open TypeBRankThreeProductRadical TypeBRankThreeProductRadicalQuotient
open TypeBRankThreeProductOrdinarySource TypeBRankThreeProductRawWeight

universe u

private theorem mapEquiv_injective {K A B : Type u}
    [Field K] [CharZero K] [Group A] [Group B] (e : A ≃* B) :
    Function.Injective (fun chi : Irr K A => mapEquiv chi e) := by
  intro chi theta h
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  have hx := congrArg (fun eta : Irr K B => eta (e x)) h
  simpa only [mapEquiv_apply, MulEquiv.symm_apply_apply] using hx

private theorem mapEquiv_symm {K A B : Type u}
    [Field K] [CharZero K] [Group A] [Group B]
    (chi : Irr K A) (e : A ≃* B) :
    mapEquiv (mapEquiv chi e) e.symm = chi := by
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  change chi (e.symm (e x)) = chi x
  rw [MulEquiv.symm_apply_apply]

private theorem cast_defectZero {p : ℕ} {K G : Type u}
    [Field K] [CharZero K] [Group G] [Finite G]
    {Q R : Subgroup G} (h : Q = R) {chi : Irr K (NormalizerQuotient Q)}
    (hdz : IsDefectZeroOrdinaryCharacter p chi) :
    IsDefectZeroOrdinaryCharacter p (CharacterWeight.castLocalCharacter h chi) := by
  subst R
  exact hdz

private theorem localCharacter_eq_of_eq {p : ℕ} {K G : Type u}
    [Field K] [CharZero K] [Group G] [Finite G]
    {W V : CharacterWeight p K G} (h : W = V) :
    CharacterWeight.castLocalCharacter (congrArg CharacterWeight.subgroup h)
      W.localCharacter = V.localCharacter := by
  subst V
  rfl

variable {I K : Type u} (H : I → Type u) [Fintype I]
variable [∀ i, Group (H i)] [∀ i, Finite (H i)]
variable [Field K] [CharZero K]
variable {p : ℕ} (hp : Nat.Prime p)

/-- The coordinates are the images of the original radical subgroup. -/
def coordinateSubgroups (W : CharacterWeight p K (∀ i, H i)) :
    ∀ i, Subgroup (H i) :=
  fun i => W.subgroup.map (projection H i)

include hp in
/-- Radicality gives equality with the literal product of these images. -/
theorem subgroup_eq_pi_coordinates (W : CharacterWeight p K (∀ i, H i)) :
    W.subgroup = Subgroup.pi Set.univ (coordinateSubgroups H W) :=
  radical_eq_coordinateHull H hp W.subgroup W.radical

include hp in
/-- Each projected subgroup is itself radical. -/
theorem coordinateSubgroups_radical (W : CharacterWeight p K (∀ i, H i)) (i : I) :
    IsRadicalSubgroup p (coordinateSubgroups H W i) :=
  radical_projection H hp W.subgroup W.radical i

/-- The same local character, now on the product of actual quotient groups. -/
def quotientCharacter (W : CharacterWeight p K (∀ i, H i)) :
    Irr K (∀ i, NormalizerQuotient (coordinateSubgroups H W i)) :=
  mapEquiv
    (CharacterWeight.castLocalCharacter (subgroup_eq_pi_coordinates H hp W)
      W.localCharacter)
    (normalizerQuotientPiEquiv H (coordinateSubgroups H W))

theorem quotientCharacter_defectZero (W : CharacterWeight p K (∀ i, H i)) :
    IsDefectZeroOrdinaryCharacter p (quotientCharacter H hp W) :=
  (cast_defectZero (subgroup_eq_pi_coordinates H hp W) W.defectZero).mapEquiv
    (normalizerQuotientPiEquiv H (coordinateSubgroups H W))

variable [HasEnoughRootsOfUnity K (Nat.card (∀ i, H i))]
variable (ordinary : ∀ Q : ∀ i, Subgroup (H i),
  ExternalProductSource (fun i => NormalizerQuotient (Q i)) p hp
    (quotientProductRoots (K := K) H Q))

/-- Ordinary coordinates use the inverse of the constructed product map. -/
def coordinateCharacters (W : CharacterWeight p K (∀ i, H i)) :
    ∀ i, Irr K (NormalizerQuotient (coordinateSubgroups H W i)) :=
  (productEquiv (fun i => NormalizerQuotient (coordinateSubgroups H W i))
    (ordinary (coordinateSubgroups H W))).symm (quotientCharacter H hp W)

/-- The recovered tuple reproduces the same transported local character. -/
theorem product_coordinateCharacters (W : CharacterWeight p K (∀ i, H i)) :
    product (fun i => NormalizerQuotient (coordinateSubgroups H W i))
      (ordinary (coordinateSubgroups H W)) (coordinateCharacters H hp ordinary W) =
        quotientCharacter H hp W :=
  (productEquiv (fun i => NormalizerQuotient (coordinateSubgroups H W i))
    (ordinary (coordinateSubgroups H W))).apply_symm_apply (quotientCharacter H hp W)

/-- Defect zero is inherited by every actual ordinary coordinate. -/
theorem coordinateCharacters_defectZero
    (W : CharacterWeight p K (∀ i, H i)) (i : I) :
    IsDefectZeroOrdinaryCharacter p (coordinateCharacters H hp ordinary W i) := by
  have hprod : IsDefectZeroOrdinaryCharacter p
      (product (fun i => NormalizerQuotient (coordinateSubgroups H W i))
        (ordinary (coordinateSubgroups H W)) (coordinateCharacters H hp ordinary W)) := by
    rw [product_coordinateCharacters H hp ordinary W]
    exact quotientCharacter_defectZero H hp W
  exact ((product_defect_zero_iff
    (fun i => NormalizerQuotient (coordinateSubgroups H W i))
    (ordinary (coordinateSubgroups H W))
    (coordinateCharacters H hp ordinary W)).mp hprod) i

/-- Intrinsic raw coordinates, before taking any conjugacy quotient. -/
def rawCoordinates (W : CharacterWeight p K (∀ i, H i)) :
    ∀ i, CharacterWeight p K (H i) := fun i =>
  { prime := hp
    subgroup := coordinateSubgroups H W i
    radical := coordinateSubgroups_radical H hp W i
    localCharacter := coordinateCharacters H hp ordinary W i
    defectZero := coordinateCharacters_defectZero H hp ordinary W i }

@[simp] theorem rawCoordinates_subgroup
    (W : CharacterWeight p K (∀ i, H i)) (i : I) :
    (rawCoordinates H hp ordinary W i).subgroup = W.subgroup.map (projection H i) := rfl

@[simp] theorem rawCoordinates_localCharacter
    (W : CharacterWeight p K (∀ i, H i)) (i : I) :
    (rawCoordinates H hp ordinary W i).localCharacter =
      coordinateCharacters H hp ordinary W i := rfl

/-- The value equation retains the literal subgroup-equality transport. -/
theorem coordinate_values (W : CharacterWeight p K (∀ i, H i))
    (x : NormalizerQuotient (Subgroup.pi Set.univ (coordinateSubgroups H W))) :
    CharacterWeight.castLocalCharacter (subgroup_eq_pi_coordinates H hp W)
        W.localCharacter x =
      ∏ i, (rawCoordinates H hp ordinary W i).localCharacter
        (normalizerQuotientPiEquiv H (coordinateSubgroups H W) x i) := by
  have hx := congrArg
    (fun chi : Irr K (∀ i, NormalizerQuotient (coordinateSubgroups H W i)) =>
      chi (normalizerQuotientPiEquiv H (coordinateSubgroups H W) x))
    (product_coordinateCharacters H hp ordinary W)
  simpa only [product_apply, quotientCharacter, mapEquiv_apply,
    MulEquiv.symm_apply_apply, rawCoordinates_localCharacter] using hx.symm

/-- On normalizer lifts, every coordinate is the original quotient projection. -/
theorem coordinate_values_mk (W : CharacterWeight p K (∀ i, H i))
    (n : Subgroup.normalizer
      (Subgroup.pi Set.univ (coordinateSubgroups H W) : Set (∀ i, H i))) :
    CharacterWeight.castLocalCharacter (subgroup_eq_pi_coordinates H hp W)
        W.localCharacter (QuotientGroup.mk n) =
      ∏ i, (rawCoordinates H hp ordinary W i).localCharacter
        (QuotientGroup.mk (normalizerPiEquiv H (coordinateSubgroups H W) n i)) := by
  exact coordinate_values H hp ordinary W (QuotientGroup.mk n)

/-- The forward map uses the source at exactly the input radical tuple. -/
def rawProductMap (W : ∀ i, CharacterWeight p K (H i)) :
    CharacterWeight p K (∀ i, H i) :=
  rawProduct H hp W (ordinary (fun i => (W i).subgroup))

/-- Recombining the intrinsic coordinates gives literal raw-weight equality. -/
theorem rawProduct_coordinates (W : CharacterWeight p K (∀ i, H i)) :
    rawProductMap H hp ordinary (rawCoordinates H hp ordinary W) = W := by
  apply CharacterWeight.eq_of_isomorphic
  refine ⟨(subgroup_eq_pi_coordinates H hp W).symm, ?_⟩
  change CharacterWeight.castLocalCharacter (subgroup_eq_pi_coordinates H hp W).symm
    (mapEquiv
      (product (fun i => NormalizerQuotient (coordinateSubgroups H W i))
        (ordinary (coordinateSubgroups H W)) (coordinateCharacters H hp ordinary W))
      (normalizerQuotientPiEquiv H (coordinateSubgroups H W)).symm) = W.localCharacter
  rw [product_coordinateCharacters H hp ordinary W]
  change CharacterWeight.castLocalCharacter (subgroup_eq_pi_coordinates H hp W).symm
    (mapEquiv
      (mapEquiv
        (CharacterWeight.castLocalCharacter (subgroup_eq_pi_coordinates H hp W)
          W.localCharacter)
        (normalizerQuotientPiEquiv H (coordinateSubgroups H W)))
      (normalizerQuotientPiEquiv H (coordinateSubgroups H W)).symm) = W.localCharacter
  rw [mapEquiv_symm, CharacterWeight.castLocalCharacter_symm]

private theorem coordinate_characters_eq
    (Q R : ∀ i, Subgroup (H i))
    (chi : ∀ i, Irr K (NormalizerQuotient (Q i)))
    (theta : ∀ i, Irr K (NormalizerQuotient (R i))) (hQ : Q = R)
    (hchi : CharacterWeight.castLocalCharacter (congrArg (Subgroup.pi Set.univ) hQ)
        (mapEquiv (product (fun i => NormalizerQuotient (Q i)) (ordinary Q) chi)
          (normalizerQuotientPiEquiv H Q).symm) =
      mapEquiv (product (fun i => NormalizerQuotient (R i)) (ordinary R) theta)
        (normalizerQuotientPiEquiv H R).symm) :
    ∀ i, CharacterWeight.castLocalCharacter (congrFun hQ i) (chi i) = theta i := by
  subst R
  have hprod := mapEquiv_injective (normalizerQuotientPiEquiv H Q).symm hchi
  have htuple := TypeBRankThreeProductOrdinarySource.product_injective
    (fun i => NormalizerQuotient (Q i)) (ordinary Q) hprod
  intro i
  exact congrFun htuple i

/-- Projection equality and ordinary product uniqueness give injectivity. -/
theorem rawProduct_injective : Function.Injective (rawProductMap H hp ordinary) := by
  intro W V h
  have hsub := congrArg CharacterWeight.subgroup h
  have hQ : (fun i => (W i).subgroup) = (fun i => (V i).subgroup) := by
    funext i
    have hi := congrArg (fun Q : Subgroup (∀ i, H i) => Q.map (projection H i)) hsub
    simpa only [rawProductMap, rawProduct_subgroup, map_pi_projection] using hi
  have hlocal := localCharacter_eq_of_eq h
  have hchars := coordinate_characters_eq H hp ordinary
    (fun i => (W i).subgroup) (fun i => (V i).subgroup)
    (fun i => (W i).localCharacter) (fun i => (V i).localCharacter) hQ hlocal
  funext i
  exact CharacterWeight.eq_of_isomorphic ⟨congrFun hQ i, hchars i⟩

theorem rawProduct_surjective : Function.Surjective (rawProductMap H hp ordinary) :=
  fun W => ⟨rawCoordinates H hp ordinary W, rawProduct_coordinates H hp ordinary W⟩

theorem coordinates_rawProduct (W : ∀ i, CharacterWeight p K (H i)) :
    rawCoordinates H hp ordinary (rawProductMap H hp ordinary W) = W := by
  apply rawProduct_injective H hp ordinary
  exact rawProduct_coordinates H hp ordinary (rawProductMap H hp ordinary W)

/-- All raw weights have unique intrinsic coordinates on the same factors. -/
def rawProductEquiv :
    (∀ i, CharacterWeight p K (H i)) ≃ CharacterWeight p K (∀ i, H i) where
  toFun := rawProductMap H hp ordinary
  invFun := rawCoordinates H hp ordinary
  left_inv := coordinates_rawProduct H hp ordinary
  right_inv := rawProduct_coordinates H hp ordinary

@[simp] theorem rawProductEquiv_apply (W : ∀ i, CharacterWeight p K (H i)) :
    rawProductEquiv H hp ordinary W =
      rawProduct H hp W (ordinary (fun i => (W i).subgroup)) := rfl

@[simp] theorem rawProductEquiv_symm_apply (W : CharacterWeight p K (∀ i, H i)) :
    (rawProductEquiv H hp ordinary).symm W = rawCoordinates H hp ordinary W := rfl

end ModularRep.PaperProofs.TypeBRankThreeProductWeightCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
