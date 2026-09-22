import ManuscriptIBAW.TypeC.PrincipalParameters
import ManuscriptIBAW.TypeC.PrincipalNumericalParameters

/-!
# Coordinates for product subgroups and Feng–Malle colours

The source identifies local basic subgroups and their actual characters
with the finite Feng–Malle colour set. The remaining source clauses classify subgroup
multiplicities. They do not assume a map of weights or a bijection of full parameter sets. Extension by zero and restriction of staircase heights
construct that bijection below.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalProductAtlas
open ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer
open ModularRep.PaperProofs.OddTwoPrincipalProductCharacterJoin
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource

universe u

variable {n : ℕ} {F K Index : Type u}
variable [Field F] [Fintype F] [Field K] [CharZero K]

local instance coordinateSpFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

abbrev ProductColour (A : PrincipalProductData (n := n) (F := F) (K := K)) :=
  Σ j : Fin A.shape.count, Fin (A.shape.basic j).colours

def symplecticRankCast {a b : ℕ} (h : a = b) : Sp a F ≃* Sp b F := by
  subst b
  exact MulEquiv.refl _

/-- Each FM colour has an actual basic subgroup and its own ordinary
defect zero character. The rank is fixed by the numerical colour index. -/
structure FMPaletteRealisation where
  basic : ∀ c : FMPalette n, BasicModel (2 ^ c.1.1) F
  character : ∀ c : FMPalette n, LocalDefectZeroCharacters (K := K) (basic c).subgroup

variable (atlas : Index → PrincipalProductData (n := n) (F := F) (K := K))

/-- Coordinates comparing the basic subgroup and local character data with the
X−1 colour set in Feng–Malle, Section 5.1 and Proposition 5.4. The subgroup
identifications, normaliser lifts and character equalities are hypotheses.
The commuting square fixes the quotient equivalence to the prescribed
conjugation and rank coordinates. -/
structure FMProductCoordinates where
  palette : FMPaletteRealisation (n := n) (F := F) (K := K)
  coordinate : ∀ i, ProductColour (atlas i) ↪ FMPalette n
  rank_eq : ∀ i (a : ProductColour (atlas i)),
    (atlas i).shape.rank a.1 = 2 ^ (coordinate i a).1.1
  conjugator : ∀ i (a : ProductColour (atlas i)), Sp (2 ^ (coordinate i a).1.1) F
  subgroup_eq : ∀ i (a : ProductColour (atlas i)),
    ((((atlas i).shape.basic a.1).subgroup.map
      (symplecticRankCast (rank_eq i a)).toMonoidHom).map
        (MulAut.conj (conjugator i a)).toMonoidHom) =
      (palette.basic (coordinate i a)).subgroup
  normalizerLift : ∀ i (a : ProductColour (atlas i)),
    Subgroup.normalizer (((atlas i).shape.basic a.1).subgroup :
      Set (Sp ((atlas i).shape.rank a.1) F)) →*
      Subgroup.normalizer ((palette.basic (coordinate i a)).subgroup :
        Set (Sp (2 ^ (coordinate i a).1.1) F))
  normalizerLift_value : ∀ i (a : ProductColour (atlas i)) z,
    (normalizerLift i a z).1 = conjugator i a *
      symplecticRankCast (rank_eq i a) z.1 * (conjugator i a)⁻¹
  quotientEquiv : ∀ i (a : ProductColour (atlas i)),
    NormalizerQuotient ((atlas i).shape.basic a.1).subgroup ≃*
      NormalizerQuotient (palette.basic (coordinate i a)).subgroup
  quotient_square : ∀ i (a : ProductColour (atlas i)) z,
    quotientEquiv i a (QuotientGroup.mk' _ z) =
      QuotientGroup.mk' _ (normalizerLift i a z)
  character_eq : ∀ i (a : ProductColour (atlas i)),
    OrdinaryIrreducibleCharacter.mapEquiv
      (((atlas i).localCharacters a.1).enumeration a.2).1 (quotientEquiv i a) =
        (palette.character (coordinate i a)).1

namespace FMProductCoordinates

variable {atlas}
variable (C : FMProductCoordinates atlas)

def extendHeights (i : Index) (h : Assignments (atlas i).shape) : FMPalette n → ℕ :=
  Function.extend (C.coordinate i) (fun a => h.1 a.1 a.2) (fun _ => 0)

@[simp] theorem extendHeights_coordinate (i : Index)
    (h : Assignments (atlas i).shape) (a : ProductColour (atlas i)) :
    C.extendHeights i h (C.coordinate i a) = h.1 a.1 a.2 :=
  (C.coordinate i).injective.extend_apply _ _ a

theorem extendHeights_zero (i : Index) (h : Assignments (atlas i).shape)
    (c : FMPalette n) (hc : c ∉ Set.range (C.coordinate i)) :
    C.extendHeights i h c = 0 :=
  Function.extend_apply' _ _ _ hc

theorem extendHeights_rank (i : Index) (h : Assignments (atlas i).shape) :
    fmRank (C.extendHeights i h) = n := by
  classical
  have hs : fmRank (C.extendHeights i h) =
      ∑ a : ProductColour (atlas i),
        2 ^ (C.coordinate i a).1.1 * triangular (h.1 a.1 a.2) := by
    unfold fmRank
    calc
      _ = ∑ c ∈ Finset.univ.image (C.coordinate i),
          2 ^ c.1.1 * triangular (C.extendHeights i h c) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro c _ hc
        have hnot : c ∉ Set.range (C.coordinate i) := by simpa using hc
        rw [C.extendHeights_zero i h c hnot]
        simp [triangular]
      _ = _ := by
        rw [Finset.sum_image (by
          intro a _ b _ heq
          exact (C.coordinate i).injective heq)]
        simp only [extendHeights_coordinate]
  rw [hs, Fintype.sum_sigma]
  simp_rw [← C.rank_eq]
  simp_rw [← Finset.mul_sum, h.2]
  simpa only [Nat.mul_comm] using (atlas i).shape.rank_sum

def encode (h : PrincipalParameter atlas) : FMParameter n :=
  ⟨C.extendHeights h.1 h.2, C.extendHeights_rank h.1 h.2⟩

/-- This condition involves only the multiplicity of each actual basic
subgroup. Its local character colours are summed separately. -/
def HasProductMultiplicities (height : FMPalette n → ℕ) (i : Index) : Prop :=
  (∀ c, c ∉ Set.range (C.coordinate i) → height c = 0) ∧
    (∀ j : Fin (atlas i).shape.count,
      ∑ b : Fin ((atlas i).shape.basic j).colours,
        triangular (height (C.coordinate i ⟨j, b⟩)) = (atlas i).shape.copies j)

theorem encoded_multiplicities (h : PrincipalParameter atlas) :
    C.HasProductMultiplicities (C.encode h).1 h.1 := by
  constructor
  · exact C.extendHeights_zero h.1 h.2
  · intro j
    change (∑ b, triangular (C.extendHeights h.1 h.2 (C.coordinate h.1 ⟨j, b⟩))) = _
    simp only [extendHeights_coordinate]
    exact h.2.2 j

/-- The group classification chooses and uniquely identifies a product
subgroup from its multiplicities in the same classification of local factors.
Neither condition compares characters or gives a map of principal weights. -/
structure MultiplicityClassification : Prop where
  exists_index : ∀ h : FMParameter n, ∃ i, C.HasProductMultiplicities h.1 i
  unique_index : ∀ (h : FMParameter n) (i j : Index),
    C.HasProductMultiplicities h.1 i → C.HasProductMultiplicities h.1 j → i = j

variable (M : C.MultiplicityClassification)

def decodedIndex (h : FMParameter n) : Index := Classical.choose (M.exists_index h)

theorem decoded_multiplicities (h : FMParameter n) :
    C.HasProductMultiplicities h.1 (C.decodedIndex M h) :=
  Classical.choose_spec (M.exists_index h)

def decode (h : FMParameter n) : PrincipalParameter atlas :=
  ⟨C.decodedIndex M h,
    ⟨fun j b => h.1 (C.coordinate (C.decodedIndex M h) ⟨j, b⟩),
      (C.decoded_multiplicities M h).2⟩⟩

theorem encode_decode (h : FMParameter n) : C.encode (C.decode M h) = h := by
  apply Subtype.ext
  funext c
  by_cases hc : c ∈ Set.range (C.coordinate (C.decodedIndex M h))
  · obtain ⟨a, rfl⟩ := hc
    exact C.extendHeights_coordinate _ _ a
  · exact (C.extendHeights_zero _ _ c hc).trans
      ((C.decoded_multiplicities M h).1 c hc).symm

include M in
theorem encode_injective : Function.Injective C.encode := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ heq
  have hj' : C.HasProductMultiplicities (C.encode ⟨i, hi⟩).1 j := by
    rw [heq]
    exact C.encoded_multiplicities ⟨j, hj⟩
  have hij := M.unique_index (C.encode ⟨i, hi⟩) i j
    (C.encoded_multiplicities ⟨i, hi⟩) hj'
  subst j
  have hh : hi = hj := by
    apply Subtype.ext
    funext a b
    have hval := congrArg (fun h : FMParameter n => h.1 (C.coordinate i ⟨a, b⟩)) heq
    simpa only [encode, extendHeights_coordinate] using hval
  cases hh
  rfl

/-- Extension by zero and restriction of staircase heights give the numerical
parameter equivalence. -/
def parameterEquiv : PrincipalParameter atlas ≃ FMParameter n where
  toFun := C.encode
  invFun := C.decode M
  left_inv h := C.encode_injective M (C.encode_decode M (C.encode h))
  right_inv := C.encode_decode M

end FMProductCoordinates

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
