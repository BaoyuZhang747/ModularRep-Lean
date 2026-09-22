import ModularRep.PaperProofs.TypeBRankThreeProductRadicalQuotient
import ModularRep.PaperProofs.TypeBRankThreeProductOrdinarySource
import ModularRep.WeightCharacterBridge

/-!
# Raw weights on the literal finite product

The subgroup is the actual coordinate product.  Its local ordinary character
is the prescribed product on the actual factor normalizer quotients,
transported forward along the inverse of the actual quotient equivalence.
The prime, radicality and defect-zero proofs concern this same pair.

Sufficient finite ordinary roots descend from the ambient product order by
subgroup and quotient divisibility.  The only external input is the existing
ordinary product dictionary on these exact quotient carriers.  This module
contains no block selector, induced-block assignment or weight equivalence.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs.TypeBRankThreeProductRawWeight

open TypeBRankThreeProductRadical TypeBRankThreeProductRadicalQuotient
open TypeBRankThreeProductOrdinarySource

universe u

variable {I K : Type u} (H : I → Type u) [Fintype I]
variable [∀ i, Group (H i)] [∀ i, Finite (H i)]

/-- The actual quotient product order divides the ambient product order.
This is the universe-polymorphic two-divisibility argument underlying
TypeBLocalReductionInstantiation.local_order_dvd. -/
theorem quotientProduct_order_dvd (Q : ∀ i, Subgroup (H i)) :
    Nat.card (∀ i, NormalizerQuotient (Q i)) ∣ Nat.card (∀ i, H i) := by
  rw [← Nat.card_congr (normalizerQuotientPiEquiv H Q).toEquiv]
  exact (Subgroup.card_quotient_dvd_card
    ((Subgroup.pi Set.univ Q).subgroupOf
      (Subgroup.normalizer (Subgroup.pi Set.univ Q : Set (∀ i, H i))))).trans
    (Subgroup.card_subgroup_dvd_card
      (Subgroup.normalizer (Subgroup.pi Set.univ Q : Set (∀ i, H i))))

variable [Field K] [CharZero K]
variable [HasEnoughRootsOfUnity K (Nat.card (∀ i, H i))]

/-- One ambient finite-root guard supplies the SAME quotient product guard. -/
def quotientProductRoots (Q : ∀ i, Subgroup (H i)) :
    HasEnoughRootsOfUnity K (Nat.card (∀ i, NormalizerQuotient (Q i))) :=
  HasEnoughRootsOfUnity.of_dvd K (quotientProduct_order_dvd H Q)

variable {p : ℕ} (hp : Nat.Prime p)
variable (W : ∀ i, CharacterWeight p K (H i))
variable (ordinary : ExternalProductSource
  (fun i => NormalizerQuotient ((W i).subgroup)) p hp
  (quotientProductRoots (K := K) H (fun i => (W i).subgroup)))

/-- The raw product weight uses the literal subgroup and local quotient maps. -/
def rawProduct : CharacterWeight p K (∀ i, H i) where
  prime := hp
  subgroup := Subgroup.pi Set.univ (fun i => (W i).subgroup)
  radical := (radical_pi_iff H p (fun i => (W i).subgroup)).mpr
    (fun i => (W i).radical)
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv
    (product (fun i => NormalizerQuotient ((W i).subgroup)) ordinary
      (fun i => (W i).localCharacter))
    (normalizerQuotientPiEquiv H (fun i => (W i).subgroup)).symm
  defectZero := ((product_defect_zero_iff
    (fun i => NormalizerQuotient ((W i).subgroup)) ordinary
    (fun i => (W i).localCharacter)).mpr
      (fun i => (W i).defectZero)).mapEquiv
    (normalizerQuotientPiEquiv H (fun i => (W i).subgroup)).symm

/-- The product radical is retained as a literal subgroup equality. -/
@[simp] theorem rawProduct_subgroup :
    (rawProduct H hp W ordinary).subgroup =
      Subgroup.pi Set.univ (fun i => (W i).subgroup) := rfl

/-- The local character retains the prescribed external product and its map. -/
theorem rawProduct_localCharacter :
    (rawProduct H hp W ordinary).localCharacter =
      OrdinaryIrreducibleCharacter.mapEquiv
        (product (fun i => NormalizerQuotient ((W i).subgroup)) ordinary
          (fun i => (W i).localCharacter))
        (normalizerQuotientPiEquiv H (fun i => (W i).subgroup)).symm := rfl

/-- Values on every actual normalizer quotient element use the forward
coordinate quotient equivalence. -/
@[simp] theorem rawProduct_localCharacter_apply
    (x : NormalizerQuotient (Subgroup.pi Set.univ (fun i => (W i).subgroup))) :
    (rawProduct H hp W ordinary).localCharacter x =
      ∏ i, (W i).localCharacter
        (normalizerQuotientPiEquiv H (fun i => (W i).subgroup) x i) := rfl

/-- Values on the original normalizer lifts preserve their actual coordinates. -/
theorem rawProduct_localCharacter_mk
    (n : Subgroup.normalizer
      (Subgroup.pi Set.univ (fun i => (W i).subgroup) : Set (∀ i, H i))) :
    (rawProduct H hp W ordinary).localCharacter (QuotientGroup.mk n) =
      ∏ i, (W i).localCharacter
        (QuotientGroup.mk (normalizerPiEquiv H (fun i => (W i).subgroup) n i)) := rfl

end ModularRep.PaperProofs.TypeBRankThreeProductRawWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
