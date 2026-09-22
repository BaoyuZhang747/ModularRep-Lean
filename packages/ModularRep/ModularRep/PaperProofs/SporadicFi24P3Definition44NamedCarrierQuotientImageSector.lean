import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientAveraging

/-! # A primitive has nonzero central-quotient image exactly in the trivial sector -/

noncomputable section
open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientImageSector

open ModularRep
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralQuotientAveraging

universe u
variable {k G : Type u} [Field k] [Group G]

theorem quotient_trivialCentralIdempotent_image
    (Z : Subgroup G) [Z.Normal] [Fintype Z]
    [Invertible (Fintype.card Z : k)] :
    algebraMapOf (QuotientGroup.mk' Z)
        (centralCharacterIdempotent Z (1 : Z →* kˣ)) = 1 := by
  classical
  have hz (z : Z) : QuotientGroup.mk' Z (z : G) = 1 :=
    (QuotientGroup.eq_one_iff (z : G)).mpr z.property
  rw [centralCharacterIdempotent, map_smul, linearCharacterWeightedSum, map_sum]
  simp only [MonoidHom.one_apply, inv_one, Units.val_one,
    algebraMapOf_single, hz, ← MonoidAlgebra.one_def, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]

theorem centralCharacterSector_eq_one_of_quotient_image_ne_zero
    [IsAlgClosed k] (Z : Subgroup G) [Z.Normal] [Fintype Z]
    [Invertible (Fintype.card Z : k)] (hcentral : Z ≤ Subgroup.center G)
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (hne : algebraMapOf (QuotientGroup.mk' Z) b ≠ 0) :
    hb.centralCharacterSector Z hcentral = 1 := by
  classical
  by_contra hsector
  have hzero := hb.mul_centralCharacterIdempotent_eq_zero_of_ne_sector
    Z hcentral (mu := (1 : Z →* kˣ)) (Ne.symm hsector)
  have hmap := congrArg (algebraMapOf (k := k) (QuotientGroup.mk' Z)) hzero
  rw [map_mul, quotient_trivialCentralIdempotent_image, mul_one, map_zero] at hmap
  exact hne hmap

theorem trivial_sector_of_quotient_image_ne_zero
    [IsAlgClosed k] (Z : Subgroup G) [Z.Normal] [Fintype Z]
    [Invertible (Fintype.card Z : k)] (hcentral : Z ≤ Subgroup.center G)
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (hne : algebraMapOf (QuotientGroup.mk' Z) b ≠ 0) :
    IsCentralCharacterSector Z b (1 : Z →* kˣ) := by
  have hsector := hb.centralCharacterSector_isSector Z hcentral
  have heq := centralCharacterSector_eq_one_of_quotient_image_ne_zero Z hcentral hb hne
  simpa only [heq] using hsector

theorem quotient_image_ne_zero_iff_trivial_sector
    [IsAlgClosed k] (Z : Subgroup G) [Z.Normal] [Fintype Z]
    [Invertible (Fintype.card Z : k)] (hcentral : Z ≤ Subgroup.center G)
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b) :
    algebraMapOf (QuotientGroup.mk' Z) b ≠ 0 ↔ IsCentralCharacterSector Z b (1 : Z →* kˣ) :=
  ⟨trivial_sector_of_quotient_image_ne_zero Z hcentral hb,
    quotient_image_ne_zero_of_trivial_sector Z hb⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientImageSector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
