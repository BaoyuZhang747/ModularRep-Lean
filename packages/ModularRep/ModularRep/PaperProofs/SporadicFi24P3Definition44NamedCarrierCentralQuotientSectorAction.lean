import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly

/-! The specified Z-trivial sector is preserved by every automorphism pair
commuting with the fixed quotient. This follows from nonzero quotient image,
without assumptions about local reduction choices. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction

open ModularRep
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralQuotientAveraging
open SporadicFi24P3Definition44NamedCarrierQuotientImageSector
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly

universe u

theorem algebraMapOf_twist_square
    {k G H : Type u} [Field k] [Group G] [Group H]
    (f : G →* H) (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ x, f (alpha x) = beta (f x)) (a : k[G]) :
    algebraMapOf f (MonoidAlgebra.mapDomainRingEquiv k alpha a) =
      MonoidAlgebra.mapDomainRingEquiv k beta (algebraMapOf f a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single x c =>
      simp only [MonoidAlgebra.mapDomainRingEquiv_single, algebraMapOf_single, square]

theorem trivial_sector_twist_of_quotient_square
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G]
    (Z : Subgroup G) [Z.Normal] [Fintype Z]
    [Invertible (Fintype.card Z : k)] (hcentral : Z ≤ Subgroup.center G)
    (alpha : MulAut G) (beta : MulAut (G ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (b : LiteralPrimitiveBlock k G)
    (hb : IsCentralCharacterSector Z b.val (1 : Z →* kˣ)) :
    IsCentralCharacterSector Z (MulOpposite.op alpha • b).val (1 : Z →* kˣ) := by
  have squareInv (x : G) : QuotientGroup.mk' Z (alpha.symm x) =
      beta.symm (QuotientGroup.mk' Z x) := by
    apply beta.injective
    simpa only [MulEquiv.apply_symm_apply] using (square (alpha.symm x)).symm
  have hne := quotient_image_ne_zero_of_trivial_sector Z b.property hb
  apply trivial_sector_of_quotient_image_ne_zero Z hcentral
    (MulOpposite.op alpha • b).property
  change algebraMapOf (QuotientGroup.mk' Z)
    (MonoidAlgebra.mapDomainRingEquiv k alpha.symm b.val) ≠ 0
  rw [algebraMapOf_twist_square (QuotientGroup.mk' Z) alpha.symm beta.symm squareInv]
  intro hz
  apply hne
  apply (MonoidAlgebra.mapDomainRingEquiv k beta.symm).injective
  simpa only [map_zero] using hz

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
variable (hcentral : Z ≤ Subgroup.center X)

def sectorTwist (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) :
    SectorWeights R Z ≃ SectorWeights R Z where
  toFun w := ⟨MulOpposite.op alpha • w.val, by
    rw [R.1.weightBlock_transport]
    exact trivial_sector_twist_of_quotient_square Z hcentral alpha beta square
      (R.1.weightBlock w.val) w.property⟩
  invFun w := ⟨MulOpposite.op alpha.symm • w.val, by
    rw [R.1.weightBlock_transport]
    apply trivial_sector_twist_of_quotient_square Z hcentral alpha.symm beta.symm
      _ (R.1.weightBlock w.val) w.property
    intro x
    apply beta.injective
    simpa only [MulEquiv.apply_symm_apply] using (square (alpha.symm x)).symm⟩
  left_inv w := by
    apply Subtype.ext
    exact inv_smul_smul (MulOpposite.op alpha) w.val
  right_inv w := by
    apply Subtype.ext
    exact smul_inv_smul (MulOpposite.op alpha) w.val

omit [CharP k p] in
theorem sectorTwist_val (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (w : SectorWeights R Z) :
    (sectorTwist R Z hcentral alpha beta square w).val = MulOpposite.op alpha • w.val := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
