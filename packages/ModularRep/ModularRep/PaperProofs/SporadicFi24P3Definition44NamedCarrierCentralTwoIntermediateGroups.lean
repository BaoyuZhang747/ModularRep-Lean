import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient

/-! The actual centre-two ambient has no proper intermediate group
above its original-group base. No faithful outer action is needed. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoIntermediateGroups

open ModularRep
open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient

universe u
variable {G T C : Type u} [Group G] [Group T] [Group C]
variable (E : GroupExtension G T C)
variable {p : ℕ} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [Finite G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)

theorem brauer_quotient_card_le_two (hC : Nat.card C = 2) :
    Nat.card (brauerAmbient E iota phi ⧸ (brauerEmbedding E iota phi).range) ≤ 2 := by
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; decide)
  let e := QuotientGroup.quotientMulEquivOfEq (brauerEmbedding_range E iota phi)
  calc
    Nat.card (brauerAmbient E iota phi ⧸ (brauerEmbedding E iota phi).range) =
        Nat.card (brauerAmbient E iota phi ⧸ (brauerProjection E iota phi).ker) :=
      Nat.card_congr e.toEquiv
    _ ≤ Nat.card C :=
      Nat.card_le_card_of_injective (QuotientGroup.kerLift (brauerProjection E iota phi))
        (QuotientGroup.kerLift_injective _)
    _ = 2 := hC

theorem brauer_intermediate_eq_base_or_top (hC : Nat.card C = 2)
    (J : Subgroup (brauerAmbient E iota phi))
    (hJ : (brauerEmbedding E iota phi).range ≤ J) :
    J = (brauerEmbedding E iota phi).range ∨ J = ⊤ := by
  let : Finite T := extension_finite E hC
  exact subgroup_eq_base_or_top_of_quotient_card_le_two
    (brauerEmbedding E iota phi).range (brauer_quotient_card_le_two E iota phi hC) J hJ

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoIntermediateGroups


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
