import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
import ModularRep.SubgroupIntervalTwo

/-! The actual Brauer stabilizer modulo its embedded inner subgroup embeds
in the literal outer automorphism quotient. Cardinality and cyclicity follow
from the structural outer-quotient binding, without a selected splitting. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

open ModularRep
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

universe u

instance innerInverseOpRangeNormal {G : Type u} [Group G] :
    (RepresentationWeight.innerInverseOpHom (G := G)).range.Normal := by
  constructor
  intro beta hbeta alpha
  obtain ⟨x, rfl⟩ := hbeta
  refine ⟨alpha.unop⁻¹ x, ?_⟩
  apply MulOpposite.unop_injective
  ext y
  simp [RepresentationWeight.innerInverseOpHom, mul_assoc]

abbrev LiteralOuterQuotient (G : Type u) [Group G] :=
  (MulAut G)ᵐᵒᵖ ⧸ (RepresentationWeight.innerInverseOpHom (G := G)).range

instance literalOuterFinite {G : Type u} [Group G] [Finite G] :
    Finite (LiteralOuterQuotient G) := by
  let : Finite (MulAut G) := Finite.of_injective
    (fun alpha : MulAut G => (alpha : G → G)) DFunLike.coe_injective
  let : Finite (MulAut G)ᵐᵒᵖ := Finite.of_equiv (MulAut G) MulOpposite.opEquiv
  exact Finite.of_surjective
    (QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range)
    (QuotientGroup.mk'_surjective _)

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)

theorem actualBase_eq_comap_innerRange :
    actualBase iota phi =
      (RepresentationWeight.innerInverseOpHom (G := G)).range.comap
        (MulAction.stabilizer (MulAut G)ᵐᵒᵖ phi).subtype := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

def actualOuterEmbedding :
    ActualAutAmbient iota phi ⧸ actualBase iota phi →* LiteralOuterQuotient G :=
  QuotientGroup.map (actualBase iota phi)
    (RepresentationWeight.innerInverseOpHom (G := G)).range
    (MulAction.stabilizer (MulAut G)ᵐᵒᵖ phi).subtype
    (actualBase_eq_comap_innerRange iota phi).le

theorem actualOuterEmbedding_injective :
    Function.Injective (actualOuterEmbedding iota phi) := by
  rw [← MonoidHom.ker_eq_bot_iff, actualOuterEmbedding, QuotientGroup.ker_map,
    ← actualBase_eq_comap_innerRange, QuotientGroup.map_mk'_self]

theorem actual_quotient_card_le_outer :
    Nat.card (ActualAutAmbient iota phi ⧸ actualBase iota phi) ≤
      Nat.card (LiteralOuterQuotient G) :=
  Nat.card_le_card_of_injective (actualOuterEmbedding iota phi)
    (actualOuterEmbedding_injective iota phi)

theorem actual_quotient_card_le_two
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2) :
    Nat.card (ActualAutAmbient iota phi ⧸ actualBase iota phi) ≤ 2 := by
  simpa only [hOuter] using actual_quotient_card_le_outer iota phi

theorem actual_quotient_isCyclic
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2) :
    IsCyclic (ActualAutAmbient iota phi ⧸ actualBase iota phi) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (LiteralOuterQuotient G) := isCyclic_of_prime_card hOuter
  exact isCyclic_of_injective (actualOuterEmbedding iota phi)
    (actualOuterEmbedding_injective iota phi)

theorem actual_intermediate_eq_base_or_top
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (J : Subgroup (ActualAutAmbient iota phi)) (hJ : actualBase iota phi ≤ J) :
    J = actualBase iota phi ∨ J = ⊤ :=
  subgroup_eq_base_or_top_of_quotient_card_le_two (actualBase iota phi)
    (actual_quotient_card_le_two iota phi hOuter) J hJ

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
