import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCenterEquivariantReplacement

/-! The concrete original-ambient gamma-product comparison, including the
outer-trivial case. The fixed predicate abbreviates only the full checked
output, retaining actual characters, roots, operators and quotient map. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPairComparison

open ModularRep
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierFaithfulCenterEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement
  (collapsedProductEquiv collapsedProductRepresentation collapsedProduct_affords)

universe u

theorem innerInverseOpHom_surjective_of_outer_card_one
    {G : Type u} [Group G]
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1) :
    Function.Surjective (RepresentationWeight.innerInverseOpHom (G := G)) := by
  let : Subsingleton (LiteralOuterQuotient G) := (Nat.card_eq_one_iff_unique.mp hOuter).1
  intro a
  have hq : QuotientGroup.mk'
      (RepresentationWeight.innerInverseOpHom (G := G)).range a = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff a).mp hq

theorem originalAmbient_surjective_of_outer_card_one
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [Group G] [Finite G]
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1) :
    Function.Surjective (innerEmbedding iota phi) := by
  intro a
  obtain ⟨x, hx⟩ := innerInverseOpHom_surjective_of_outer_card_one hOuter a.1
  exact ⟨x, Subtype.ext hx⟩

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (nu : Subgroup.center G →* kˣ) (phi : ScalarBrauerSector iota nu)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)

local notation "B" => (⊤ : Subgroup G)
local notation "Z" => Subgroup.center G
local notation "N" => Subgroup.normalizer (V.subgroup : Set G)
local notation "L" => (⊤ : Subgroup N)
local notation "ZL" => Subgroup.comap (Subgroup.subtype N) Z
local notation "eG" => (Subgroup.topEquiv.symm : G ≃* B)
local notation "eN" => (Subgroup.topEquiv.symm : N ≃* L)
local notation "rG" => PrimeRegularRootEmbedding.alongMulEquiv iota eG
local notation "rL" => PrimeRegularRootEmbedding.alongMulEquiv source.normalizerRoot eN
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG (Subtype.val phi)
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer
local notation "rhoG" => globalRepresentation iota nu phi
local notation "rhoL" => localRepresentation iota V source
local notation "qE" => topQuotientEquiv (Subgroup.subtype N)

/-- Fixed concrete output, never a source premise. -/
def OriginalPairComparison : Prop :=
  Function.Surjective (innerEmbedding iota phi.1) ∧
  Subgroup.centralizer (B : Set G) = Z ∧
  B ⊔ Z = B ∧ L ⊔ ZL = L ∧
  (∀ a : G, IrreducibleBrauerCharacter.twist (gammaRoot iota)
    (gamma iota nu) (MulAut.conjNormal a) = gamma iota nu) ∧
  (∀ c : PrimeRegularElement (G := Z) p,
    (gamma iota nu).1 c = (gammaRoot iota).lift (nu c.1 : k)) ∧
  ∃ (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL),
    GlobalGammaProduct iota nu phi MG ∧
    LocalGammaProduct iota nu V source ML ∧
    MG.factorSet = ScalarFactorSet.trivial ∧
    ML.factorSet = ScalarFactorSet.trivial ∧
    (∀ n : N, qE (QuotientGroup.mk' L n) = QuotientGroup.mk' B n.1) ∧
    ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
    ScalarFactorSet.Cohomologous ML.factorSet (ScalarFactorSet.pullback qE MG.factorSet)

theorem faithful_pair_comparison
    (hnu : Function.Injective nu)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (tau : MulAut G)
    (hcard : Nat.card (Subgroup.center G) = 3 ∨
      Nat.card (Subgroup.center G) = 4 ∨ Nat.card (Subgroup.center G) = 6)
    (hinverts : ∀ z : Subgroup.center G, tau (z : G) = (z : G)⁻¹)
    (hlocal : ∀ z : Subgroup.center G,
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
        (Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
          (nu z : k) • 1) : OriginalPairComparison iota nu phi V source :=
  faithful_center_equivariant_replacement iota nu phi V source hnu hOuter tau hcard hinverts hlocal

/-- With trivial actual outer quotient, the original group is already
the ambient for every same-scalar pair. The centre is retained without
faithfulness, size or inversion assumptions. -/
theorem outer_trivial_pair_comparison
    (hOuter : Nat.card (LiteralOuterQuotient G) = 1)
    (hlocal : ∀ z : Subgroup.center G,
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
        (Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
          (nu z : k) • 1) : OriginalPairComparison iota nu phi V source := by
  refine ⟨originalAmbient_surjective_of_outer_card_one iota phi.1 hOuter,
    originalAmbient_centralizer, top_sup_eq _, top_sup_eq _,
    gamma_fixed iota nu, gamma_value iota nu, ?_⟩
  have hG : Representation.IsIrreducible rhoG :=
    topRestriction_irreducible _ (Classical.choose_spec phi.1.2).1
  have hL : Representation.IsIrreducible rhoL :=
    topRestriction_irreducible _ (Classical.choose_spec source.localBrauer.2).1
  have hcharG := global_affords iota nu phi
  have hcharL := local_affords iota V source
  refine ⟨topModel (chosenIBrRepresentation iota phi.1).ρ,
    topModel (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ,
    ⟨hG, hcharG, collapsedProduct_affords B Z le_top rG phiG rhoG hcharG,
      global_model_product iota nu phi _⟩,
    ⟨hL, hcharL, collapsedProduct_affords L ZL le_top rL phiL rhoL hcharL,
      local_model_product iota nu V source hlocal _⟩,
    rfl, rfl, topQuotientEquiv_mk (Subgroup.subtype N), rfl,
    ScalarFactorSet.trivial_cohomologous_pullback_trivial qE⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPairComparison


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
