import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPairComparison
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierProductModelTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda

/-! The original central character and actual product-denominator models,
enriching the SAME centre-two and original-G comparison witnesses. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralProductComparisons

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierProductModelTransport
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
open SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
open SporadicFi24P3Definition44NamedCarrierOriginalPairComparison

universe u

theorem local_product_image_of_le {A : Type u} [Group A]
    (D : Subgroup A) (L : Subgroup D) (C : Subgroup A) (hCD : C ≤ D) :
    (L ⊔ C.comap D.subtype).map D.subtype = L.map D.subtype ⊔ C := by
  have hCrange : C ≤ D.subtype.range := hCD.trans_eq D.range_subtype.symm
  rw [Subgroup.map_sup, Subgroup.map_comap_eq_self hCrange]

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)

section CentralTwo
open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement
variable {T C : Type u} [Group T] [Group C]
variable (nu : Subgroup.center G →* kˣ) (phi : ScalarBrauerSector iota nu)
variable (E : GroupExtension G T C) (hC : Nat.card C = 2)
variable (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
variable (hAut : Function.Surjective E.conjAct)
variable (hZ : Nat.card (Subgroup.center G) = 2)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
variable (Omega : ScalarBrauerSector iota nu → ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (chi chi' : ScalarBrauerSector iota nu),
  chi'.1 = a • chi.1 → Omega chi' = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := p) (K := K) (G := G)) = Omega phi)
local notation "A" => brauerAmbient E iota (Subtype.val phi)
local notation "i" => brauerEmbedding E iota (Subtype.val phi)
local notation "B" => MonoidHom.range i
local notation "Z" => Subgroup.centralizer (B : Set A)
local notation "D" => embeddedNormalizer i V.subgroup
local notation "L" => embeddedLocalBase i V.subgroup
local notation "rhoG" => globalRepresentation iota nu phi E
local notation "rhoL" => localRepresentation iota nu phi E V source
local notation "rZ" => gammaRoot iota nu phi E hC hOuter hAut
local notation "gam" => gamma iota nu phi E hC hOuter hAut
local notation "nuZ" => gammaScalar iota nu phi E hC hOuter hAut
local notation "ZL" => Subgroup.comap (Subgroup.subtype D) Z
local notation "qE" => matchedLocalQuotientEquiv iota nu phi V Omega hOmega hclass E

local notation "hBG" => sup_eq_left.mpr (centralizer_le_base iota nu phi E hC hOuter hAut)
local notation "hBL" => local_product_denominator iota nu phi E hC hOuter hAut V

/-- All original witnesses, with the ordinary lambda and actual product models. -/
def CentralTwoProductComparison : Prop :=
    letI : Finite T := extension_finite E hC
    Function.Surjective (brauerAction E iota phi.1) ∧
    (∀ a : A, ∃ d : D, ∃ x : G, a = d.1 * i x) ∧
    Z ≤ Subgroup.center A ∧
    B ⊔ Z = B ∧ L ⊔ ZL = L ∧
    (∀ a : A, IrreducibleBrauerCharacter.twist rZ gam (MulAut.conjNormal a) = gam) ∧
    (∀ c : PrimeRegularElement (G := Z) p, (gam).1 c = (rZ).lift (nuZ c.1 : k)) ∧
    Function.Injective (ordinaryCentralLambda iota nu) ∧
    (∀ c d : Z, c * d = d * c) ∧
    (∀ z : PrimeRegularElement (G := Subgroup.center G) p,
      (gam).val (PrimeRegularElement.map
        (centerEquiv iota nu phi E hC hOuter hAut).toMonoidHom z) =
          ordinaryCentralLambda iota nu z.val) ∧
    (∀ z : PrimeRegularElement (G := Subgroup.center G) p,
      phi.val.val (PrimeRegularElement.map (Subgroup.center G).subtype z) =
        phi.val.val ⟨1, isPrimeRegular_one⟩ * ordinaryCentralLambda iota nu z.val) ∧
    (L ⊔ ZL).map (Subgroup.subtype D) = (L).map (Subgroup.subtype D) ⊔ Z ∧
    ∃ (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL),
      GlobalGammaProduct iota nu phi E hC hOuter hAut MG ∧
      LocalGammaProduct iota nu phi E hC hOuter hAut hZ V source ML ∧
      MG.factorSet = ScalarFactorSet.trivial ∧
      ML.factorSet = ScalarFactorSet.trivial ∧
      (∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.1) ∧
      ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
      ScalarFactorSet.Cohomologous ML.factorSet
        (ScalarFactorSet.pullback qE MG.factorSet) ∧
      ProductModelOutput B (B ⊔ Z) L (L ⊔ ZL) hBG hBL rhoG rhoL MG ML qE (Subgroup.subtype D)

theorem central_two_product_comparison (hnu : Function.Injective nu)
    (hOld : CentralTwoPairComparison iota nu phi E hC hOuter hAut hZ V source Omega hOmega hclass) :
    CentralTwoProductComparison iota nu phi E hC hOuter hAut hZ V source Omega hOmega hclass := by
  let : Finite T := extension_finite E hC
  rcases hOld with ⟨hsurj, hfac, hcentral, hBG0, hBL0, hfixed, hval,
    MG, ML, hG, hL, hMG, hML, hq, hf, hc⟩
  refine ⟨hsurj, hfac, hcentral, hBG0, hBL0, hfixed, hval,
    ordinaryCentralLambda_faithful iota nu hnu, ?_, ?_,
    scalarBrauer_lies_over_ordinaryCentralLambda iota nu phi,
    local_product_image_of_le D L Z (centralizer_le_normalizer iota nu phi E hC hOuter hAut hZ V),
    MG, ML, hG, hL, hMG, hML, hq, hf, hc,
    product_model_output B (B ⊔ Z) L (L ⊔ ZL) hBG hBL rhoG rhoL MG ML qE
      (Subgroup.subtype D) hq hf hc⟩
  · intro c d
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hcentral c.property) d.val).symm
  · intro z
    rw [gamma_value]
    change ((subgroupRoot iota (Subgroup.center G)).alongMulEquiv
      (centerEquiv iota nu phi E hC hOuter hAut)).lift
        (nu ((centerEquiv iota nu phi E hC hOuter hAut).symm
          (centerEquiv iota nu phi E hC hOuter hAut z.val)) : k) =
            ordinaryCentralLambda iota nu z.val
    rw [MulEquiv.symm_apply_apply, PrimeRegularRootEmbedding.alongMulEquiv_lift]
    exact (ordinaryCentralLambda_subgroup_value iota nu z.val).symm

end CentralTwo

section Original
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierFaithfulCenterEquivariantReplacement

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

local notation "hBG" => top_sup_eq Z
local notation "hBL" => top_sup_eq ZL

/-- The original-G comparison on the same models and actual products. -/
def OriginalProductComparison : Prop :=
  Function.Surjective (innerEmbedding iota phi.1) ∧
  Subgroup.centralizer (B : Set G) = Z ∧
  B ⊔ Z = B ∧ L ⊔ ZL = L ∧
  (∀ a : G, IrreducibleBrauerCharacter.twist (gammaRoot iota)
    (gamma iota nu) (MulAut.conjNormal a) = gamma iota nu) ∧
  (∀ c : PrimeRegularElement (G := Z) p,
    (gamma iota nu).1 c = (gammaRoot iota).lift (nu c.1 : k)) ∧
  Function.Injective (ordinaryCentralLambda iota nu) ∧
  (∀ c d : Z, c * d = d * c) ∧
  (∀ z : PrimeRegularElement (G := Z) p,
    (gamma iota nu).val z = ordinaryCentralLambda iota nu z.val) ∧
  (∀ z : PrimeRegularElement (G := Z) p,
    phi.val.val (PrimeRegularElement.map (Subgroup.center G).subtype z) =
      phi.val.val ⟨1, isPrimeRegular_one⟩ * ordinaryCentralLambda iota nu z.val) ∧
  (L ⊔ ZL).map (Subgroup.subtype N) = (L).map (Subgroup.subtype N) ⊔ Z ∧
  ∃ (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL),
    GlobalGammaProduct iota nu phi MG ∧
    LocalGammaProduct iota nu V source ML ∧
    MG.factorSet = ScalarFactorSet.trivial ∧
    ML.factorSet = ScalarFactorSet.trivial ∧
    (∀ n : N, qE (QuotientGroup.mk' L n) = QuotientGroup.mk' B n.1) ∧
    ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
    ScalarFactorSet.Cohomologous ML.factorSet (ScalarFactorSet.pullback qE MG.factorSet) ∧
    ProductModelOutput B (B ⊔ Z) L (L ⊔ ZL) hBG hBL rhoG rhoL MG ML qE (Subgroup.subtype N)

theorem original_product_comparison (hnu : Function.Injective nu)
    (hOld : OriginalPairComparison iota nu phi V source) :
    OriginalProductComparison iota nu phi V source := by
  rcases hOld with ⟨hsurj, hcentralizer, hBG0, hBL0, hfixed, hval,
    MG, ML, hG, hL, hMG, hML, hq, hf, hc⟩
  refine ⟨hsurj, hcentralizer, hBG0, hBL0, hfixed, hval,
    ordinaryCentralLambda_faithful iota nu hnu, ?_, ?_,
    scalarBrauer_lies_over_ordinaryCentralLambda iota nu phi,
    local_product_image_of_le N L Z (Subgroup.center_le_normalizer (V.subgroup : Set G)),
    MG, ML, hG, hL, hMG, hML, hq, hf, hc,
    product_model_output B (B ⊔ Z) L (L ⊔ ZL) hBG hBL rhoG rhoL MG ML qE
      (Subgroup.subtype N) hq hf hc⟩
  · intro c d
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp c.property d.val).symm
  · intro z
    rw [gamma_value]
    exact (ordinaryCentralLambda_subgroup_value iota nu z.val).symm

end Original
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralProductComparisons


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
