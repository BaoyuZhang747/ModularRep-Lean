import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierProductModelTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralLift
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralRestrictionFormula
import ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow

/-! Actual centreless centralizer character and central-product models.
Every affording representation, operator and coboundary is retained. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessCentralProduct

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement
  (collapsedProductEquiv collapsedProductRepresentation collapsedProduct_affords)
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierProductModelTransport
open SporadicFi24P3Definition44NamedCarrierCentralLift (ordinaryIrr_apply_eq_one_of_subsingleton)
open SporadicFi24P3Definition44Clause3ACWindow (trivialIBr trivialIBr_apply trivialIBr_fixed)

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (hcenter : Subgroup.center G = ⊥)
include hcenter
local notation "A" => ActualAutAmbient iota phi
local notation "B" => actualBase iota phi
local notation "C" => Subgroup.centralizer (B : Set A)

theorem centralizer_eq_bot : C = ⊥ := actualBase_centralizer_eq_bot iota phi hcenter

theorem centralizer_element_eq_one (c : C) : (c : A) = 1 :=
  (Subgroup.eq_bot_iff_forall C).mp (centralizer_eq_bot iota phi hcenter) c.val c.property

theorem center_map_eq_centralizer : (Subgroup.center G).map (innerEmbedding iota phi) = C := by
  rw [hcenter, Subgroup.map_bot, centralizer_eq_bot iota phi hcenter]

def centerEquiv : Subgroup.center G ≃* C :=
  ((Subgroup.center G).equivMapOfInjective (innerEmbedding iota phi)
    (innerEmbedding_injective iota phi hcenter)).trans
      (MulEquiv.subgroupCongr (center_map_eq_centralizer iota phi hcenter))

theorem centerEquiv_ambient (z : Subgroup.center G) :
    (centerEquiv iota phi hcenter z : A) = innerEmbedding iota phi z.val := rfl

def gammaRoot : PrimeRegularRootEmbedding p k K C :=
  (subgroupRoot iota (Subgroup.center G)).alongMulEquiv (centerEquiv iota phi hcenter)

def gamma : IBr (gammaRoot iota phi hcenter) := trivialIBr (gammaRoot iota phi hcenter)

theorem gamma_value (c : PrimeRegularElement (G := C) p) :
    (gamma iota phi hcenter).val c = 1 := trivialIBr_apply _ c

theorem gamma_fixed (a : A) :
    IrreducibleBrauerCharacter.twist (gammaRoot iota phi hcenter)
      (gamma iota phi hcenter) (MulAut.conjNormal a) = gamma iota phi hcenter :=
  trivialIBr_fixed _ _

theorem centralizer_commutes (c d : C) : c * d = d * c := by
  apply Subtype.ext
  simp only [centralizer_element_eq_one iota phi hcenter]

theorem centralizer_le_base : C ≤ B := by
  rw [centralizer_eq_bot iota phi hcenter]
  exact bot_le

theorem centralizer_central : C ≤ Subgroup.center A := by
  rw [centralizer_eq_bot iota phi hcenter]
  exact bot_le

omit [Fintype G] in
theorem lambda_value (lam : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G))
    (z : Subgroup.center G) : lam z = 1 := by
  let : Subsingleton (Subgroup.center G) := by rw [hcenter]; infer_instance
  exact ordinaryIrr_apply_eq_one_of_subsingleton lam z

omit [CharZero K] [Fintype G] in
theorem lambda_faithful (lam : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G)) :
    Function.Injective lam := by
  intro z t _
  apply Subtype.ext
  exact ((Subgroup.eq_bot_iff_forall _).mp hcenter z.val z.property).trans
    ((Subgroup.eq_bot_iff_forall _).mp hcenter t.val t.property).symm

theorem gamma_over_lambda (lam : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G))
    (z : PrimeRegularElement (G := Subgroup.center G) p) :
    (gamma iota phi hcenter).val
      (PrimeRegularElement.map (centerEquiv iota phi hcenter).toMonoidHom z) = lam z.val := by
  rw [gamma_value, lambda_value hcenter lam z.val]

theorem global_over_lambda (lam : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G))
    (z : PrimeRegularElement (G := Subgroup.center G) p) :
    phi.val (PrimeRegularElement.map (Subgroup.center G).subtype z) =
      phi.val ⟨1, isPrimeRegular_one⟩ * lam z.val := by
  have hz : z.val.val = 1 := (Subgroup.eq_bot_iff_forall _).mp hcenter z.val.val z.val.property
  have he : PrimeRegularElement.map (Subgroup.center G).subtype z =
      (⟨1, isPrimeRegular_one⟩ : PrimeRegularElement (G := G) p) := Subtype.ext hz
  rw [he, lambda_value hcenter lam z.val, mul_one]

variable (V : CharacterWeight p K G)
local notation "D" => embeddedNormalizer (innerEmbedding iota phi) V.subgroup
local notation "L" => embeddedLocalBase (innerEmbedding iota phi) V.subgroup
local notation "CD" => Subgroup.comap (Subgroup.subtype D) C

theorem local_centralizer_eq_bot : CD = ⊥ := by
  rw [centralizer_eq_bot iota phi hcenter]
  change (Subgroup.subtype D).ker = ⊥
  exact (MonoidHom.ker_eq_bot_iff (Subgroup.subtype D)).mpr (Subgroup.subtype_injective D)

theorem local_centralizer_le_base : CD ≤ L := by
  rw [local_centralizer_eq_bot iota phi hcenter V]
  exact bot_le

theorem local_product_image : (L ⊔ CD).map (D).subtype = (L).map (D).subtype ⊔ C := by
  rw [Subgroup.map_sup, local_centralizer_eq_bot iota phi hcenter V,
    Subgroup.map_bot, centralizer_eq_bot iota phi hcenter]

theorem ordinary_over_lambda
    (lam : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G)) (z : Subgroup.center G) :
    centralRestriction V z = V.localCharacter 1 * lam z := by
  have hz : z.val = 1 := (Subgroup.eq_bot_iff_forall _).mp hcenter z.val z.property
  rw [lambda_value hcenter lam z, mul_one]
  change V.localCharacter (QuotientGroup.mk
    (⟨z.val, Subgroup.center_le_normalizer (V.subgroup : Set G) z.property⟩ :
      Subgroup.normalizer (V.subgroup : Set G))) = V.localCharacter 1
  have hn : (⟨z.val, Subgroup.center_le_normalizer (V.subgroup : Set G) z.property⟩ :
      Subgroup.normalizer (V.subgroup : Set G)) = 1 := Subtype.ext hz
  rw [hn]
  rfl

/-- The actual centralizer and its irreducible gamma over the original lambda. -/
def CenterlessGammaData (lam : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G)) : Prop :=
  (∀ c d : C, c * d = d * c) ∧ C ≤ Subgroup.center A ∧
  (L ⊔ CD).map (Subgroup.subtype D) = (L).map (Subgroup.subtype D) ⊔ C ∧
  Function.Injective lam ∧
  (∀ a : A, IrreducibleBrauerCharacter.twist (gammaRoot iota phi hcenter)
    (gamma iota phi hcenter) (MulAut.conjNormal a) = gamma iota phi hcenter) ∧
  (∀ z : PrimeRegularElement (G := Subgroup.center G) p,
    (gamma iota phi hcenter).val
      (PrimeRegularElement.map (centerEquiv iota phi hcenter).toMonoidHom z) = lam z.val) ∧
  (∀ z : PrimeRegularElement (G := Subgroup.center G) p,
    phi.val (PrimeRegularElement.map (Subgroup.center G).subtype z) =
      phi.val ⟨1, isPrimeRegular_one⟩ * lam z.val) ∧
  ∀ z : Subgroup.center G, centralRestriction V z = V.localCharacter 1 * lam z

theorem centerless_gamma_data (lam : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center G)) :
    CenterlessGammaData iota phi hcenter V lam :=
  ⟨centralizer_commutes iota phi hcenter, centralizer_central iota phi hcenter,
    local_product_image iota phi hcenter V, lambda_faithful hcenter lam,
    gamma_fixed iota phi hcenter, gamma_over_lambda iota phi hcenter lam,
    global_over_lambda iota phi hcenter lam, ordinary_over_lambda hcenter V lam⟩

variable (Omega : IBr iota → ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (chi : IBr iota), Omega (a • chi) = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = Omega phi)
variable (source : CanonicalRawReduction iota V)
local notation "eG" => actualBaseEquiv iota phi hcenter
local notation "eN" => normalizerBaseEquiv (innerEmbedding iota phi)
  (innerEmbedding_injective iota phi hcenter) V.subgroup
local notation "rG" => iota.alongMulEquiv eG
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer
local notation "hBG" => sup_eq_left.mpr (centralizer_le_base iota phi hcenter)
local notation "hBL" => sup_eq_left.mpr (local_centralizer_le_base iota phi hcenter V)
local notation "qE" => matchedLocalQuotientEquiv iota phi V Omega hOmega hclass
local notation "qP" => productQuotientEquiv B (B ⊔ C) L (L ⊔ CD) hBG hBL qE

/-- Full retained comparison, now with models on the actual product denominators. -/
def CenterlessProductComparison : Prop :=
  C = ⊥ ∧ B ⊔ C = B ∧ L ⊔ CD = L ∧
  ∃ (WG : FDRep k B) (WL : FDRep k L)
    (MG : AssociatedProjectiveModel B WG.ρ) (ML : AssociatedProjectiveModel L WL.ρ),
    Representation.IsIrreducible WG.ρ ∧ (phiG).val = Representation.brauerCharacterOfRootEmbedding WG.ρ rG ∧
    Representation.IsIrreducible WL.ρ ∧ (phiL).val = Representation.brauerCharacterOfRootEmbedding WL.ρ rL ∧
    MG.factorSet = ScalarFactorSet.trivial ∧ ML.factorSet = ScalarFactorSet.trivial ∧
    (∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.val) ∧
    ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
    ScalarFactorSet.Cohomologous ML.factorSet (ScalarFactorSet.pullback qE MG.factorSet) ∧
    (IrreducibleBrauerCharacter.alongMulEquiv rG
      (collapsedProductEquiv B C (centralizer_le_base iota phi hcenter)).symm phiG).val =
      (representationOnEqualBase B (B ⊔ C) hBG WG.ρ).brauerCharacterOfRootEmbedding
        ((rG).alongMulEquiv (collapsedProductEquiv B C (centralizer_le_base iota phi hcenter)).symm) ∧
    (IrreducibleBrauerCharacter.alongMulEquiv rL
      (collapsedProductEquiv L CD (local_centralizer_le_base iota phi hcenter V)).symm phiL).val =
      (representationOnEqualBase L (L ⊔ CD) hBL WL.ρ).brauerCharacterOfRootEmbedding
        ((rL).alongMulEquiv (collapsedProductEquiv L CD (local_centralizer_le_base iota phi hcenter V)).symm) ∧
    (∀ (b : B) (c : C), MG.operator (b.val * c.val) = WG.ρ b * (1 : k) • 1) ∧
    (∀ (l : L) (c : CD), ML.operator (l.val * c.val) = WL.ρ l * (1 : k) • 1) ∧
    (∀ d : D, qP (QuotientGroup.mk' (L ⊔ CD) d) = QuotientGroup.mk' (B ⊔ C) d.val) ∧
    (modelOnEqualBase L (L ⊔ CD) hBL WL.ρ ML).factorSet =
      ScalarFactorSet.pullback qP (modelOnEqualBase B (B ⊔ C) hBG WG.ρ MG).factorSet ∧
    ScalarFactorSet.Cohomologous (modelOnEqualBase L (L ⊔ CD) hBL WL.ρ ML).factorSet
      (ScalarFactorSet.pullback qP (modelOnEqualBase B (B ⊔ C) hBG WG.ρ MG).factorSet)

theorem centerless_product_comparison
    (hOld : CenterlessPairComparison iota phi V Omega hOmega hclass source hcenter) :
    CenterlessProductComparison iota phi hcenter V Omega hOmega hclass source := by
  rcases hOld with ⟨hC, WG, WL, MG, ML, hWG, hG, hWL, hL, hMG, hML, hq, hf, hc⟩
  refine ⟨hC, hBG, hBL, WG, WL, MG, ML, hWG, hG, hWL, hL, hMG, hML, hq, hf, hc,
    collapsedProduct_affords B C (centralizer_le_base iota phi hcenter) rG phiG WG.ρ hG,
    collapsedProduct_affords L CD (local_centralizer_le_base iota phi hcenter V) rL phiL WL.ρ hL,
    ?_, ?_, productQuotientEquiv_mk B (B ⊔ C) L (L ⊔ CD) hBG hBL qE (D).subtype hq,
    product_factor_equality B (B ⊔ C) L (L ⊔ CD) hBG hBL WG.ρ WL.ρ MG ML qE hf,
    product_cohomology B (B ⊔ C) L (L ⊔ CD) hBG hBL WG.ρ WL.ρ MG ML qE hc⟩
  · intro b c
    rw [centralizer_element_eq_one iota phi hcenter c, mul_one, one_smul, mul_one]
    exact MG.restriction b
  · intro l c
    have hc1 : c.val = 1 :=
      (Subgroup.eq_bot_iff_forall CD).mp (local_centralizer_eq_bot iota phi hcenter V) c.val c.property
    rw [hc1, mul_one, one_smul, mul_one]
    exact ML.restriction l

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessCentralProduct


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
