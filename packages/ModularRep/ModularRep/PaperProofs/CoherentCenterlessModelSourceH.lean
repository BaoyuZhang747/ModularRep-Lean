import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessModelSourceH
import ModularRep.PaperProofs.CoherentModelBlockWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessAD3Assembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEmbeddedBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientModelBlockWitnesses

/-! Extension and block conditions for the same representation models, with compatible global, local and intermediate root correspondences. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.CoherentCenterlessModelSourceH

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement
  (collapsedProductEquiv collapsedProductRepresentation collapsedProduct_affords)
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierCenterlessCentralProduct
open SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
open SporadicFi24P3Definition44NamedCarrierSamePairQOneModelRows
open SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows
open SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups
open SporadicFi24P3Definition44NamedCarrierCentralQuotientModelBlockWitnesses
open SporadicFi24P3Definition44NamedCarrierProductModelTransport
open SporadicFi24P3Definition44NamedCarrierCentralLift (ordinaryIrr_apply_eq_one_of_subsingleton)
open SporadicFi24P3Definition44Clause3ACWindow (trivialIBr trivialIBr_apply trivialIBr_fixed)

open ModularRep.PaperProofs.CoherentModelBlockWitnesses

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
local instance ambientFintype : Fintype (ActualAutAmbient iota phi) := Fintype.ofFinite _

variable (hcenter : Subgroup.center G = ⊥)
include hcenter
local notation "A" => ActualAutAmbient iota phi
local notation "B" => actualBase iota phi
local notation "C" => Subgroup.centralizer (B : Set A)

variable (V : CharacterWeight p K G)
local notation "D" => embeddedNormalizer (innerEmbedding iota phi) V.subgroup
local notation "L" => embeddedLocalBase (innerEmbedding iota phi) V.subgroup
local notation "CD" => Subgroup.comap (Subgroup.subtype D) C

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

def CoherentCenterlessProductSourceHComparison : Prop :=
  C = ⊥ ∧ B ⊔ C = B ∧ L ⊔ CD = L ∧
  ∃ (WG : FDRep k B) (WL : FDRep k L)
    (MG : AssociatedProjectiveModel B WG.ρ) (ML : AssociatedProjectiveModel L WL.ρ)
    (hMG : MG.factorSet = ScalarFactorSet.trivial) (hML : ML.factorSet = ScalarFactorSet.trivial),
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
      (ScalarFactorSet.pullback qP (modelOnEqualBase B (B ⊔ C) hBG WG.ρ MG).factorSet) ∧
    (V.subgroup ≠ ⊥ → CoherentModelPairSourceHBlocks B D rG rL phiG phiL
      WG.ρ WL.ρ MG ML hMG hML) ∧
    ∀ hV : V.subgroup = ⊥,
      CoherentCommonModelSourceHBlocks iota phi V source B eG D
        (embeddedNormalizer_eq_top (innerEmbedding iota phi) V.subgroup hV)
        L eN WG.ρ MG hMG

/-- The strengthened comparison contains every original conclusion. -/
theorem CoherentCenterlessProductSourceHComparison.forget
    (h : CoherentCenterlessProductSourceHComparison iota phi hcenter V Omega hOmega hclass source) :
    SporadicFi24P3Definition44NamedCarrierCenterlessModelSourceH.CenterlessProductSourceHComparison
      iota phi hcenter V Omega hOmega hclass source := by
  obtain ⟨hC, hBG', hBL', WG, WL, MG, ML, hMG, hML, hWG, hG, hWL, hL,
    hMG', hML', hq, hf, hc, hGP, hLP, hGO, hLO, hqp, hfp, hcp, hpositive, hcommon⟩ := h
  refine ⟨hC, hBG', hBL', WG, WL, MG, ML, hMG, hML, hWG, hG, hWL, hL,
    hMG', hML', hq, hf, hc, hGP, hLP, hGO, hLO, hqp, hfp, hcp, ?_, ?_⟩
  · intro hV
    exact (hpositive hV).forget B D rG rL phiG phiL WG.ρ WL.ρ MG ML hMG hML
  · intro hV
    exact (hcommon hV).forget iota phi V source B eG D
      (embeddedNormalizer_eq_top (innerEmbedding iota phi) V.subgroup hV) L eN WG.ρ MG hMG

end ModularRep.PaperProofs.CoherentCenterlessModelSourceH

/-
Part of the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
The results use the explicit assumptions described in the formalisation report.
-/
