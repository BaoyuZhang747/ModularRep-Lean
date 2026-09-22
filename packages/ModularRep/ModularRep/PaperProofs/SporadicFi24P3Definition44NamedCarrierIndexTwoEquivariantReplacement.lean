import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIndexTwoBrauerExtension

/-! Actual global and local extensions derived from their quotient cardinal bounds. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIndexTwoEquivariantReplacement

open SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierIndexTwoBrauerExtension

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance
  (stableNormalizerAut stableNormalizerAut_coe inflated_ordinary_fixed_of_isomorphic)

universe u

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G)
variable (Omega : IBr iota → ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (chi : IBr iota),
  Omega (a • chi) = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := p) (K := K) (G := G)) = Omega phi)

include Omega hOmega hclass

variable (source : CanonicalRawReduction iota V)
variable (hcenter : Subgroup.center G = ⊥)

local notation "A" => ActualAutAmbient iota phi
local notation "B" => actualBase iota phi
local notation "D" => embeddedNormalizer (innerEmbedding iota phi) V.subgroup
local notation "L" => embeddedLocalBase (innerEmbedding iota phi) V.subgroup
local notation "eG" => actualBaseEquiv iota phi hcenter
local notation "eN" => normalizerBaseEquiv (innerEmbedding iota phi)
  (innerEmbedding_injective iota phi hcenter) V.subgroup
local notation "rG" => iota.alongMulEquiv eG
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv
  source.normalizerRoot eN source.localBrauer
local notation "qE" => matchedLocalQuotientEquiv iota phi V Omega hOmega hclass

/-- The centreless, outer-order-two deduction in `lem:equivariant-replacement`.
For every matched pair of the arbitrary supplied equivariant map, the two
actual characters have associated models with the same trivial factor class
under the natural quotient identification. The final coboundary is constant one.
Navarro 8.15 identifies these character-dependent classes independently of the
choice of associated operators. -/
theorem centerless_equivariant_replacement_of_index_two
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2) :
    Subgroup.centralizer (B : Set A) = ⊥ ∧
    ∃ (WG : FDRep k B) (WL : FDRep k L)
      (MG : AssociatedProjectiveModel B WG.ρ)
      (ML : AssociatedProjectiveModel L WL.ρ),
      Representation.IsIrreducible WG.ρ ∧
      phiG.1 = Representation.brauerCharacterOfRootEmbedding WG.ρ rG ∧
      Representation.IsIrreducible WL.ρ ∧
      phiL.1 = Representation.brauerCharacterOfRootEmbedding WL.ρ rL ∧
      MG.factorSet = ScalarFactorSet.trivial ∧
      ML.factorSet = ScalarFactorSet.trivial ∧
      (∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.1) ∧
      ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
      ScalarFactorSet.Cohomologous ML.factorSet
        (ScalarFactorSet.pullback qE MG.factorSet) := by
  refine ⟨actualBase_centralizer_eq_bot iota phi hcenter, ?_⟩
  have hcardG : Nat.card (A ⧸ B) ≤ 2 := actual_quotient_card_le_two iota phi hOuter
  have hcardL : Nat.card (D ⧸ L) ≤ 2 := (Nat.card_congr (qE).toEquiv).le.trans hcardG
  obtain ⟨WG, hWG, hcharG, ⟨EG⟩⟩ :=
    exists_extension_realisation_of_ibr_fixed_quotient_card_le_two
      rG phiG hcardG (actualGlobalBaseFixed iota phi hcenter)
  obtain ⟨WL, hWL, hcharL, ⟨EL⟩⟩ :=
    exists_extension_realisation_of_ibr_fixed_quotient_card_le_two
      rL phiL hcardL
      (actualLocalBrauer_fixed_of_equivariant_match
        iota phi V Omega hOmega hclass source hcenter)
  refine ⟨WG, WL, AssociatedProjectiveModel.ofExtension EG,
    AssociatedProjectiveModel.ofExtension EL,
    hWG, hcharG, hWL, hcharL, rfl, rfl, ?_, rfl, ?_⟩
  · exact matchedLocalQuotientEquiv_mk iota phi V Omega hOmega hclass
  · exact ScalarFactorSet.trivial_cohomologous_pullback_trivial qE

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIndexTwoEquivariantReplacement


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
