import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFactorOneExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement

/-! The same centreless matched models give actual representation extensions.
The local pair and factor-set comparison are retained literally. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedModels

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

open SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)

section Centerless
open SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
variable (phi : IBr iota) (V : CharacterWeight p K G)
variable (Omega : IBr iota → ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (chi : IBr iota),
  Omega (a • chi) = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := p) (K := K) (G := G)) = Omega phi)
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

local notation "C" => Subgroup.centralizer (B : Set A)
local notation "CL" => Subgroup.comap (Subgroup.subtype D) C

def ReducedPairModelsOutput : Prop :=
  C = ⊥ ∧
  ∃ (WG : FDRep k B) (WL : FDRep k L)
    (MG : AssociatedProjectiveModel B WG.ρ)
    (ML : AssociatedProjectiveModel L WL.ρ)
    (hMG : MG.factorSet = ScalarFactorSet.trivial)
    (hML : ML.factorSet = ScalarFactorSet.trivial),
    Representation.IsIrreducible WG.ρ ∧
    (phiG).val = Representation.brauerCharacterOfRootEmbedding WG.ρ rG ∧
    Representation.IsIrreducible WL.ρ ∧
    (phiL).val = Representation.brauerCharacterOfRootEmbedding WL.ρ rL ∧
    (∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.val) ∧
    ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
    ScalarFactorSet.Cohomologous ML.factorSet (ScalarFactorSet.pullback qE MG.factorSet) ∧
    (∀ (b : B) (c : C), MG.operator (b.val * c.val) = WG.ρ b) ∧
    (∀ (l : L) (c : CL), ML.operator (l.val * c.val) = WL.ρ l) ∧
    (∀ a : A, (extensionOfFactorOne MG hMG).representation a = MG.operator a) ∧
    (∀ d : D, (extensionOfFactorOne ML hML).representation d = ML.operator d) ∧
    (∀ b : B, (extensionOfFactorOne MG hMG).representation b = WG.ρ b) ∧
    (∀ l : L, (extensionOfFactorOne ML hML).representation l = WL.ρ l) ∧
    Representation.IsIrreducible (extensionOfFactorOne MG hMG).representation ∧
    Representation.IsIrreducible (extensionOfFactorOne ML hML).representation

theorem reduced_pair_models_of_comparison
    (hComparison : CenterlessPairComparison iota phi V Omega hOmega hclass source hcenter) :
    ReducedPairModelsOutput iota phi V Omega hOmega hclass source hcenter := by
  obtain ⟨hC, WG, WL, MG, ML, hIG, hAG, hIL, hAL, hMG, hML, hq, hf, hc⟩ := hComparison
  refine ⟨hC, WG, WL, MG, ML, hMG, hML, hIG, hAG, hIL, hAL, hq, hf, hc, ?_, ?_,
    extensionOfFactorOne_operator MG hMG, extensionOfFactorOne_operator ML hML,
    MG.restriction, ML.restriction,
    (extensionOfFactorOne MG hMG).representation_isIrreducible hIG,
    (extensionOfFactorOne ML hML).representation_isIrreducible hIL⟩
  · intro b c
    have hc1 : c.val = 1 := (Subgroup.eq_bot_iff_forall C).mp hC c.val c.property
    rw [hc1, mul_one]
    exact MG.restriction b
  · intro l c
    have hc1 : c.val = 1 := by
      apply Subtype.ext
      exact (Subgroup.eq_bot_iff_forall C).mp hC c.val.val c.property
    rw [hc1, mul_one]
    exact ML.restriction l

theorem reduced_pair_models
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    ReducedPairModelsOutput iota phi V Omega hOmega hclass source hcenter :=
  reduced_pair_models_of_comparison iota phi V Omega hOmega hclass source hcenter
    (centerless_pair_comparison iota phi V Omega hOmega hclass source hcenter hOuter principle)

end Centerless
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedModels


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
