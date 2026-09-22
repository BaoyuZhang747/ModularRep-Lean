import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantReplacement

/-! Concrete output predicates copying the complete accepted centreless and
centre-two comparisons. Their canonical quotient maps keep the actual
correspondence and its proofs. Neither predicate is a source assumption. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

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

/-- The complete centreless conclusion, used only as constructed output. -/
def CenterlessPairComparison : Prop :=
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
        (ScalarFactorSet.pullback qE MG.factorSet)

theorem centerless_pair_comparison
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    CenterlessPairComparison iota phi V Omega hOmega hclass source hcenter :=
  centerless_equivariant_replacement iota phi V Omega hOmega hclass source hcenter
    hOuter principle

end Centerless

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

/-- The complete centre-two conclusion on the original extension. -/
def CentralTwoPairComparison : Prop :=
    letI : Finite T := extension_finite E hC
    Function.Surjective (brauerAction E iota phi.1) ∧
    (∀ a : A, ∃ d : D, ∃ x : G, a = d.1 * i x) ∧
    Z ≤ Subgroup.center A ∧
    B ⊔ Z = B ∧ L ⊔ ZL = L ∧
    (∀ a : A, IrreducibleBrauerCharacter.twist rZ gam (MulAut.conjNormal a) = gam) ∧
    (∀ c : PrimeRegularElement (G := Z) p, (gam).1 c = (rZ).lift (nuZ c.1 : k)) ∧
    ∃ (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL),
      GlobalGammaProduct iota nu phi E hC hOuter hAut MG ∧
      LocalGammaProduct iota nu phi E hC hOuter hAut hZ V source ML ∧
      MG.factorSet = ScalarFactorSet.trivial ∧
      ML.factorSet = ScalarFactorSet.trivial ∧
      (∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.1) ∧
      ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
      ScalarFactorSet.Cohomologous ML.factorSet
        (ScalarFactorSet.pullback qE MG.factorSet)

theorem central_two_pair_comparison
    (hlocal : ∀ z : Subgroup.center G,
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
        (Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
          (nu z : k) • 1)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    CentralTwoPairComparison iota nu phi E hC hOuter hAut hZ V source Omega hOmega hclass :=
  central_two_equivariant_replacement (iota := iota) (nu := nu) (phi := phi)
    (E := E) (hC := hC) (hOuter := hOuter) (hAut := hAut) (hZ := hZ)
    (V := V) (source := source) (Omega := Omega) (hOmega := hOmega) (hclass := hclass)
    hlocal principle

end CentralTwo

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterPairComparison


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
