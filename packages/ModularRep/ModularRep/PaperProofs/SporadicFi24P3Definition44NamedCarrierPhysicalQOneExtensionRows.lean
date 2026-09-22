import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneValues
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneModelRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessQOneAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoQOneAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulQOneAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOuterTrivialQOneAssembly

/-! The second Q=1 clause on every retained row and every retained global
model, with each branch's actual groups and embeddings fixed literally. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalQOneExtensionRows

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource)
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierSamePairQOneValues
open SporadicFi24P3Definition44NamedCarrierSamePairQOneModelRows
open SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1

def CenterlessCommonOutput (hcenter : Subgroup.center G = ⊥) (e : FB ≃ FW) : Prop :=
  ∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val →
    ∀ (source : CanonicalRawReduction iota V) (hV : V.subgroup = ⊥),
      EveryModelCommon iota phi.val V source
        (actualBase iota phi.val) (actualBaseEquiv iota phi.val hcenter)
        (embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup)
        (embeddedNormalizer_eq_top (innerEmbedding iota phi.val) V.subgroup hV)
        (embeddedLocalBase (innerEmbedding iota phi.val) V.subgroup)
        (normalizerBaseEquiv (innerEmbedding iota phi.val)
          (innerEmbedding_injective iota phi.val hcenter) V.subgroup)

theorem centerless_common_output (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (Dzero : DefectZeroReductionSource iota)
    (Tzero : TrivialWeightSource (p := p) (X := G))
    (hQOne : SameMapQOneOutput iota hinj R blocks E1 e Dzero Tzero)
    (seed : ∀ phi : FB, Nonempty (PrimeRegularRootEmbedding p k K (ActualAutAmbient iota phi.val))) :
    CenterlessCommonOutput iota hinj R blocks E1 hcenter e := by
  intro phi V hclass source hV
  apply every_model_common iota phi.val V source
    (actualBase iota phi.val) (actualBaseEquiv iota phi.val hcenter)
    (embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup)
    (embeddedNormalizer_eq_top (innerEmbedding iota phi.val) V.subgroup hV)
    (embeddedLocalBase (innerEmbedding iota phi.val) V.subgroup)
    (normalizerBaseEquiv (innerEmbedding iota phi.val)
      (innerEmbedding_injective iota phi.val hcenter) V.subgroup)
  · ext n
    rfl
  · exact localBrauer_atOne_of_same_map iota hinj R blocks E1 e availability compatibility
      Dzero Tzero hQOne phi V hclass hV source
  · exact seed phi

section CentralTwo
variable {T C : Type u} [Group T] [Group C]
variable (E : GroupExtension G T C) (hC : Nat.card C = 2)

def CentralTwoCommonOutput (e : FB ≃ FW) : Prop :=
  letI : Finite T := extension_finite E hC
  ∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val →
    ∀ (source : CanonicalRawReduction iota V) (hV : V.subgroup = ⊥),
      EveryModelCommon iota phi.val V source
        (brauerEmbedding E iota phi.val).range
        (MonoidHom.ofInjective (brauerEmbedding_injective E iota phi.val))
        (embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup)
        (embeddedNormalizer_eq_top (brauerEmbedding E iota phi.val) V.subgroup hV)
        (embeddedLocalBase (brauerEmbedding E iota phi.val) V.subgroup)
        (normalizerBaseEquiv (brauerEmbedding E iota phi.val)
          (brauerEmbedding_injective E iota phi.val) V.subgroup)

theorem central_two_common_output
    (e : FB ≃ FW) (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (Dzero : DefectZeroReductionSource iota)
    (Tzero : TrivialWeightSource (p := p) (X := G))
    (hQOne : SameMapQOneOutput iota hinj R blocks E1 e Dzero Tzero)
    (seed : letI : Finite T := extension_finite E hC
      ∀ phi : FB, Nonempty (PrimeRegularRootEmbedding p k K (brauerAmbient E iota phi.val))) :
    CentralTwoCommonOutput iota hinj R blocks E1 E hC e := by
  let : Finite T := extension_finite E hC
  intro phi V hclass source hV
  apply every_model_common iota phi.val V source
    (brauerEmbedding E iota phi.val).range
    (MonoidHom.ofInjective (brauerEmbedding_injective E iota phi.val))
    (embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup)
    (embeddedNormalizer_eq_top (brauerEmbedding E iota phi.val) V.subgroup hV)
    (embeddedLocalBase (brauerEmbedding E iota phi.val) V.subgroup)
    (normalizerBaseEquiv (brauerEmbedding E iota phi.val)
      (brauerEmbedding_injective E iota phi.val) V.subgroup)
  · ext n
    rfl
  · exact localBrauer_atOne_of_same_map iota hinj R blocks E1 e availability compatibility
      Dzero Tzero hQOne phi V hclass hV source
  · exact seed phi

end CentralTwo

def OriginalCommonOutput (e : FB ≃ FW) : Prop :=
  ∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val →
    ∀ (source : CanonicalRawReduction iota V) (hV : V.subgroup = ⊥),
      EveryModelCommonAtRoot iota phi.val V source
        (⊤ : Subgroup G) Subgroup.topEquiv.symm
        (Subgroup.normalizer (V.subgroup : Set G))
        (by rw [hV]; exact Subgroup.normalizer_eq_top (⊥ : Subgroup G))
        (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G)))
        Subgroup.topEquiv.symm iota

theorem original_common_output
    (e : FB ≃ FW) (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (Dzero : DefectZeroReductionSource iota)
    (Tzero : TrivialWeightSource (p := p) (X := G))
    (hQOne : SameMapQOneOutput iota hinj R blocks E1 e Dzero Tzero) :
    OriginalCommonOutput iota hinj R blocks E1 e := by
  intro phi V hclass source hV
  apply every_model_common_at_root iota phi.val V source
    (⊤ : Subgroup G) Subgroup.topEquiv.symm
    (Subgroup.normalizer (V.subgroup : Set G))
    (by rw [hV]; exact Subgroup.normalizer_eq_top (⊥ : Subgroup G))
    (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G)))
    Subgroup.topEquiv.symm
  · ext n
    rfl
  · exact localBrauer_atOne_of_same_map iota hinj R blocks E1 e availability compatibility
      Dzero Tzero hQOne phi V hclass hV source
  · intro zeta
    exact PrimeRegularRootEmbedding.alongMulEquiv_lift iota
      (Subgroup.topEquiv.symm : G ≃* (⊤ : Subgroup G)) (((zeta : kˣ) : k))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalQOneExtensionRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
