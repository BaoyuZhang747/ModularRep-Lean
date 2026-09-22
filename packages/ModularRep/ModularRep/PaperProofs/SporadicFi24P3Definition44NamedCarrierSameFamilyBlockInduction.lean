import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs

/-! Reference-sector block preservation transports to the same faithful
family and yields actual local block induction for every matched raw row. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction

open ModularRep ModularRep.CharacterWeight Formalisation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))

/-- Both block-induction statements refer to the original specified catalogues. -/
def RawBlockOutput (phi : IBr iota) (V : CharacterWeight p K G) : Prop :=
  let O := R.1.operations
  let D := O.inflatedNormalizerBlockData V.subgroup
  let := O.ambientBlockData.fintypeBlock
  let := D.fintypeBlock
  O.rawWeightBlock V = operationsBlock iota hinj R phi ∧
  BlockInducesTo (Subgroup.normalizer (V.subgroup : Set G))
    D.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer V.subgroup
      (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
    (operationsBlock iota hinj R phi) ∧
  ∀ source : CanonicalRawReduction iota V,
    BlockInducesTo (Subgroup.normalizer (V.subgroup : Set G))
      D.catalogue O.ambientBlockData.catalogue
      (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        O V.subgroup source.normalizerRoot source.localBrauer)
      (operationsBlock iota hinj R phi)

theorem raw_block_output (phi : IBr iota) (V : CharacterWeight p K G)
    (hraw : R.1.operations.rawWeightBlock V = operationsBlock iota hinj R phi)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations) :
    RawBlockOutput iota hinj R phi V := by
  let O := R.1.operations
  let D := O.inflatedNormalizerBlockData V.subgroup
  let := O.ambientBlockData.fintypeBlock
  let := D.fintypeBlock
  have hind := inducedBlock_spec (Subgroup.normalizer (V.subgroup : Set G))
    D.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer V.subgroup
      (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
    (O.blockInductionDefined V)
  change BlockInducesTo _ _ _ _ (O.rawWeightBlock V) at hind
  rw [hraw] at hind
  refine ⟨hraw, hind, ?_⟩
  intro source
  rw [compatibility.normalizerBrauerBlock_eq_inflateToNormalizer V source]
  exact hind

section Family
variable {Block : Type u} [Fintype Block]
variable {blockIdempotent : Block → k[G]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "A" => (MulAut G)ᵐᵒᵖ
local notation "S" => FaithfulSector (k := k) (X := G)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "pX" => faithfulBrauerSector iota hinj blocks R E1
local notation "pY" => faithfulWeightSector iota hinj blocks R E1
local notation "hpX" => brauerProjection_equivariant iota hinj blocks R E1
local notation "hpY" => weightProjection_equivariant iota hinj blocks R E1

/-- The only new correspondence input is on the original reference fibre. -/
def BaseBlockPreserving (nu0 : S) (e0 : Fibre pX nu0 ≃ Fibre pY nu0) : Prop :=
  ∀ x : Fibre pX nu0,
    R.1.weightBlock (e0 x).val.val = operationsBlock iota hinj R x.val.val

def FamilyBlockPreserving (e : FB ≃ FW) : Prop :=
  ∀ phi : FB, R.1.weightBlock (e phi).val = operationsBlock iota hinj R phi.val

theorem transported_block_preserving
    (nu0 : S) (t : S → A) (ht : ∀ nu, t nu • nu0 = nu)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (h0 : BaseBlockPreserving iota hinj R blocks E1 nu0 e0) :
    FamilyBlockPreserving iota hinj R blocks E1
      (transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) := by
  intro phi
  let x0 : Fibre pX nu0 :=
    (fibreFromBase pX hpX nu0 t ht (pX phi)).symm ⟨phi, rfl⟩
  change R.1.weightBlock (t (pX phi) • (e0 x0).val.val) =
    operationsBlock iota hinj R phi.val
  rw [R.1.weightBlock_transport, h0 x0]
  change t (pX phi) • operationsBlock iota hinj R ((t (pX phi))⁻¹ • phi.val) =
    operationsBlock iota hinj R phi.val
  have htransport : operationsBlock iota hinj R ((t (pX phi))⁻¹ • phi.val) =
      (t (pX phi))⁻¹ • operationsBlock iota hinj R phi.val :=
    operationsBrauerSupport iota hinj R ((t (pX phi))⁻¹) phi.val
  rw [htransport]
  exact smul_inv_smul _ _

theorem family_block_preserving_of_independent
    (nu0 : S) (hcase : FaithfulSectorOrbitCases (G := G))
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (h0 : BaseBlockPreserving iota hinj R blocks E1 nu0 e0)
    (e : FB ≃ FW)
    (hIndependent : ∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
      e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0) :
    FamilyBlockPreserving iota hinj R blocks E1 e := by
  let t : S → A := fun nu => Classical.choose (faithfulSector_orbit nu0 hcase nu)
  have ht : ∀ nu, t nu • nu0 = nu := fun nu =>
    Classical.choose_spec (faithfulSector_orbit nu0 hcase nu)
  rw [hIndependent t ht]
  exact transported_block_preserving iota hinj R blocks E1 nu0 t ht e0 h0

/-- The universal raw statement applies to every existing Omega row and source. -/
def MatchedBlockOutput (e : FB ≃ FW) : Prop :=
  FamilyBlockPreserving iota hinj R blocks E1 e ∧
  ∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val →
    RawBlockOutput iota hinj R phi.val V

theorem matched_block_output (e : FB ≃ FW)
    (hblock : FamilyBlockPreserving iota hinj R blocks E1 e)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations) :
    MatchedBlockOutput iota hinj R blocks E1 e := by
  refine ⟨hblock, ?_⟩
  intro phi V hmatch
  exact raw_block_output iota hinj R phi.val V
    ((congrArg R.1.weightBlock hmatch).trans (hblock phi)) compatibility

theorem matched_block_output_of_base
    (nu0 : S) (hcase : FaithfulSectorOrbitCases (G := G))
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (h0 : BaseBlockPreserving iota hinj R blocks E1 nu0 e0)
    (e : FB ≃ FW)
    (hIndependent : ∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
      e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations) :
    MatchedBlockOutput iota hinj R blocks E1 e :=
  matched_block_output iota hinj R blocks E1 e
    (family_block_preserving_of_independent iota hinj R blocks E1
      nu0 hcase e0 h0 e hIndependent) compatibility

end Family
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
