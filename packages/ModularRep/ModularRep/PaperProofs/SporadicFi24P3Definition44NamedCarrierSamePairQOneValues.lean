import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameMapQOne
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCharacters
import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual

/-! Pointwise Q=1 reduction on arbitrary raw rows of the SAME faithful map. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneValues

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter
    trivialNormalizerQuotientEquiv)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierQOneCharacters (exists_atOne_from_raw)

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))

section Family
variable {Block : Type u} [Fintype Block]
variable {blockIdempotent : Block → k[G]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1

theorem exists_original_defectZero_of_raw_qOne
    (e : FB ≃ FW)
    (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := G))
    (hQOne : SameMapQOneOutput iota hinj R blocks E1 e D T)
    (phi : FB) (V : CharacterWeight p K G)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (hV : V.subgroup = ⊥) :
    ∃ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G),
      D.reduce (iota := iota) d = phi.val ∧
      ∀ n : Subgroup.normalizer (V.subgroup : Set G),
        V.localCharacter (QuotientGroup.mk n) = d.val n.val := by
  obtain ⟨d, hd, heval⟩ := exists_atOne_from_raw T V hV
  have hAtOne := (atOne_block_of_availability iota hinj R availability D T compatibility d).trans
    (operationsBlock_eq iota hinj R blocks (D.reduce (iota := iota) d))
  have hsector : brauerSector iota hinj blocks (D.reduce (iota := iota) d) =
      weightSector (R := R) (e phi).val := by
    change blockSector (brauerBlock iota hinj blocks (D.reduce (iota := iota) d)) =
      blockSector (R.1.weightBlock (e phi).val)
    rw [← hAtOne, hd, hclass]
  let phiD : FB := ⟨D.reduce (iota := iota) d, by
    rw [hsector]
    exact (e phi).faithful⟩
  have himage : (e phiD).val = (e phi).val :=
    (hQOne d phiD rfl).1.trans (hd.trans hclass)
  have val_inj : Function.Injective (fun w : FW => w.val) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    cases h
    rfl
  exact ⟨d, congrArg FaithfulIBr.val (e.injective (val_inj himage)), heval⟩

theorem localBrauer_atOne_of_same_map
    (e : FB ≃ FW)
    (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := G))
    (hQOne : SameMapQOneOutput iota hinj R blocks E1 e D T)
    (phi : FB) (V : CharacterWeight p K G)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (hV : V.subgroup = ⊥) (source : CanonicalRawReduction iota V) :
    PrimeRegularClassFunction.pullback
      (Subgroup.normalizer (V.subgroup : Set G)).subtype phi.val.val = source.localBrauer.val := by
  obtain ⟨d, hD, heval⟩ := exists_original_defectZero_of_raw_qOne
    iota hinj R blocks E1 e availability compatibility D T hQOne phi V hclass hV
  apply PrimeRegularClassFunction.ext
  intro n
  have hraw : V.localCharacter (QuotientGroup.mk n.val) =
      phi.val.val (PrimeRegularElement.map (Subgroup.normalizer (V.subgroup : Set G)).subtype n) :=
    (heval n.val).trans
      ((D.reduce_isReduction (iota := iota) d
        (PrimeRegularElement.map (Subgroup.normalizer (V.subgroup : Set G)).subtype n)).trans
        (congrArg (fun chi : IBr iota => chi.val
          (PrimeRegularElement.map (Subgroup.normalizer (V.subgroup : Set G)).subtype n)) hD))
  exact hraw.symm.trans (source.localBrauer_reduction n)

end Family
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneValues


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
