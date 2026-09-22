import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
import ModularRep.PaperProofs.SporadicDefectZeroWeightFibreActual

/-! Q=1 normalization forced on the same faithful map by specified block
preservation. Every retained ordinary map is covered by its class law. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameMapQOne

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
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))

/-- Current local availability already covers the actual row of every raw weight. -/
def rawReductionOfAvailability (availability : LocalCanonicalAvailability iota)
    (V : CharacterWeight p K G) : CanonicalRawReduction iota V :=
  Classical.choice (availability ⟨V.subgroup, V.radical⟩
    ⟨V.localCharacter, V.defectZero⟩)

theorem atOne_block_of_availability
    (availability : LocalCanonicalAvailability iota)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := G))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G)) :
    R.1.weightBlock (T.atOne d) = operationsBlock iota hinj R (D.reduce (iota := iota) d) := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  have COne := trivialWeightBlockCompatibilityOfCanonicalOperations iota hinj R
    (rawReductionOfAvailability iota availability) D T compatibility
  exact (COne.block_atOne d).trans
    (operationsBlock_eq iota hinj R R.1.operations.ambientBlockData.blocks (D.reduce (iota := iota) d)).symm

theorem atOne_local_eq_of_class
    (hp : p.Prime) (T : TrivialWeightSource (p := p) (X := G))
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G))
    (theta : LocalDefectZeroCharacter (K := K) ⟨⊥, T.trivialRadical⟩)
    (hclass : classAt hp ⟨⊥, T.trivialRadical⟩ theta = T.atOne d) :
    theta = ⟨(T.rawAtOne d).localCharacter, (T.rawAtOne d).defectZero⟩ := by
  apply classAt_injective hp ⟨⊥, T.trivialRadical⟩
  exact hclass

theorem atOne_global_eq_of_class
    (hp : p.Prime) (T : TrivialWeightSource (p := p) (X := G))
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G))
    (theta : LocalDefectZeroCharacter (K := K) ⟨⊥, T.trivialRadical⟩)
    (hclass : classAt hp ⟨⊥, T.trivialRadical⟩ theta = T.atOne d) :
    OrdinaryIrreducibleCharacter.mapEquiv theta.val
      trivialNormalizerQuotientEquiv = d.val := by
  rw [atOne_local_eq_of_class hp T d theta hclass]
  change OrdinaryIrreducibleCharacter.mapEquiv
    (OrdinaryIrreducibleCharacter.mapEquiv d.val trivialNormalizerQuotientEquiv.symm)
    trivialNormalizerQuotientEquiv = d.val
  rw [OrdinaryIrreducibleCharacter.mapEquiv_trans, MulEquiv.symm_trans_self,
    OrdinaryIrreducibleCharacter.mapEquiv_refl]

section Family
variable {Block : Type u} [Fintype Block]
variable {blockIdempotent : Block → k[G]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1

/-- Inverse-map uniqueness forces the image of each faithful reduction. -/
theorem faithful_atOne_of_block_preserving
    (e : FB ≃ FW) (hblock : FamilyBlockPreserving iota hinj R blocks E1 e)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := G))
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G))
    (phi : FB) (hphi : phi.val = D.reduce (iota := iota) d)
    (hAtOne : R.1.weightBlock (T.atOne d) = brauerBlock iota hinj blocks (D.reduce (iota := iota) d)) :
    (e phi).val = T.atOne d := by
  let y : FW := ⟨T.atOne d, by
    change Function.Injective (blockSector (R.1.weightBlock (T.atOne d)))
    rw [hAtOne, ← hphi]
    exact phi.faithful⟩
  have hpreval : (e.symm y).val = phi.val := by
    apply Eq.trans _ hphi.symm
    apply DefectZeroOrdinaryBlockSource.uniqueBrauer
      (iota := iota) (hinj := hinj) (blocks := blocks) D B d
    calc
      brauerBlock iota hinj blocks (e.symm y).val =
          operationsBlock iota hinj R (e.symm y).val :=
        (operationsBlock_eq iota hinj R blocks (e.symm y).val).symm
      _ = R.1.weightBlock (e (e.symm y)).val := (hblock (e.symm y)).symm
      _ = R.1.weightBlock (T.atOne d) := by rw [e.apply_symm_apply]
      _ = brauerBlock iota hinj blocks (D.reduce (iota := iota) d) := hAtOne
  have val_inj : Function.Injective (fun x : FB => x.val) := by
    intro x z h
    cases x
    cases z
    simpa only [FaithfulIBr.mk.injEq] using h
  have hpre : e.symm y = phi := val_inj hpreval
  exact congrArg FaithfulWeight.val ((congrArg e hpre).symm.trans (e.apply_symm_apply y))

/-- The fixed output covers the original faithful character, its actual Q=1
fibre, and every retained ordinary Omega through the existing class law. -/
def SameMapQOneOutput (e : FB ≃ FW) (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := G)) : Prop :=
  ∀ (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G))
    (phi : FB), phi.val = D.reduce (iota := iota) d →
    (e phi).val = T.atOne d ∧
    radicalClass (e phi).val = RadicalConjugacyClass.trivialClass T.trivialRadical ∧
    ∀ theta : LocalDefectZeroCharacter (K := K) ⟨⊥, T.trivialRadical⟩,
      classAt iota.prime ⟨⊥, T.trivialRadical⟩ theta = (e phi).val →
      theta = ⟨(T.rawAtOne d).localCharacter, (T.rawAtOne d).defectZero⟩ ∧
      OrdinaryIrreducibleCharacter.mapEquiv theta.val
        trivialNormalizerQuotientEquiv = d.val

theorem same_map_qOne_of_block_preserving
    (e : FB ≃ FW) (hblock : FamilyBlockPreserving iota hinj R blocks E1 e)
    (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := G))
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D) :
    SameMapQOneOutput iota hinj R blocks E1 e D T := by
  intro d phi hphi
  have hAtOne := (atOne_block_of_availability iota hinj R availability D T compatibility d).trans
    (operationsBlock_eq iota hinj R blocks (D.reduce (iota := iota) d))
  have hOne := faithful_atOne_of_block_preserving iota hinj R blocks E1
    e hblock D T B d phi hphi hAtOne
  refine ⟨hOne, ?_, ?_⟩
  · rw [hOne]
    exact T.radicalClass_atOne d
  · intro theta hclass
    exact ⟨atOne_local_eq_of_class iota.prime T d theta (hclass.trans hOne),
      atOne_global_eq_of_class iota.prime T d theta (hclass.trans hOne)⟩

end Family
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameMapQOne


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
