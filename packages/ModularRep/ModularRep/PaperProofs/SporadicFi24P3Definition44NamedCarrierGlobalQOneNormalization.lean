import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameMapQOne
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps

/-! Original all-character Q=1 normalization and reverse fibre uniqueness for the unchanged global correspondence. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization
open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter trivialNormalizerQuotientEquiv)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicFi24P3Definition44NamedCarrierRepresentativeMaps

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (E : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := X))
variable (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))

def GlobalQOneOutput : Prop :=
  (∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    E (D.reduce (iota := iota) d) = T.atOne d) ∧
  (∀ phi : IBr iota,
    radicalClass (E phi) = RadicalConjugacyClass.trivialClass T.trivialRadical ↔
      ∃! d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
        D.reduce (iota := iota) d = phi) ∧
  (∀ (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
      (theta : LocalDefectZeroCharacter (K := K) ⟨⊥, T.trivialRadical⟩),
    (Quotient.mk'' (Quotient.mk'' (characterWeightAt iota.prime ⟨⊥, T.trivialRadical⟩ theta)) :
        ConjugacyClass (p := p) (K := K) (G := X)) = E (D.reduce (iota := iota) d) →
      theta = ⟨(T.rawAtOne d).localCharacter, (T.rawAtOne d).defectZero⟩ ∧
      OrdinaryIrreducibleCharacter.mapEquiv theta.val trivialNormalizerQuotientEquiv = d.val)

theorem global_qOne_of_canonical_blocks
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (hblock : ∀ phi, R.1.weightBlock (E phi) = operationsBlock iota hinj R phi)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (Bzero : letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks D) :
    GlobalQOneOutput iota E D T := by
  have hOne := qOne_of_canonical_blockPreservingEquiv iota hinj R C E hblock D T compatibility Bzero
  refine ⟨hOne, ?_, ?_⟩
  · intro phi
    constructor
    · intro hphi
      obtain ⟨d, hd⟩ := T.exists_atOne_of_radicalClass_eq_trivial (E phi) hphi
      have heq : D.reduce (iota := iota) d = phi := E.injective ((hOne d).trans hd)
      exact ⟨d, heq, fun d' hd' => D.reduce_injective (iota := iota) (hd'.trans heq.symm)⟩
    · rintro ⟨d, hd, _⟩
      rw [← hd, hOne]
      exact T.radicalClass_atOne d
  · intro d theta hclass
    exact ⟨atOne_local_eq_of_class iota.prime T d theta (hclass.trans (hOne d)),
      atOne_global_eq_of_class iota.prime T d theta (hclass.trans (hOne d))⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
