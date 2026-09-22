import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual

/-!
# Q=1 normalization of the literal representative local map

The weight-class normalization identifies the image under the same local
bijection with the ordinary character on N_X(1)/1. Transport to X gives
exactly the original defect-zero character, as in Spath 4.1(iv).
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQOne

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
variable (D : DefectZeroReductionSource iota)
variable (T : TrivialWeightSource (p := p) (X := X))
variable (hOmegaOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
  Omega (D.reduce (iota := iota) d) = T.atOne d)

def atOneBrauer (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    BrauerAtRadical iota Omega ⟨⊥, T.trivialRadical⟩ := by
  refine ⟨D.reduce (iota := iota) d, ?_⟩
  rw [hOmegaOne]
  rfl

theorem localMap_atOne (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    localMap iota Omega iota.prime ⟨⊥, T.trivialRadical⟩
        (atOneBrauer iota Omega D T hOmegaOne d) =
      ⟨(T.rawAtOne d).localCharacter, (T.rawAtOne d).defectZero⟩ := by
  apply (localDefectZeroEquivWeightRadicalFibre (K := K) iota.prime
    ⟨⊥, T.trivialRadical⟩).injective
  apply Subtype.ext
  rw [localDefectZeroEquivWeightRadicalFibre_apply_val,
    localDefectZeroEquivWeightRadicalFibre_apply_val, localMap_class]
  exact hOmegaOne d

theorem localMap_atOne_global
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    OrdinaryIrreducibleCharacter.mapEquiv
        (localMap iota Omega iota.prime ⟨⊥, T.trivialRadical⟩
          (atOneBrauer iota Omega D T hOmegaOne d)).1
        trivialNormalizerQuotientEquiv = d.1 := by
  rw [localMap_atOne]
  change OrdinaryIrreducibleCharacter.mapEquiv
    (OrdinaryIrreducibleCharacter.mapEquiv d.1 trivialNormalizerQuotientEquiv.symm)
      trivialNormalizerQuotientEquiv = d.1
  rw [OrdinaryIrreducibleCharacter.mapEquiv_trans, MulEquiv.symm_trans_self,
    OrdinaryIrreducibleCharacter.mapEquiv_refl]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQOne


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
