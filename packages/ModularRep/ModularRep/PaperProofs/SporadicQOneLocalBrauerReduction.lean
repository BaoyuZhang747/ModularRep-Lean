import ModularRep.BrauerCharacterEquivTransport
import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual

/-!
# Brauer reduction in the trivial-radical branch

At the trivial radical subgroup, the local quotient is canonically the
ambient group.  The local Brauer character is therefore the transport of the
canonical defect-zero reduction along this equivalence.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

/-- At `Q = 1`, the transported local Brauer character is the reduction of
the canonical local ordinary character. -/
theorem qOneLocalBrauer_isReduction
    (iota : PrimeRegularRootEmbedding p k K X)
    (D : DefectZeroReductionSource
      (p := p) (K := K) (X := X) iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      (iota.alongMulEquiv
        (trivialNormalizerQuotientEquiv (X := X)).symm)
      (T.rawAtOne d).localCharacter
      (IrreducibleBrauerCharacter.alongMulEquiv iota
        (trivialNormalizerQuotientEquiv (X := X)).symm
        (D.reduce (iota := iota) d)) := by
  intro g
  exact D.reduce_isReduction (iota := iota) d
    (PrimeRegularElement.map
      (trivialNormalizerQuotientEquiv (X := X)).toMonoidHom g)

end ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
