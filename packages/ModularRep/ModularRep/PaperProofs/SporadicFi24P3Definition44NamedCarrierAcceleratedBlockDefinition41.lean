import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket

/-! Full block-local Definition4.1 output on the fixed actual block problem.
Both Q=1 requirements, actual character extensions and every intermediate block
law are retained. No problem or semantic predicate is selected by the caller. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedBlockDefinition41
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
  (ActualBlock LiteralCarrierAdapter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket
universe u

structure BlockDefinition41Witness
    (P : Definition35Problem.{u})
    (Cover : EllPrimeCoverSource P.p P.H)
    (D : DefectZeroReductionSource P.iota)
    (T : TrivialWeightSource (p := P.p) (X := P.H)) where
  omega : Definition35Brauer P ≃ Definition35Weight P
  equivariant : Definition35Equivariant P omega
  classQOne :
    ∀ (d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H))
      (hd : irreducibleBrauerCharacterBlock
        P.iota P.irreducibleBrauerInjective P.blocks
        (D.reduce (iota := P.iota) d) = P.block),
      (omega ⟨D.reduce (iota := P.iota) d, hd⟩).val = T.atOne d
  compatibility :
    CanonicalLocalBlockCompatibility P.iota P.blockSource.operations
  packets :
    ∀ (psi : Definition35Brauer P) (V : CharacterWeight P.p P.K P.H),
      (Quotient.mk'' (Quotient.mk'' V) :
        CharacterWeight.ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) =
        (omega psi).val → OriginalActualWeightPacket P psi V

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

def BlockCertificate
    (iota : PrimeRegularRootEmbedding p k K X)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (Cover : EllPrimeCoverSource p X)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (b : ActualBlock (k := k) (X := X)) : Prop :=
  let hinj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let P := blockProblem iota hinj R (canonicalSelectedReduction iota R C) b
  Nonempty (BlockDefinition41Witness P Cover D T)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedBlockDefinition41


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
