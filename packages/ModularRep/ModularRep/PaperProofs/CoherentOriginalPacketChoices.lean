import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate

/-!
# Compatible extension and block witnesses for a fixed matching

This interface requires the existence of packets with a common root convention
for the specified Brauer character and weight matching. It does not impose root
agreement on an arbitrary packet selected from a raw existence proof.
The existence of these compatible packets is an explicit additional assumption.
The numerical matching is retained. Its raw packet field is replaced, so this
interface does not prove compatible extensions or intermediate block witnesses
from their lower sources.
-/

noncomputable section

namespace ModularRep.PaperProofs.CoherentOriginalPacketChoices

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open EvenFieldFLZSourceConditions
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource)
open SpathRootCoherence

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)

/-- Compatible choices for each pair in the specified matching. -/
def OriginalPacketChoices
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X)) : Prop :=
  ∀ Q xi, ∃ packet : OriginalPacketAt iota hinj R C Omega Q xi,
    OriginalPacketRoots packet

variable (Cover : EllPrimeCoverSource p X)
variable (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))

/-- Keep the matching and its proved properties, choosing compatible packets
from the strengthened extension and block source. -/
def withCompatiblePackets
    (W : Definition41Witness iota hinj R C Cover D T)
    (choices : OriginalPacketChoices iota hinj R C W.Omega) :
    Definition41Witness iota hinj R C Cover D T :=
  { W with packets := fun Q xi => Classical.choose (choices Q xi) }

/-- Replacing the packet field leaves the exact matching unchanged. -/
@[simp] theorem withCompatiblePackets_Omega
    (W : Definition41Witness iota hinj R C Cover D T)
    (choices : OriginalPacketChoices iota hinj R C W.Omega) :
    (withCompatiblePackets iota hinj R C Cover D T W choices).Omega = W.Omega := rfl

/-- The selected packets satisfy the additional root requirements. -/
theorem of_original_with_packet_choices
    (W : Definition41Witness iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R C Cover D T)
    (choices : OriginalPacketChoices iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R C W.Omega) : Definition41Certificate iota R Cover := by
  apply of_original iota R Cover C D T
    (withCompatiblePackets iota _ R C Cover D T W choices)
  intro Q xi
  exact Classical.choose_spec (choices Q xi)

end ModularRep.PaperProofs.CoherentOriginalPacketChoices

/-
Part of the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
The results use the explicit assumptions described in the formalisation report.
-/
