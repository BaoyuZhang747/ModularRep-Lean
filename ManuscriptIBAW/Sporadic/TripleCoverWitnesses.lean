import ModularRep.PaperProofs.CoherentOriginalPacketChoices
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverNumerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate

/-!
# Compatible witnesses for the triple cover calculation

The numerical argument constructs a block preserving equivariant bijection.
The additional source requires compatible extension and intermediate block
witnesses for exactly this matching. Their existence remains an external
assumption. The lower construction still supplies a raw witness, but its
packet field is replaced by the compatible witnesses supplied by this source.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace ManuscriptIBAW.Sporadic.TripleCoverWitnesses

open ModularRep.PaperProofs
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource)
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
  (QuotientDataFamily)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily
  (TrivialAmbientDataFamily TrivialAmbientRootFamily)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTripleCoverFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable [Finite (WeightClass (p := p) (K := K) (X := X))]

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate

/-- The matching selected by the numerical argument, with its proved properties.
This choice concerns the bijection, not the extension packets. -/
def numericalMatching
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X,
      ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (counts : ActualBlockC2Counts iota hinj R tau) :
    {Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X) //
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi} :=
  ⟨Classical.choose (exists_actual_equivariant_of_counts iota hinj R tau decomposition counts),
    Classical.choose_spec (exists_actual_equivariant_of_counts iota hinj R tau decomposition counts)⟩

/-- Existence of compatible extension and intermediate block witnesses for
exactly the matching selected by the numerical argument. These witnesses
remain an external assumption, not a consequence of the numerical counts. -/
def PacketCompatibility
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X,
      ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (counts : ActualBlockC2Counts iota hinj R tau) : Prop :=
  CoherentOriginalPacketChoices.OriginalPacketChoices iota hinj R C
    (numericalMatching iota hinj R tau decomposition counts).1

/-- The numerical matching and compatible extension and block witnesses give the full condition. -/
theorem complete
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (hpne : p ≠ 3)
    {S : Type u} [Group S] [Fintype S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3)
    (hOuterS : Nat.card (LiteralOuterQuotient S) = 2)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X,
      ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (counts : ActualBlockC2Counts iota hinj R tau)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (Bzero :
      letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks D)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel))
    (ambientData : TrivialAmbientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) hq)
    (seed : TrivialAmbientRootFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) hq)
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K) 
    (packets : PacketCompatibility iota hinj R C tau decomposition counts) :
    Definition41Certificate iota R
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) := by
  let matching := numericalMatching iota hinj R tau decomposition counts
  let Omega := matching.1
  have hOmega := matching.2.1
  have hblock := matching.2.2
  let hOne := qOne_of_canonical_blockPreservingEquiv
    iota hinj R C Omega hblock D T compatibility Bzero
  exact CoherentOriginalPacketChoices.of_original_with_packet_choices iota R C _ D T
    (SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily.ofNormalizedEquiv
      iota hinj R C hpne q hq hs hna hkernel hOuterS tau decomposition hinverts
      D T Omega hOmega hblock hOne compatibility lower ambientData seed
      extensionPrinciple fieldSource S9295 S9495 S820)
    packets

end ManuscriptIBAW.Sporadic.TripleCoverWitnesses

/-
This file belongs to the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under explicit external assumptions.
-/
