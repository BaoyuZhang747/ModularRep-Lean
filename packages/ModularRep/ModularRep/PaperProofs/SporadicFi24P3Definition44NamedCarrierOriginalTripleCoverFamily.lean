import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTripleCoverFacts

/-! All original packets on the actual universal triple cover, away from
three. The prime-to-p cover, prime-centre dichotomy and moved-centre fact
are derived from the same universal map, kernel order and inversion action. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
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

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)

def ofNormalizedEquiv
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
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (a • phi) = a • Omega phi)
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d)
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
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K) :
    Definition41Witness iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) D T := by
  have hcard : Nat.card (Subgroup.center X) = 3 :=
    center_card_three_of_fullCover q hq hs hna hkernel
  have hprime : (Nat.card (Subgroup.center X)).Prime := by rw [hcard]; decide
  exact SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily.ofNormalizedEquiv
    iota hinj R C
    (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
    hq hprime hOuterS tau decomposition
    (movesCenter_of_card_three_of_inverts tau hcard hinverts)
    D T Omega hOmega hblock hOne compatibility lower ambientData seed
    extensionPrinciple fieldSource S9295 S9495 S820

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
