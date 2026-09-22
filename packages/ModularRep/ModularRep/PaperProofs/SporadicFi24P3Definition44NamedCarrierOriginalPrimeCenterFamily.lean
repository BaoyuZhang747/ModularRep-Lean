import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterPacket

/-! Construct the original Definition 4.1 family from one normalized,
equivariant, block-preserving correspondence and unselected lower data.
The actual central-kernel dichotomy supplies all packets internally. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativePackets
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
  (QuotientDataFamily)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbientBlockData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterPacket

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)

abbrev TrivialCenterEquation (phi : IBr iota) : Prop :=
  ∀ z : PrimeRegularElement (G := Subgroup.center X) p,
    phi.1 (PrimeRegularElement.map (Subgroup.center X).subtype z) =
      phi.1 ⟨1, isPrimeRegular_one⟩

abbrev TrivialAmbientDataFamily
    (Cover : EllPrimeCoverSource p X)
    (hUniversal : IsUniversalCentralExtension Cover.quotient) :=
  ∀ (phi : IBr iota) (V : CharacterWeight p K X)
      (hglobal : TrivialCenterEquation iota phi),
    let P := problemAt iota hinj R (canonicalSelectedReduction iota R C) phi
    let psi := ownBrauerAt iota hinj R (canonicalSelectedReduction iota R C) phi
    OriginalAmbientBlockData P psi V
      (trivialSectorOriginalAmbient P psi Cover.quotient hUniversal
        Cover.simple Cover.nonabelian Cover.centerPrimeTo hglobal)
      (actualLocalNormalizerData P psi V Cover.quotient hUniversal
        Cover.simple Cover.nonabelian Cover.centerPrimeTo hglobal)

abbrev TrivialAmbientRootFamily
    (Cover : EllPrimeCoverSource p X)
    (hUniversal : IsUniversalCentralExtension Cover.quotient) :=
  ∀ (phi : IBr iota) (hglobal : TrivialCenterEquation iota phi),
    let P := problemAt iota hinj R (canonicalSelectedReduction iota R C) phi
    let psi := ownBrauerAt iota hinj R (canonicalSelectedReduction iota R C) phi
    PrimeRegularRootEmbedding P.p P.k P.K
      (trivialSectorOriginalAmbient P psi Cover.quotient hUniversal
        Cover.simple Cover.nonabelian Cover.centerPrimeTo hglobal).A

def ofNormalizedEquiv
    (Cover : EllPrimeCoverSource p X)
    (hUniversal : IsUniversalCentralExtension Cover.quotient)
    (hcardCenter : (Nat.card (Subgroup.center X)).Prime)
    (hOuterS : Nat.card (LiteralOuterQuotient Cover.S) = 2)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X,
      ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (movesCenter : ∃ z : Subgroup.center X, tau (z : X) ≠ z)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (a • phi) = a • Omega phi)
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C Cover)
    (ambientData : TrivialAmbientDataFamily iota hinj R C Cover hUniversal)
    (seed : TrivialAmbientRootFamily iota hinj R C Cover hUniversal)
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K) :
    Definition41Witness iota hinj R C Cover D T := by
  refine {
    Omega := Omega
    equivariant := hOmega
    block_preserving := hblock
    classQOne := hOne
    compatibility := compatibility
    packets := ?_ }
  intro Q xi
  let P := problemAt iota hinj R (canonicalSelectedReduction iota R C) xi.1
  let psi := ownBrauerAt iota hinj R (canonicalSelectedReduction iota R C) xi.1
  let V := characterWeightAt iota.prime Q (localMap iota Omega iota.prime Q xi)
  let S := lower xi.1 V
  have hclass :
      (Quotient.mk'' (Quotient.mk'' V) :
        WeightClass (p := p) (K := K) (X := X)) = Omega xi.1 :=
    localMap_class iota Omega iota.prime Q xi
  have hrawBlock :
      letI := P.blockSource.operations.ambientBlockData.fintypeBlock
      P.blockSource.operations.rawWeightBlock V =
        irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
          P.blockSource.operations.ambientBlockData.blocks psi.1 := by
    change R.1.operations.rawWeightBlock V = operationsBlock iota hinj R xi.1
    exact (congrArg R.1.weightBlock hclass).trans (hblock xi.1)
  exact primeCenterOriginalPacket P psi V Cover.quotient hUniversal
    Cover.simple Cover.nonabelian Cover.centerPrimeTo hcardCenter
    (C V) compatibility hrawBlock S (ambientData xi.1 V)
    Omega hOmega D T hOne hclass hOuterS tau decomposition movesCenter
    extensionPrinciple (seed xi.1) fieldSource S9295 S9495 S820

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
