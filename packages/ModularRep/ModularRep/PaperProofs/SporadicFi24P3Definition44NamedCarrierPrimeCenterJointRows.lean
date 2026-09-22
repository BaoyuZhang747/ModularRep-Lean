import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterPhysicalJoin
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulJoinedModelBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulAD3Assembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerBlocks

/-! Concrete joint witnesses on every original ordinary row, with its actual central-kernel ambient. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterJointRows

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open CentralEllPrimeIBrFibreTransport
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] :
    Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (hprimeTo : ¬ p ∣ Nat.card (Subgroup.center X))

variable {BlockD : Type u} [MulAction (MulAut (X ⧸ (Subgroup.center X)))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ (Subgroup.center X)) (Block := BlockD))
variable (CU : ∀ (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ (Q : RadicalSubgroup (p := p) (G := X ⧸ (Subgroup.center X)))
    (eta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction (quotientRoot iota (Subgroup.center X)) (characterWeightAt iota.prime Q eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota (Subgroup.center X)) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective (Subgroup.center X)) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using (show Subgroup.center X ≤ Subgroup.center X from le_rfl))
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : ∀ Q : RadicalSubgroup (p := p) (G := X),
  CentralPrimeToPrimitiveImageSource (k := k)
    (normalizerMap (QuotientGroup.mk' (Subgroup.center X)) Q.1)
    (fixedNormalizer_surjective iota.prime (Subgroup.center X) (show Subgroup.center X ≤ Subgroup.center X from le_rfl) hprimeTo Q.1 Q.2) iota.prime
    (fixedNormalizer_kernel_central (Subgroup.center X) Q.1 (show Subgroup.center X ≤ Subgroup.center X from le_rfl))
    (fixedNormalizer_kernel_primeTo (Subgroup.center X) Q.1 (show Subgroup.center X ≤ Subgroup.center X from le_rfl) hprimeTo))



open Formalisation
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierPrimeCenterSectorJoin
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open EvenFieldFLZ318FixedTheoremGate
local notation "Z" => Subgroup.center X
variable (hprime : (Nat.card (Subgroup.center X)).Prime)
variable (eD : IBr (quotientRoot iota (Subgroup.center X)) ≃
  ConjugacyClass (p := p) (K := K) (G := X ⧸ Subgroup.center X))
local notation "EU" => transportedUp iota R Z le_rfl hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
local notation "BF" => trivialBrauerFibre iota R Z le_rfl

variable (hq : IsUniversalCentralExtension (QuotientGroup.mk' (Subgroup.center X)))
variable (hBlockD : downstairsBlockProperty iota (Subgroup.center X) OD eD)
variable (hD : ∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Subgroup.center X)),
  (∀ x, QuotientGroup.mk' (Subgroup.center X) (alpha x) = beta (QuotientGroup.mk' (Subgroup.center X) x)) →
  ∀ psi : IBr (quotientRoot iota (Subgroup.center X)),
    eD (IrreducibleBrauerCharacter.twist (quotientRoot iota (Subgroup.center X)) psi beta) =
      MulOpposite.op beta • eD psi)


open SporadicFi24P3Definition44NamedCarrierFaithfulJoinedModelBlocks
open SporadicFi24P3Definition44NamedCarrierOrdinaryCentralLambda
open SporadicFi24P3Definition44NamedCarrierAD3OrdinaryData
open SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauerBlocks
open SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedLocal
open CentralEllPrimeWeightLocalQuotient
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryAssembly

/-- Actual faithful scalar, ordinary row, action, local reduction and one joint model pair. -/
def FaithfulJointRow (phi : IBr iota) (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q) : Prop :=
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  let inj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let bs := R.1.operations.ambientBlockData.blocks
  let V := characterWeightAt iota.prime Q theta
  ∃ nu : FaithfulSector (k := k) (X := X),
    nu.val = brauerSector iota inj bs phi ∧
    Subgroup.center X ⊓ (chosenIBrRepresentation iota phi).ρ.ker = ⊥ ∧
    ∃ source : CanonicalRawReduction iota V,
      OrdinaryRowData iota nu.val (brauerSector iota inj bs phi) V ∧
      FaithfulActionOutput iota phi V ∧
      LocalOrdinaryRealization iota V source
        (Subgroup.topEquiv.symm : Subgroup.normalizer (V.subgroup : Set X) ≃*
          (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set X)))) ∧
      OriginalProductBlocksComparison iota (brauerSector iota inj bs phi)
        (scalarBrauer iota inj bs phi) V source

/-- The same reduced local row/root/class and its actual ambient witnesses. -/
def TrivialJointRow (phi : BF) (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q) : Prop :=
  Subgroup.center X ⊓ (chosenIBrRepresentation iota phi.val).ρ.ker = Subgroup.center X ∧
  let QD := fixedRadicalImage iota Z le_rfl hprimeTo Q
  let psi := (canonicalBrauerEquiv iota R Z le_rfl).symm phi
  ∃ eta : LocalDefectZeroCharacter (K := K) QD,
    (∀ x : NormalizerQuotient Q.val, theta.val x = eta.val (qW Z Q.val x)) ∧
    (CU Q theta).localBrauer.val = PrimeRegularClassFunction.pullback
      (normalizerMap (QuotientGroup.mk' Z) Q.val) (CD QD eta).localBrauer.val ∧
    ∃ hmatch : classAt iota.prime QD eta = eD psi,
      ReducedPairBrauerBlocksOutput (quotientRoot iota Z) psi
        (characterWeightAt iota.prime QD eta) eD
        (fullDownEquivariance iota Z rfl hq eD hD) hmatch (CD QD eta)
        (quotientCenter_eq_bot Z rfl hq)

/-- Each actual matched ordinary row retains one complete branch witness.
The same strong concrete predicate is suitable for every source-shaped construction field. -/
def CentralKernelJointPair (phi : IBr iota)
    (w : ConjugacyClass (p := p) (K := K) (G := X)) : Prop :=
  ∀ (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q),
    classAt iota.prime Q theta = w →
      (∃ hphi : phi ∈ BF, TrivialJointRow iota R hprimeTo CU CD eD hq hD ⟨phi, hphi⟩ Q theta) ∨
      FaithfulJointRow iota R phi Q theta

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterJointRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
