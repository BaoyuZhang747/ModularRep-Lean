import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterJoinedLocalMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction

/-! Specified joined map on the unchanged R catalogue and quotient transport. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterPhysicalJoin

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
open SporadicFi24P3Definition44NamedCarrierAllPairs
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

/-- R owns its catalogue; the trivial and faithful maps are retained literally. -/
def physicalJoin :
    let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
    let inj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    (FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine) →
      (IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := X)) := by
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro eF
  exact joined iota (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ hprime EU eF

variable (hq : IsUniversalCentralExtension (QuotientGroup.mk' (Subgroup.center X)))
variable (hBlockD : downstairsBlockProperty iota (Subgroup.center X) OD eD)
variable (hD : ∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Subgroup.center X)),
  (∀ x, QuotientGroup.mk' (Subgroup.center X) (alpha x) = beta (QuotientGroup.mk' (Subgroup.center X) x)) →
  ∀ psi : IBr (quotientRoot iota (Subgroup.center X)),
    eD (IrreducibleBrauerCharacter.twist (quotientRoot iota (Subgroup.center X)) psi beta) =
      MulOpposite.op beta • eD psi)

include hq hBlockD hD in
theorem physical_join_laws :
    let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
    let inj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    ∀ (eF : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine),
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : FaithfulIBr iota inj bs R routine), eF (a • phi) = a • eF phi) →
      (∀ phi : FaithfulIBr iota inj bs R routine,
        R.1.weightBlock (eF phi).val = brauerBlock iota inj bs phi.val) →
      let E := physicalJoin iota R hprimeTo OD CU CD compatU compatD Sglobal Slocal hprime eD eF
      (∀ phi : BF, E phi.val = (EU phi).val) ∧
      (∀ phi : FaithfulIBr iota inj bs R routine, E phi.val = (eF phi).val) ∧
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), E (a • phi) = a • E phi) ∧
      (∀ phi : IBr iota, R.1.weightBlock (E phi) = brauerBlock iota inj bs phi) ∧
      (∀ phi : IBr iota, weightSector (R := R) (E phi) = brauerSector iota inj bs phi) := by
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  intro eF heF hbF
  let inj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  let bs := R.1.operations.ambientBlockData.blocks
  let routine : RoutineTransportInput iota inj bs R := ⟨⟩
  have hbT : ∀ phi : BF, R.1.weightBlock (EU phi).val = brauerBlock iota inj bs phi.val :=
    fun phi => (transportedUp_block iota R Z le_rfl hprimeTo OD CU CD compatU compatD
      Sglobal Slocal eD hBlockD phi).symm.trans
        (operationsBlock_eq iota inj R bs phi.val)
  have heT : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi psi : BF), psi.val = a • phi.val →
      (EU psi).val = a • (EU phi).val := by
    intro a phi psi hpsi
    let beta := fullCenterAutEquiv Z rfl hq a.unop
    let square (x : X) : QuotientGroup.mk' Z (a.unop x) = beta (QuotientGroup.mk' Z x) :=
      (fullCenterAutEquiv_square Z rfl hq a.unop x).symm
    have ht : psi = brauerSectorTwist iota R Z le_rfl a.unop beta square phi := Subtype.ext hpsi
    rw [ht]
    exact congrArg (fun w : SectorWeights R Z => w.val)
      (transportedUp_covariance iota R Z le_rfl hprimeTo OD CU CD compatU compatD
        Sglobal Slocal eD a.unop beta square (hD a.unop beta square) phi)
  exact ⟨joined_trivial iota inj bs R routine hprime EU eF,
    joined_faithful iota inj bs R routine hprime EU eF,
    joined_equivariant iota inj bs R routine hprime EU eF heT heF,
    joined_block iota inj bs R routine hprime EU eF hbT hbF,
    joined_sector iota inj bs R routine hprime EU eF hbT hbF⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterPhysicalJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
