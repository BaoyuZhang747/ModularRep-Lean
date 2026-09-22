import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

/-! The quotient correspondence's block law lifts to the original specified
trivial sector. Both block images are derived; nonzero orthogonal images identify the block. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightClasses
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] :
    Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

local notation "BF" => trivialBrauerFibre iota R Z hcentral

def brauerBlockOf (phi : IBr iota) : ActualBlock (k := k) (X := X) := by
  letI : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  exact irreducibleBrauerCharacterBlock iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks phi

variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (CU : ∀ (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ (Q : RadicalSubgroup (p := p) (G := X ⧸ Z))
    (eta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction (quotientRoot iota Z) (characterWeightAt iota.prime Q eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : ∀ Q : RadicalSubgroup (p := p) (G := X),
  CentralPrimeToPrimitiveImageSource (k := k)
    (normalizerMap (QuotientGroup.mk' Z) Q.1)
    (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
    (fixedNormalizer_kernel_central Z Q.1 hcentral)
    (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))


def quotientBrauerBlock (psi : IBr (quotientRoot iota Z)) : BlockD := by
  letI : Fintype BlockD := OD.ambientBlockData.fintypeBlock
  exact irreducibleBrauerCharacterBlock (quotientRoot iota Z)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot iota Z))
    OD.ambientBlockData.blocks psi

def downstairsBlockProperty (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z)) : Prop :=
  ∀ (psi : IBr (quotientRoot iota Z)) (Wbar : CharacterWeight p K (X ⧸ Z)),
    rawClass Wbar = eD psi → quotientBrauerBlock iota Z OD psi = OD.rawWeightBlock Wbar

theorem transportedUp_block (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (hD : downstairsBlockProperty iota Z OD eD) (phi : BF) :
    brauerBlockOf iota R phi.val = R.1.weightBlock
      (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD phi).val := by
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  let _ : Fintype BlockD := OD.ambientBlockData.fintypeBlock
  let chi := (canonicalBrauerEquiv iota R Z hcentral).symm phi
  let w := transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD phi
  let eU := R.1.operations.ambientBlockData.blockIdempotent
  let eQ := OD.ambientBlockData.blockIdempotent
  let DU := R.1.operations.ambientBlockData.blocks
  let DQ := OD.ambientBlockData.blocks
  let F := algebraMapOf (k := k) (QuotientGroup.mk' Z)
  have imageB : F (eU (brauerBlockOf iota R phi.val)) =
      eQ (quotientBrauerBlock iota Z OD chi) :=
    actualBrauerBlock_image (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
      (by simpa only [QuotientGroup.ker_mk'] using hcentral)
      (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)
      Sglobal iota (quotientRoot iota Z) (fun V => quotientRoot_compatible iota Z V.ρ)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot iota Z))
      DU DQ phi.val chi (canonicalBrauerEquiv_symm_pullback iota R Z hcentral phi).symm
  obtain ⟨W, hW⟩ := rawClass_surjective (p := p) (K := K) (X := X) w.val
  obtain ⟨Wbar, hclassD, _hsub, _hfactor, hImageW⟩ :=
    (central_quotient_weight_transport_with_invertible iota R Z hcentral hprimeTo
      OD CU CD compatU compatD Sglobal Slocal).1 w W hW
  have hEW : sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal w =
      eD chi := transportedUp_square iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD phi
  have hblockD := hD chi Wbar (hclassD.trans hEW)
  have imageW : F (eU (R.1.weightBlock w.val)) = eQ (OD.rawWeightBlock Wbar) := by
    change F (R.1.operations.ambientBlockData.blockIdempotent (R.1.weightBlock w.val)) = _
    rw [R.2]
    exact hImageW
  exact blockIndex_eq_of_map_eq_of_ne_zero DU F.toRingHom
    (brauerBlockOf iota R phi.val) (R.1.weightBlock w.val)
    (imageB.trans ((congrArg eQ hblockD).trans imageW.symm))
    (by
      intro hz
      exact (DQ.primitive (quotientBrauerBlock iota Z OD chi)).ne_zero (imageB.symm.trans hz))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
