import ModularRep.PaperProofs.CentralEllPrimeIBrFibreEquivariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

/-! The one retained quotient correspondence transports equivariance through
literal paired automorphisms. Neither an involution nor a full descent hom is required. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open CentralEllPrimeIBrFibreTransport CentralEllPrimeIBrFibreEquivariance
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport

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

def brauerSectorTwist (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) : BF ≃ BF := by
  letI : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  exact {
    toFun := twistTrivialCentralCharacterFibre iota R.1.operations.ambientBlockData.blocks
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral alpha beta square
    invFun := twistTrivialCentralCharacterFibre iota R.1.operations.ambientBlockData.blocks
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral alpha.symm beta.symm (by
        intro x
        apply beta.injective
        simpa only [MulEquiv.apply_symm_apply] using (square (alpha.symm x)).symm)
    left_inv := fun phi => by
      apply Subtype.ext
      exact inv_smul_smul (MulOpposite.op alpha) phi.val
    right_inv := fun phi => by
      apply Subtype.ext
      exact smul_inv_smul (MulOpposite.op alpha) phi.val }

theorem brauerSectorTwist_val (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) (phi : BF) :
    (brauerSectorTwist iota R Z hcentral alpha beta square phi).val =
      IrreducibleBrauerCharacter.twist iota phi.val alpha := rfl

theorem canonicalBrauerEquiv_covariance (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (psi : IBr (quotientRoot iota Z)) :
    canonicalBrauerEquiv iota R Z hcentral (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) =
      brauerSectorTwist iota R Z hcentral alpha beta square (canonicalBrauerEquiv iota R Z hcentral psi) := by
  apply Subtype.ext
  exact inflateIBr_twist_of_quotientSquare iota (quotientRoot iota Z)
    (canonicalQuotientRealisation iota Z) alpha beta square psi

theorem canonicalBrauerEquiv_symm_covariance (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) (phi : BF) :
    (canonicalBrauerEquiv iota R Z hcentral).symm (brauerSectorTwist iota R Z hcentral alpha beta square phi) =
      IrreducibleBrauerCharacter.twist (quotientRoot iota Z)
        ((canonicalBrauerEquiv iota R Z hcentral).symm phi) beta := by
  let EB := canonicalBrauerEquiv iota R Z hcentral
  let TB := brauerSectorTwist iota R Z hcentral alpha beta square
  apply EB.injective
  exact (EB.apply_symm_apply (TB phi)).trans
    ((congrArg TB (EB.apply_symm_apply phi).symm).trans
      (canonicalBrauerEquiv_covariance iota R Z hcentral alpha beta square (EB.symm phi)).symm)

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


theorem transportedUp_covariance (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (hD : ∀ psi : IBr (quotientRoot iota Z),
      eD (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) = MulOpposite.op beta • eD psi)
    (phi : BF) :
    transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD
      (brauerSectorTwist iota R Z hcentral alpha beta square phi) =
      sectorTwist R Z hcentral alpha beta square
        (transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal eD phi) := by
  apply (sectorToQuotient iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal).injective
  rw [transportedUp_square, sectorToQuotient_covariance, transportedUp_square,
    canonicalBrauerEquiv_symm_covariance, hD]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
