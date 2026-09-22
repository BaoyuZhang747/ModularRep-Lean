import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionCarriers
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionUpperCorrespondence
import ModularRep.PaperProofs.TypeBAllRankGGGRBasisPhysical

/-!
# Calibrated principal Brauer transport from Spin to matrix Omega

The existing central-two inflation and matrix equivalence give an
equivalence of the actual principal Brauer fibres. Both prescribed roots
are calibrated to the same modular system; the intermediate quotient root
is constructed by groupRoot. The specified principal block is identified
by uniqueness. No full-cover theorem is needed for this character transport.

The Omega count is derived from the same PrincipalRationalClassCount used
by the accepted GGGR theorem and the independent rational Spin class count
U+D. It does not repeat a Spin Brauer-count source or introduce a matching.
The fixation theorem is a pure transport helper: the final application
must supply Spin fixation by internally invoking the accepted selector.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionBrauerTransport

open ModularRep TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding
open TypeBPrincipalSpinMatrixFieldTransport TypeBPrincipalRootLiftBinding
open TypeBAllRankPrincipalCriterionCarriers
open TypeBSpinRationalUnipotentClassBinding

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
  (N : NormSource n F) [Finite (Spin n F N)]
  (C : TypeBCliffordOrthogonalSourceBinding.Source
    n F r f parameters (rank3 rank) N)
  (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
  {K O k : Type} [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (Msys : ModularSystem 2 K O k)
  (rootSpin : PrimeRegularRootEmbedding 2 k K (Spin n F N))
  (rootX : PrimeRegularRootEmbedding 2 k K (X n F))
  (compatibleSpin : RootResidueCompatible Msys rootSpin)
  (compatibleX : RootResidueCompatible Msys rootX)
  (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k)
  (regular : TypeBCentralKernelBrauerInflation.PrimeRegularQuotientLiftPrinciple.{0} 2)
  (centralBlocks : NavarroCentralBlockPrinciple 2 k)
  [Fintype (LiteralPrimitiveBlock k (X n F))]
  (matrixBlocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (X n F) => b.val))
  (bSpin : LiteralPrimitiveBlock k (Spin n F N)) (principalSpin : IsPrincipal bSpin)
  (bX : LiteralPrimitiveBlock k (X n F)) (principalX : IsPrincipal bX)

/-- The existing central quotient and matrix maps, restricted to the two
prescribed principal blocks and calibrated roots. -/
def principalBrauerEquiv : BrauerFibre rootSpin bSpin ≃ BrauerFibre rootX bX := by
  let oldRoot := groupRoot Msys (TypeBSpinCoverSource.Omega N)
  have oldCompatible : RootResidueCompatible Msys oldRoot :=
    groupRoot_residue Msys (TypeBSpinCoverSource.Omega N)
  have spinLifts : rootSpin.lift = oldRoot.lift :=
    spinLifts_of_residue parameters (rank3 rank) centre Msys rootSpin oldRoot
      compatibleSpin oldCompatible
  have matrixLifts : rootX.lift = oldRoot.lift :=
    matrixLifts_of_residue parameters (rank3 rank) centre C Msys rootX oldRoot
      compatibleX oldCompatible
  have rootEqual : rootSpin = canonicalSpinRoot parameters (rank3 rank) centre oldRoot :=
    spinRoot_eq_canonical parameters (rank3 rank) centre oldRoot rootSpin spinLifts
  have blockEqual : spinMatrixBlockEquiv parameters (rank3 rank) C centre
      oldRoot centralBlocks bSpin = bX :=
    spinMatrixBlock_eq_principal parameters (rank3 rank) C centre oldRoot centralBlocks
      matrixBlocks bSpin principalSpin bX principalX
  rw [rootEqual, ← blockEqual]
  exact spinMatrixBrauerFibreEquiv parameters (rank3 rank) C centre oldRoot rootX
    matrixLifts kernel regular centralBlocks bSpin

include C centre compatibleSpin compatibleX kernel regular centralBlocks matrixBlocks
  principalSpin principalX in
/-- Cardinality transport has no independent numerical premise. -/
theorem principalBrauer_card_eq :
    Nat.card (BrauerFibre rootX bX) = Nat.card (BrauerFibre rootSpin bSpin) :=
  (Nat.card_congr (principalBrauerEquiv parameters rank N C centre Msys rootSpin rootX
    compatibleSpin compatibleX kernel regular centralBlocks matrixBlocks
    bSpin principalSpin bX principalX)).symm

section Count

variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

include C centre compatibleSpin compatibleX kernel regular centralBlocks matrixBlocks
  principalX in
/-- Combine the accepted rational-class/principal-character equality with
only the new rational Spin class formula. No second Brauer-count source is
accepted, and U/D are the explicit admissible partition expressions. -/
theorem omega_principal_card
    (count : TypeBAllRankGGGR.BasisPhysical.PrincipalRationalClassCount
      parameters rank rootSpin bSpin principalSpin)
    (rationalClassCard : Nat.card (UnipotentClass (r := r) (N := N)) =
      TypeBAllRankPrincipalCriterionUpperCorrespondence.U n +
        TypeBAllRankPrincipalCriterionUpperCorrespondence.D n) :
    Nat.card (BrauerFibre rootX bX) =
      TypeBAllRankPrincipalCriterionUpperCorrespondence.U n +
        TypeBAllRankPrincipalCriterionUpperCorrespondence.D n := by
  calc
    Nat.card (BrauerFibre rootX bX) = Nat.card (BrauerFibre rootSpin bSpin) :=
      principalBrauer_card_eq parameters rank N C centre Msys rootSpin rootX
        compatibleSpin compatibleX kernel regular centralBlocks matrixBlocks
        bSpin principalSpin bX principalX
    _ = Nat.card (UnipotentClass (r := r) (N := N)) := count.card_eq.symm
    _ = _ := rationalClassCard

end Count

include centre compatibleSpin compatibleX kernel regular centralBlocks matrixBlocks
  principalSpin principalX in
/-- The final application discharges spinFixed with the accepted all-rank
principal selector on these very data. This helper adds only calibrated
transport along the actual Spin-to-matrix projection. -/
theorem omega_field_fixed_of_spin_fixed
    (fieldSource : FieldActionSource n F r f parameters N)
    (spinFixed : ∀ (e : FieldGroup f) (theta : IBr rootSpin),
      Supported rootSpin bSpin theta →
        IrreducibleBrauerCharacter.twist rootSpin theta (spinFieldAction n F fieldSource e) =
          theta) :
    ∀ (e : FieldGroup f) (phi : IBr rootX), Supported rootX bX phi →
      IrreducibleBrauerCharacter.twist rootX phi
        (omegaAction parameters rank N C fieldSource e) = phi :=
  TypeBAllRankPrincipalCriterionCarriers.matrix_field_fixed_of_spin_fixed
    parameters rank N C fieldSource centre Msys rootSpin rootX compatibleSpin compatibleX
    kernel regular centralBlocks matrixBlocks bSpin principalSpin bX principalX spinFixed

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionBrauerTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
