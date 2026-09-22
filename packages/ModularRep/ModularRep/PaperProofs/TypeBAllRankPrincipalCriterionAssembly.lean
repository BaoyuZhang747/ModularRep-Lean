import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionMatrixStructure
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionUpperCorrespondence
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionWeightFieldSource
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionExtensions

/-!
# Construction on the actual SO/Omega principal fibres

The final application supplies two internally derived facts: field
fixation of the Omega principal Brauer fibre and its U(n)+D(n) count.
Every other input below is an independently scoped structural, specified,
covering, scalar-count or published source on the displayed carriers.

The upper correspondence and its matched inertia equality are constructed
from one/two fibres and the independent counts. The same modular-system
calibrations give root agreement. The actual index-two quotient determines
the trivial Hall subgroup; no Hall, matching, selector or completed
downstairs condition is a parameter. FYZ is used only at the two matrix
Frobenius generators and on the same block-scoped specified weight data.

The four extension/selector fields use the existing honest cyclic
extension consumers. Applying the uniform one-block BS source returns
normalized packets on the same output matching. This module is an
internal construction helper, not a source asserting that Type B field
fixation alone implies the criterion. Its external source inhabitants and
specified/source interpretation remain the explicit E1/E2/U boundary.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionAssembly

open ModularRep CharacterWeight TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCriterionHypotheses TypeBLocalReductionInstantiation
open TypeBQ3PrincipalWeightInflation
open TypeBAllRankPrincipalCriterionCarriers
open TypeBAllRankPrincipalCriterionFixedBlockSource
open TypeBGreenPrincipalConstituentSource NavarroCoveringBrauerExtension

local instance finiteFintype (Y : Type) [Finite Y] : Fintype Y := Fintype.ofFinite Y

attribute [local instance]
  TypeBAllRankPrincipalCriterionUpperCorrespondence.physicalSubgroupFintype

variable {n r f : ℕ} {F k K O : Type}
  [fieldExponent : NeZero f]
  [Field F] [Finite F] [CharP F r]
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F r f parameters (rank3 rank) N)
  (S : FieldActionSource n F r f parameters N)

local instance fieldActorsCyclic : IsCyclic (FieldGroup f) :=
  TypeBAllRankPrincipalCriterionMatrixStructure.fieldGroup_cyclic

local notation "fieldH" => fieldAction parameters rank N C S
local notation "fieldX" => omegaAction parameters rank N C S
local notation "natural" => matrixNaturalAction parameters rank N C S
local notation "idx" => omega_index_two parameters rank N C

variable
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
  (fullCover : EvenFieldFLZ318FixedTheoremGate.IsUniversalCentralExtension
    (spinProjection parameters rank N C))
  (centreClifford : TypeBCliffordCentreSource.CentreSource n F parameters
    ((by decide : 1 ≤ 3).trans (rank3 rank)))
  (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism S).ker =
    TypeBAutomorphismSource.embeddedCenter S)
  (naturalSurjective : Function.Surjective (TypeBAutomorphismSource.ambientAutomorphism S))
  (simple : IsSimpleGroup (X n F)) (nonabelian : ¬ IsMulCommutative (X n F))
  (Msys : ModularSystem 2 K O k)
  [HasEnoughRootsOfUnity K (Nat.card (Ambient (fieldAction parameters rank N C S)))]

/-- Derive SO roots from the one existing ambient-root guard, with the
actual parameters supplied explicitly; this is not a search instance. -/
def soOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card (H n F)) :=
  TypeBAllRankPrincipalCriterionMatrixStructure.ordinaryRoots_of_ambientRoots
    parameters rank N C S

/-- The helper consumes SO roots which both public theorems derive locally. -/
def omegaOrdinaryRoots
    [HasEnoughRootsOfUnity K (Nat.card (H n F))] :
    HasEnoughRootsOfUnity K (Nat.card (X n F)) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G n F))

local notation "countU" => TypeBAllRankPrincipalCriterionUpperCorrespondence.U n
local notation "countD" => TypeBAllRankPrincipalCriterionUpperCorrespondence.D n

include fieldExponent centreSpin fullCover centreClifford naturalKernel naturalSurjective
  simple nonabelian in
/-- Construct every published antecedent on these actual SO/Omega carriers.
The only two internally supplied global facts are the Omega character
count and fixation; all upper, structural, Hall and selector data are derived. -/
theorem exists_fixedBlockHypotheses :
    letI : HasEnoughRootsOfUnity K (Nat.card (H n F)) :=
      soOrdinaryRoots parameters rank N C S
    letI : HasEnoughRootsOfUnity K (Nat.card (X n F)) :=
      omegaOrdinaryRoots (n := n) (F := F) (K := K)
    ∀ (rootX : PrimeRegularRootEmbedding 2 k K (X n F))
      (rootH : PrimeRegularRootEmbedding 2 k K (H n F))
      (compatibleX : RootResidueCompatible Msys rootX)
      (compatibleH : RootResidueCompatible Msys rootH)
      (coefficient : SpathCoefficientField 2 k Msys.prime)
      (SX : CoverWeightSource (k := k) (K := K) (X n F))
      (SH : CoverWeightSource (k := k) (K := K) (H n F))
      (bX : LiteralPrimitiveBlock k (X n F)) (principalX : IsPrincipal bX)
      (bH : LiteralPrimitiveBlock k (H n F)) (principalH : IsPrincipal bH)
      (physicalX : PhysicalWeightCalibration Msys rootX SX bX)
      (physicalH : PhysicalWeightCalibration Msys rootH SH bH),
    ∀ (green : Green811Source (G n F) rootH rootX (TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree parameters rank N C Msys rootX rootH compatibleX compatibleH) coefficient
        (quotient_isTwoGroup (G n F) (omega_index_two parameters rank N C)))
      (principalLift : PrincipalLiftSource (G n F) rootH rootX (TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree parameters rank N C Msys rootX rootH compatibleX compatibleH) coefficient
        (quotient_isTwoGroup (G n F) (omega_index_two parameters rank N C)))
      (clifford : Clifford85_87Source (G n F) rootH rootX (TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree parameters rank N C Msys rootX rootH compatibleX compatibleH) coefficient)
      (principalRestriction : PrincipalRestrictionSource (G n F) rootH rootX (TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree parameters rank N C Msys rootX rootH compatibleX compatibleH) coefficient)
      (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G n F) Msys)
      (covering : TypeBAllRankPrincipalCriterionUpperCorrespondence.PublishedPrincipalCovering
        (G n F) SX bX SH bH Msys dgn)
      (soBrauerCount : Nat.card (BrauerFibre rootH bH) = (TypeBAllRankPrincipalCriterionUpperCorrespondence.U n))
      (soWeightCount : Nat.card (SH.Fibre bH) = (TypeBAllRankPrincipalCriterionUpperCorrespondence.U n))
      (weightDoubleCount : Nat.card {v : SH.Fibre bH //
        Nat.card {w : SX.Fibre bX // TypeBWeightCoveringSplittingSource.CoversClass
          (G n F) dgn v.val w.val} = 2} = (TypeBAllRankPrincipalCriterionUpperCorrespondence.D n))
      (weightField : TypeBAllRankPrincipalCriterionWeightFieldSource.FYZCorollary363Source
        F parameters rank N C S Msys coefficient rootX rootH compatibleX compatibleH
        SX SH bX principalX bH principalH physicalX physicalH)
      (brauerCyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
      (ordinaryCyclic : ∀ (Y : Type) [Group Y] [Finite Y]
        [HasEnoughRootsOfUnity K (Nat.card Y)],
          TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K Y),
    ∀ (omegaBrauerCount : Nat.card (BrauerFibre rootX bX) = countU + countD)
          (omegaFixed : ∀ (e : FieldGroup f) (phi : BrauerFibre rootX bX),
            IrreducibleBrauerCharacter.twist rootX phi.val (fieldX e) = phi.val),
    Nonempty (FixedBlockHypotheses (G n F) fieldH natural Msys rootX rootH
      SX SH bX bH dgn (TypeBPrincipalCommonTrivialTwist.radicalLift (G n F) idx rootH)) := by
  classical
  letI : HasEnoughRootsOfUnity K (Nat.card (H n F)) :=
    soOrdinaryRoots parameters rank N C S
  letI : HasEnoughRootsOfUnity K (Nat.card (X n F)) :=
    omegaOrdinaryRoots (n := n) (F := F) (K := K)
  intro rootX rootH compatibleX compatibleH coefficient SX SH bX principalX bH principalH
    physicalX physicalH
  let roots := TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree
    parameters rank N C Msys rootX rootH compatibleX compatibleH
  let lift := TypeBPrincipalCommonTrivialTwist.radicalLift (G n F) idx rootH
  intro green principalLift clifford principalRestriction dgn covering
    soBrauerCount soWeightCount weightDoubleCount weightField brauerCyclic ordinaryCyclic
  intro omegaBrauerCount omegaFixed
  letI := SX.operations.ambientBlockData.fintypeBlock
  let structureData := TypeBAllRankPrincipalCriterionMatrixStructure.structuralData
    parameters rank N C S centreSpin fullCover centreClifford naturalKernel naturalSurjective
    rootX bX simple nonabelian
    (TypeBRankThreePrincipalFieldNaturality.physicalDecomposition SX physicalX.literal) principalX
  have characterUnion := TypeBAllRankPrincipalCriterionUpperCorrespondence.character_union
    (G n F) rootX bX principalX rootH bH principalH roots coefficient idx
    principalLift clifford principalRestriction
  have weightsFixed (e : FieldGroup f) (w : SH.Fibre bH) :
      CharacterWeight.rightTwistConjugacyClass (fieldH e) w.val = w.val :=
    TypeBAllRankPrincipalCriterionWeightFieldSource.so_field_fixed weightField e w
  obtain ⟨upper, matchedInertia, _⟩ :=
    TypeBAllRankPrincipalCriterionUpperCorrespondence.exists_upperCorrespondence
      parameters rank N C S SX physicalX.literal rootX bX principalX
      SH physicalH.literal rootH bH principalH roots coefficient green principalLift
      clifford principalRestriction Msys dgn covering
      soBrauerCount soWeightCount omegaBrauerCount weightDoubleCount omegaFixed weightsFixed
  have brauerInrFixed (phi : BrauerFibre rootX bX) (e : FieldGroup f) :
      IrreducibleBrauerCharacter.twist rootX phi.val
        ((natural).hom (SemidirectProduct.inr e)) = phi.val := by
    rw [TypeBAllRankPrincipalCriterionMatrixStructure.matrixNaturalAction_inr]
    exact omegaFixed e phi
  have weightInrFixed (w : SX.Fibre bX) (e : FieldGroup f) :
      CharacterWeight.rightTwistConjugacyClass
        ((natural).hom (SemidirectProduct.inr e)) w.val = w.val := by
    rw [TypeBAllRankPrincipalCriterionMatrixStructure.matrixNaturalAction_inr]
    exact TypeBAllRankPrincipalCriterionWeightFieldSource.omega_field_fixed weightField e w
  refine ⟨{
    coefficient := coefficient
    cover := structureData.cover
    divides_simple_order := structureData.divides_simple_order
    centralFaithful := structureData.centralFaithful
    block_invariant := structureData.block_invariant
    derived := structureData.derived
    acting_abelian := structureData.acting_abelian
    centralizer := structureData.centralizer
    natural_kernel := structureData.natural_kernel
    natural_surjective := structureData.natural_surjective
    outer_abelian := structureData.outer_abelian
    base_calibration := compatibleX
    upper_calibration := compatibleH
    roots_agree := roots
    lower_physical := physicalX
    upper_physical := physicalH
    character_union := characterUnion
    weight_union := TypeBAllRankPrincipalCriterionUpperCorrespondence.weight_union covering
    upper := upper
    hall := TypeBAllRankPrincipalCriterionMatrixStructure.canonicalHall parameters rank N C
    JG := ?_
    brauer_M := TypeBAllRankPrincipalCriterionExtensions.brauer_M_on_block
      (G n F) fieldH natural rootX bX idx brauerCyclic
    ordinary_M := TypeBAllRankPrincipalCriterionExtensions.ordinary_M_on_block
      (G n F) fieldH natural bX SX idx ordinaryCyclic
    character_selector := TypeBAllRankPrincipalCriterionExtensions.characterSelector_of_field_fixed
      (G n F) fieldH natural rootX bX rootH bH
      (fun Phi => (characterUnion Phi.val).mp Phi.property) brauerInrFixed brauerCyclic
    weight_selector := TypeBAllRankPrincipalCriterionExtensions.weightSelector_of_field_fixed
      (G n F) fieldH natural bX SX weightInrFixed ordinaryCyclic }⟩
  intro Phi phi w occurs covered
  exact congrArg
    (fun I : Subgroup (H n F) => (I : Set (H n F)) *
      ((TypeBAllRankPrincipalCriterionMatrixStructure.canonicalHall parameters rank N C).preimage :
        Set (H n F)))
    (matchedInertia Phi phi w occurs covered)

include fieldExponent centreSpin fullCover centreClifford naturalKernel naturalSurjective
  simple nonabelian in
/-- Apply the uniform fixed-block BS implication to the internally
constructed antecedents. The output keeps each normalized packet attached
to the exact output matching; `completeClauses` projects that same witness. -/
theorem exists_normalizedBlockWitness :
    letI : HasEnoughRootsOfUnity K (Nat.card (H n F)) :=
      soOrdinaryRoots parameters rank N C S
    letI : HasEnoughRootsOfUnity K (Nat.card (X n F)) :=
      omegaOrdinaryRoots (n := n) (F := F) (K := K)
    ∀ (rootX : PrimeRegularRootEmbedding 2 k K (X n F))
      (rootH : PrimeRegularRootEmbedding 2 k K (H n F))
      (compatibleX : RootResidueCompatible Msys rootX)
      (compatibleH : RootResidueCompatible Msys rootH)
      (coefficient : SpathCoefficientField 2 k Msys.prime)
      (SX : CoverWeightSource (k := k) (K := K) (X n F))
      (SH : CoverWeightSource (k := k) (K := K) (H n F))
      (bX : LiteralPrimitiveBlock k (X n F)) (principalX : IsPrincipal bX)
      (bH : LiteralPrimitiveBlock k (H n F)) (principalH : IsPrincipal bH)
      (physicalX : PhysicalWeightCalibration Msys rootX SX bX)
      (physicalH : PhysicalWeightCalibration Msys rootH SH bH),
    ∀ (green : Green811Source (G n F) rootH rootX (TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree parameters rank N C Msys rootX rootH compatibleX compatibleH) coefficient
        (quotient_isTwoGroup (G n F) (omega_index_two parameters rank N C)))
      (principalLift : PrincipalLiftSource (G n F) rootH rootX (TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree parameters rank N C Msys rootX rootH compatibleX compatibleH) coefficient
        (quotient_isTwoGroup (G n F) (omega_index_two parameters rank N C)))
      (clifford : Clifford85_87Source (G n F) rootH rootX (TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree parameters rank N C Msys rootX rootH compatibleX compatibleH) coefficient)
      (principalRestriction : PrincipalRestrictionSource (G n F) rootH rootX (TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree parameters rank N C Msys rootX rootH compatibleX compatibleH) coefficient)
      (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G n F) Msys)
      (covering : TypeBAllRankPrincipalCriterionUpperCorrespondence.PublishedPrincipalCovering
        (G n F) SX bX SH bH Msys dgn)
      (soBrauerCount : Nat.card (BrauerFibre rootH bH) = (TypeBAllRankPrincipalCriterionUpperCorrespondence.U n))
      (soWeightCount : Nat.card (SH.Fibre bH) = (TypeBAllRankPrincipalCriterionUpperCorrespondence.U n))
      (weightDoubleCount : Nat.card {v : SH.Fibre bH //
        Nat.card {w : SX.Fibre bX // TypeBWeightCoveringSplittingSource.CoversClass
          (G n F) dgn v.val w.val} = 2} = (TypeBAllRankPrincipalCriterionUpperCorrespondence.D n))
      (weightField : TypeBAllRankPrincipalCriterionWeightFieldSource.FYZCorollary363Source
        F parameters rank N C S Msys coefficient rootX rootH compatibleX compatibleH
        SX SH bX principalX bH principalH physicalX physicalH)
      (brauerCyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
      (ordinaryCyclic : ∀ (Y : Type) [Group Y] [Finite Y]
        [HasEnoughRootsOfUnity K (Nat.card Y)],
          TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K Y),
    ∀ (bs : Theorem45FixedBlockCertificate)
          (omegaBrauerCount : Nat.card (BrauerFibre rootX bX) = countU + countD)
          (omegaFixed : ∀ (e : FieldGroup f) (phi : BrauerFibre rootX bX),
            IrreducibleBrauerCharacter.twist rootX phi.val (fieldX e) = phi.val),
    Nonempty (NormalizedBlockWitness Msys rootX SX bX) := by
  classical
  letI : HasEnoughRootsOfUnity K (Nat.card (H n F)) :=
    soOrdinaryRoots parameters rank N C S
  letI : HasEnoughRootsOfUnity K (Nat.card (X n F)) :=
    omegaOrdinaryRoots (n := n) (F := F) (K := K)
  intro rootX rootH compatibleX compatibleH coefficient SX SH bX principalX bH principalH
    physicalX physicalH
  let roots := TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree
    parameters rank N C Msys rootX rootH compatibleX compatibleH
  let lift := TypeBPrincipalCommonTrivialTwist.radicalLift (G n F) idx rootH
  intro green principalLift clifford principalRestriction dgn covering
    soBrauerCount soWeightCount weightDoubleCount weightField brauerCyclic ordinaryCyclic
  intro bs omegaBrauerCount omegaFixed
  obtain ⟨hypotheses⟩ := exists_fixedBlockHypotheses parameters rank N C S
    centreSpin fullCover centreClifford naturalKernel naturalSurjective simple nonabelian
    Msys rootX rootH compatibleX compatibleH coefficient SX SH bX principalX bH principalH
    physicalX physicalH green principalLift clifford principalRestriction dgn covering
    soBrauerCount soWeightCount weightDoubleCount weightField brauerCyclic ordinaryCyclic
    omegaBrauerCount omegaFixed
  exact bs.fixedBlock (G n F) fieldH natural Msys rootX rootH SX SH bX bH dgn lift hypotheses

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
