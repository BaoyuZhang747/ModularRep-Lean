import ModularRep.PaperProofs.TypeBRankThreePrincipalCoverSplitting
import ModularRep.PaperProofs.TypeBRankThreePrincipalMatchedInertia

/-!
# The same derived principal correspondence on Omega and SO

The count-derived seed descends through the actual Brauer orbit quotient
using the covering relation calibrated to the same modular system. The
SO map retains every constituent and covering anchor of that chosen seed.
Its matched matrix inertias and common Hall products are then deductions.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalSOMatchingSplitting

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCentralKernelInertia TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalOrbitBinding TypeBRankThreePrincipalBrauerOrbitBinding
open TypeBGreenPrincipalConstituentSource NavarroCoveringBrauerExtension
open TypeBRankThreePrincipalCoveredInertia TypeBRankThreePrincipalMatchedInertia
open TypeBCliffordOrthogonalAmbientQuotient
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {r f : ℕ} [CharP F r]
  {S : OmegaWeightSource (k := k) (K := K) F}
  {SH : SOWeightSource (k := k) (K := K) F}
  {root : PrimeRegularRootEmbedding 2 k K (G F)}
  {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
  {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
  {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
  {literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val}
  {literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val}
  {delta : H F} {indexTwo : (G F).index = 2} {outside : delta ∉ G F}
  {parameters : OddFieldParameters F r f} {notThree : Nat.card F ≠ 3}
  {Msys : ModularSystem 2 K O k}
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  [HasEnoughRootsOfUnity K (Nat.card (H F))]
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta indexTwo outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

local notation "seed" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "seedDelta" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv_delta covering counts roots fieldScope
    green principalLift clifford principalRestriction

/-- The chosen derived seed sends a Brauer orbit to one actual SO cover. -/
def orbitWeightMap : PrincipalBrauerOrbit F S literal root b hb → SOWeight F SH bH :=
  Quotient.lift (fun theta => covering.cover (seed theta)) (by
    intro theta eta related
    have forward :=
      (principalBrauerOrbitRel_iff F S literal root b hb theta eta).mp related
    obtain (equal | equal) :=
      (exists_brauerStep_iff F S literal root b hb delta indexTwo outside theta eta).mp forward
    · rw [equal]
    · rw [equal, seedDelta]
      exact (covering.cover_action (seed theta)).symm)

@[simp] theorem orbitWeightMap_mk (theta : OmegaBrauer F root b) :
    orbitWeightMap covering counts roots fieldScope green principalLift clifford
      principalRestriction (Quotient.mk _ theta) = covering.cover (seed theta) := rfl

theorem orbitWeightMap_injective : Function.Injective
    (orbitWeightMap covering counts roots fieldScope green principalLift clifford
      principalRestriction) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro theta eta equal
  have sameCover : covering.cover (seed theta) = covering.cover (seed eta) := equal
  have weights := (covering.cover_eq_iff (seed theta) (seed eta)).mp sameCover
  have characters : eta = theta ∨
      eta = brauerPermutation F S literal root b hb delta indexTwo theta := by
    rcases weights with equal | equal
    · exact Or.inl ((seed).injective equal)
    · exact Or.inr ((seed).injective (equal.trans (seedDelta theta).symm))
  apply Quotient.sound
  exact (principalBrauerOrbitRel_iff F S literal root b hb theta eta).mpr
    ((exists_brauerStep_iff F S literal root b hb delta indexTwo outside theta eta).mpr
      characters)

theorem orbitWeightMap_surjective : Function.Surjective
    (orbitWeightMap covering counts roots fieldScope green principalLift clifford
      principalRestriction) := by
  intro v
  obtain ⟨w, hw⟩ := covering.cover_surjective v
  obtain ⟨theta, htheta⟩ := (seed).surjective w
  refine ⟨Quotient.mk _ theta, ?_⟩
  change covering.cover (seed theta) = v
  rw [htheta]
  exact hw

def orbitWeightEquiv : PrincipalBrauerOrbit F S literal root b hb ≃ SOWeight F SH bH :=
  Equiv.ofBijective
    (orbitWeightMap covering counts roots fieldScope green principalLift clifford
      principalRestriction)
    ⟨orbitWeightMap_injective covering counts roots fieldScope green principalLift clifford
        principalRestriction,
      orbitWeightMap_surjective covering counts roots fieldScope green principalLift clifford
        principalRestriction⟩

@[simp] theorem orbitWeightEquiv_mk (theta : OmegaBrauer F root b) :
    orbitWeightEquiv covering counts roots fieldScope green principalLift clifford
      principalRestriction (Quotient.mk _ theta) = covering.cover (seed theta) := rfl

/-- The SO correspondence uses precisely the already chosen derived seed. -/
def principalSOEquiv : SOBrauer F rootH bH ≃ SOWeight F SH bH :=
  (principalOrbitEquiv F S literal root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift clifford principalRestriction).symm.trans
    (orbitWeightEquiv covering counts roots fieldScope green principalLift clifford
      principalRestriction)

theorem principalSOEquiv_principalAbove (theta : OmegaBrauer F root b) :
    principalSOEquiv covering counts roots fieldScope green principalLift clifford
      principalRestriction
      (principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift theta) = covering.cover (seed theta) := by
  change orbitWeightEquiv covering counts roots fieldScope green principalLift clifford
      principalRestriction
      ((principalOrbitEquiv F S literal root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift clifford principalRestriction).symm
        (principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo
          green principalLift theta)) = _
  rw [← principalOrbitEquiv_mk F S literal root b hb rootH bH hbH roots fieldScope
    indexTwo green principalLift clifford principalRestriction theta, Equiv.symm_apply_apply]
  rfl

theorem occurs_iff_principalSOEquiv_eq (Phi : SOBrauer F rootH bH)
    (theta : OmegaBrauer F root b) :
    BrauerOccursInRestriction (G F) rootH root Phi.val theta.val ↔
      principalSOEquiv covering counts roots fieldScope green principalLift clifford
        principalRestriction Phi = covering.cover (seed theta) := by
  rw [principalAbove_occurs_iff F root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift theta Phi]
  constructor
  · intro equal
    rw [← equal]
    exact principalSOEquiv_principalAbove covering counts roots fieldScope green
      principalLift clifford principalRestriction theta
  · intro equal
    apply (principalSOEquiv covering counts roots fieldScope green principalLift clifford
      principalRestriction).injective
    exact (principalSOEquiv_principalAbove covering counts roots fieldScope green
      principalLift clifford principalRestriction theta).trans equal.symm

/-- Both sides refer to the literal restriction and calibrated DGN relation. -/
theorem principalSOEquiv_occurs_iff_coversClass
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) :
    BrauerOccursInRestriction (G F) rootH root Phi.val theta.val ↔
      TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
        (principalSOEquiv covering counts roots fieldScope green principalLift clifford
          principalRestriction Phi).val (seed theta).val := by
  rw [covering.covers_iff]
  exact (occurs_iff_principalSOEquiv_eq covering counts roots fieldScope green principalLift
    clifford principalRestriction Phi theta).trans eq_comm

/-- Each SO image has exactly the constituent and covering description. -/
theorem principalSOEquiv_eq_iff_exists_pair (Phi : SOBrauer F rootH bH)
    (v : SOWeight F SH bH) :
    principalSOEquiv covering counts roots fieldScope green principalLift clifford
      principalRestriction Phi = v ↔
        ∃ theta : OmegaBrauer F root b,
          BrauerOccursInRestriction (G F) rootH root Phi.val theta.val ∧
            TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn v.val (seed theta).val := by
  constructor
  · intro equal
    obtain ⟨theta, aboveEqual⟩ :=
      principalAbove_surjective F root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift clifford principalRestriction Phi
    have occurs := (principalAbove_occurs_iff F root b hb rootH bH hbH roots fieldScope
      indexTwo green principalLift theta Phi).mpr aboveEqual
    refine ⟨theta, occurs, ?_⟩
    rw [← equal]
    exact (principalSOEquiv_occurs_iff_coversClass covering counts roots fieldScope green
      principalLift clifford principalRestriction Phi theta).mp occurs
  · rintro ⟨theta, occurs, covers⟩
    have matched := (occurs_iff_principalSOEquiv_eq covering counts roots fieldScope green
      principalLift clifford principalRestriction Phi theta).mp occurs
    exact matched.trans ((covering.covers_iff v (seed theta)).mp covers)

/-- Actual SO stabilizer membership is constant in a calibrated covering fibre. -/
theorem weightStep_fix_iff_of_cover_eq (h : H F) (w v : OmegaWeight F S b)
    (sameCover : covering.cover w = covering.cover v) :
    weightStep F S literal b hb h w = w ↔ weightStep F S literal b hb h v = v := by
  by_cases hh : h ∈ G F
  · rw [weightStep_eq_of_mem F S literal b hb h hh w,
      weightStep_eq_of_mem F S literal b hb h hh v]
    exact iff_of_true rfl rfl
  · rw [weightStep_eq_delta_of_notMem F S literal b hb delta indexTwo outside h hh w,
      weightStep_eq_delta_of_notMem F S literal b hb delta indexTwo outside h hh v]
    change weightPermutation F S literal b hb delta indexTwo w = w ↔
      weightPermutation F S literal b hb delta indexTwo v = v
    obtain equal | equal := (covering.cover_eq_iff w v).mp sameCover
    · rw [equal]
    · rw [equal]
      exact (weightPermutation F S literal b hb delta indexTwo).injective.eq_iff.symm

theorem classInertia_eq_of_cover_eq (w v : OmegaWeight F S b)
    (sameCover : covering.cover w = covering.cover v) :
    classInertia F S b w = classInertia F S b v := by
  ext h
  change (conjugationOp (G F) h • w.val = w.val) ↔
    (conjugationOp (G F) h • v.val = v.val)
  have fixed := weightStep_fix_iff_of_cover_eq covering h w v sameCover
  constructor
  · intro hw
    exact congrArg Subtype.val (fixed.mp (Subtype.ext hw))
  · intro hv
    exact congrArg Subtype.val (fixed.mpr (Subtype.ext hv))

/-- Every actual constituent and covered class have equal SO class inertias. -/
theorem principalSOEquiv_matched_classInertia_eq
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (principalSOEquiv covering counts roots fieldScope green principalLift clifford
        principalRestriction Phi).val w.val) :
    classInertia F S b w = T (G F) root theta.val := by
  have anchor := (occurs_iff_principalSOEquiv_eq covering counts roots fieldScope green
    principalLift clifford principalRestriction Phi theta).mp occurs
  have sameCover : covering.cover (seed theta) = covering.cover w :=
    anchor.symm.trans ((covering.covers_iff _ w).mp covered).symm
  exact (classInertia_eq_of_cover_eq covering (seed theta) w sameCover).symm.trans
    (seed_classInertia_eq F S literal b hb delta indexTwo outside root seed seedDelta theta)

section ActualMatrixAmbient

variable (N : NormSource 3 F)
  (fieldSource : FieldActionSource 3 F r f parameters N)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F r f parameters (Nat.le_refl 3) N)

/-- The equalities use the same literal matrix SO factor of the field action. -/
theorem principalSOEquiv_matched_criterion_inertia_eq
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (principalSOEquiv covering counts roots fieldScope green principalLift clifford
        principalRestriction Phi).val w.val) :
    TypeBCriterionHypotheses.brauerMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) root theta.val =
    TypeBCriterionHypotheses.weightMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) w.val := by
  rw [matrix_brauerMInertia_eq F root b parameters N fieldSource orthogonal theta,
    matrix_weightMInertia_eq F S b parameters N fieldSource orthogonal w]
  exact (principalSOEquiv_matched_classInertia_eq covering counts roots fieldScope green
    principalLift clifford principalRestriction Phi theta w occurs covered).symm

/-- The common actual Hall preimage gives the matched principal product. -/
theorem principalSOEquiv_matched_criterion_hall_product_eq
    (hall : TypeBCriterionHypotheses.HallData (G F) 2)
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (principalSOEquiv covering counts roots fieldScope green principalLift clifford
        principalRestriction Phi).val w.val) :
    (TypeBCriterionHypotheses.brauerMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) root theta.val : Set (H F)) *
        (hall.preimage : Set (H F)) =
    (TypeBCriterionHypotheses.weightMInertia (G F)
      (soFieldAction 3 F parameters (Nat.le_refl 3) N orthogonal fieldSource)
      (matrixNaturalAction F parameters N fieldSource orthogonal) w.val : Set (H F)) *
        (hall.preimage : Set (H F)) := by
  rw [principalSOEquiv_matched_criterion_inertia_eq covering counts roots fieldScope green
    principalLift clifford principalRestriction N fieldSource orthogonal Phi theta w
    occurs covered]

end ActualMatrixAmbient

end ModularRep.PaperProofs.TypeBRankThreePrincipalSOMatchingSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
