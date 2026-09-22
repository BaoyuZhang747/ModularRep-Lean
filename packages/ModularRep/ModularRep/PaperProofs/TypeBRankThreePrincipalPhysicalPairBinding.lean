import ModularRep.PaperProofs.TypeBRankThreePrincipalRawInertiaBinding

/-!
# The specified pair of the actual principal correspondence

The character, raw weight and root are transported into the full matrix
SO and field ambient. The same computed SO correspondence supplies the
local-inertia inclusion for every raw representative. Specified catalogues
remain on the actual nested groups. Local reduction uses the given
weight's own character and the same modular system. The final abbreviation
defines the complete pair-witness type without producing a witness.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalPhysicalPairBinding

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCentralKernelInertia TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalFieldNaturality TypeBRankThreePrincipalFieldMatchingSplitting
open TypeBRankThreePrincipalMatchedInertia TypeBGreenPrincipalConstituentSource
open TypeBCliffordOrthogonalAmbientQuotient TypeBCliffordOrthogonalAmbientActionBinding
open TypeBCliffordOrthogonalFullFieldBinding NavarroCoveringBrauerExtension
open TypeBCriterionHypotheses TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open CyclicOuterLemma37Concrete TypeBSemidirectFixedFieldFactorization
open TypeBCentralKernelCarriers TypeBCentralKernelTripleCertificate
open TypeBCentralKernelTripleCarriers
open TypeBCentralKernelTripleRootFamily TypeBModularGroupRootBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] {r f : ℕ} [CharP F r]
  [HasEnoughRootsOfUnity K (Nat.card (H F))]
  {S : OmegaWeightSource (k := k) (K := K) F}
  {SH : SOWeightSource (k := k) (K := K) F}
  {root : PrimeRegularRootEmbedding 2 k K (G F)}
  {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
  {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
  {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
  {literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val}
  {literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val}
  {indexTwo : (G F).index = 2}
  {parameters : OddFieldParameters F r f} {N : NormSource 3 F}
  {fieldSource : FieldActionSource 3 F r f parameters N}
  {C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N}
  {Msys : ModularSystem 2 K O k}
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb indexTwo)
  (roots : TypeBGreenPrincipalConstituentSource.RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)
  {coefficient : SpathCoefficientField 2 k Msys.prime}
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  (fyz : TypeBRankThreePrincipalWeightFieldSplitting.FYZCorollary363SplittingSource
    F r f parameters Msys coefficient root rootH
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys root rootCalibration)
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys rootH rootHCalibration)
    S SH literal literalH guard guardH b hb bH hbH)
  {delta : H F} {outside : delta ∉ G F} {notThree : Nat.card F ≠ 3}
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta indexTwo outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C
local notation "Ghat" => embeddedG (G F) matrixField
local notation "rootHat" => TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) matrixField root
local notation "calibrationHat" =>
  TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue
    (G F) matrixField Msys root rootCalibration
local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction

variable (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b)
  (w : OmegaWeight F S b)
  (occurs : BrauerOccursInRestriction (G F) rootH root Phi.val theta.val)
  (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
    (TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv
      covering counts roots fieldScope green principalLift clifford principalRestriction Phi).val w.val)
  (W : CharacterWeight 2 K (G F))
  (representative : TypeBSpinRawWeightSeparationBinding.classOf (G F) W = w.val)

local notation "thetaHat" => TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root theta.val
local notation "WHat" => TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) matrixField W
local notation "pairInclusion" =>
  TypeBRankThreePrincipalRawInertiaBinding.principalSOEquiv_U_le_T
    gggr roots fieldScope green principalLift clifford principalRestriction fyz covering counts
    Phi theta w occurs covered W representative

variable
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (blocks :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)
      (matrixNaturalAction F parameters N fieldSource C)
    PhysicalBlockFamily (k := k)
      (inside
        (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource))
        (T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource))
          (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F)
            (soFieldAction 3 F parameters le_rfl N C fieldSource) root)
          (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F)
            (soFieldAction 3 F parameters le_rfl N C fieldSource) root theta.val)))
      (inside
        (U (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource))
          (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F)
            (soFieldAction 3 F parameters le_rfl N C fieldSource) W))
        (T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource))
          (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F)
            (soFieldAction 3 F parameters le_rfl N C fieldSource) root)
          (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F)
            (soFieldAction 3 F parameters le_rfl N C fieldSource) root theta.val))))

/-- The actual inclusion is computed from the same matching inputs. -/
def principalSOEquiv_pairData :=
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  TypeBCentralKernelPairSplittingBinding.pairData Msys Ghat rootHat calibrationHat
    thetaHat WHat pairInclusion blocks

local notation "pairData" =>
  principalSOEquiv_pairData gggr roots fieldScope green principalLift clifford
    principalRestriction fyz covering counts Phi theta w occurs covered W representative blocks

theorem principalSOEquiv_pairData_quotientRoot :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    (pairData).quotientRoot = groupRoot Msys (NormalizerQuotient (WHat).subgroup) := rfl

theorem principalSOEquiv_pairData_ambientRoot :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    (pairData).ambientRoot = groupRoot Msys (T Ghat rootHat thetaHat) := rfl

theorem principalSOEquiv_pairData_blocks :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    (pairData).blocks = blocks := rfl

/-- The complete root and block data on the actual nested pair. -/
def principalSOEquiv_tripleData :=
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  TypeBCentralKernelConjugatePairBinding.tripleData
    Ghat rootHat thetaHat WHat pairInclusion pairData

local notation "tripleData" =>
  principalSOEquiv_tripleData gggr roots fieldScope green principalLift clifford
    principalRestriction fyz covering counts Phi theta w occurs covered W representative blocks

/-- The base character is the same original theta through both literal inclusions. -/
def principalSOEquiv_baseCharacter :=
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  TypeBCentralKernelConjugatePairBinding.baseCharacter
    Ghat rootHat thetaHat WHat pairInclusion pairData

local notation "baseCharacter" =>
  principalSOEquiv_baseCharacter gggr roots fieldScope green principalLift clifford
    principalRestriction fyz covering counts Phi theta w occurs covered W representative blocks

theorem principalSOEquiv_tripleData_baseRoot_lift :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    (tripleData).base.iota.lift = root.lift := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  funext z
  exact (TypeBCentralKernelTripleCharacters.baseRoot_lift Ghat rootHat thetaHat z).trans
    (congrFun (TypeBCriterionEmbeddedPairBinding.embeddedRoot_lift (G F) matrixField root) z)

theorem principalSOEquiv_tripleData_localRoot :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    (tripleData).localData.iota = groupRoot Msys
      (localBase (inside Ghat (T Ghat rootHat thetaHat))
        (inside (U Ghat WHat) (T Ghat rootHat thetaHat))) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  exact TypeBCentralKernelPairSplittingBinding.localRoot_eq_groupRoot
    Msys Ghat rootHat thetaHat WHat pairInclusion

theorem principalSOEquiv_baseCharacter_value :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    ∀ x : PrimeRegularElement (G := inside Ghat (T Ghat rootHat thetaHat)) 2,
      (baseCharacter).val x = theta.val.val
        (PrimeRegularElement.map (TypeBCriterionEmbeddedPairBinding.baseEquiv
          (G F) matrixField).symm.toMonoidHom
          (PrimeRegularElement.map (TypeBCentralKernelTripleCharacters.baseEquiv
            Ghat rootHat thetaHat).symm.toMonoidHom x)) := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  intro x
  exact (TypeBCentralKernelConjugatePairBinding.baseCharacter_value
    Ghat rootHat thetaHat WHat pairInclusion pairData x).trans
    (congrArg (fun chi : PrimeRegularClassFunction K Ghat 2 =>
      chi (PrimeRegularElement.map (TypeBCentralKernelTripleCharacters.baseEquiv
        Ghat rootHat thetaHat).symm.toMonoidHom x))
      (TypeBCriterionEmbeddedPairBinding.brauerEquiv_val (G F) matrixField root theta.val))

/-- Enough roots for Omega and its image are derived from the actual SO guard. -/
def principalSOEquiv_localCharacter :=
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  letI : HasEnoughRootsOfUnity K (Nat.card (G F)) :=
    HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F) matrixField
  TypeBCentralKernelPairSplittingBinding.localCharacter Msys Ghat rootHat calibrationHat
    thetaHat WHat pairInclusion navarro blocks

local notation "localCharacter" =>
  principalSOEquiv_localCharacter gggr roots fieldScope green principalLift clifford
    principalRestriction fyz covering counts Phi theta w occurs covered W representative navarro blocks

theorem principalSOEquiv_localCharacter_reduction :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    ∀ x : PrimeRegularElement
      (G := localBase (inside Ghat (T Ghat rootHat thetaHat))
        (inside (U Ghat WHat) (T Ghat rootHat thetaHat))) 2,
      (WHat).localCharacter (TypeBCentralKernelWeightTransport.localMk (WHat).subgroup
        ((TypeBCentralKernelTripleCharacters.localEquiv
          Ghat rootHat thetaHat WHat pairInclusion).symm x.val)) =
            (localCharacter).val x := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  letI : HasEnoughRootsOfUnity K (Nat.card (G F)) :=
    HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F) matrixField
  exact TypeBCentralKernelPairSplittingBinding.localCharacter_reduction Msys
    Ghat rootHat calibrationHat thetaHat WHat pairInclusion navarro blocks

/-- The regular value is that of the original W.localCharacter on the
corresponding actual normalizer point. The point equation is only an anchor. -/
theorem principalSOEquiv_localCharacter_original_value :
    letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    ∀ (x : Subgroup.normalizer (W.subgroup : Set (G F)))
      (y : PrimeRegularElement
        (G := localBase (inside Ghat (T Ghat rootHat thetaHat))
          (inside (U Ghat WHat) (T Ghat rootHat thetaHat))) 2),
      TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) matrixField x =
        (TypeBCentralKernelTripleCharacters.localEquiv
          Ghat rootHat thetaHat WHat pairInclusion).symm y.val →
      W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup x) =
        (localCharacter).val y := by
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  letI : HasEnoughRootsOfUnity K (Nat.card (G F)) :=
    HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F) matrixField
  intro x y point
  exact (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv_localCharacter
    (G F) matrixField W x
    ((TypeBCentralKernelTripleCharacters.localEquiv
      Ghat rootHat thetaHat WHat pairInclusion).symm y.val) point).symm.trans
    (TypeBCentralKernelPairSplittingBinding.localCharacter_reduction Msys
      Ghat rootHat calibrationHat thetaHat WHat pairInclusion navarro blocks y)

/-- Only the witness type is instantiated. No initial witness is supplied. -/
abbrev principalSOEquiv_PairWitness :=
  letI : NeZero f := TypeBMatrixAmbientOrdinaryRoots.fieldDegreeNeZero parameters
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  letI : HasEnoughRootsOfUnity K (Nat.card (G F)) :=
    HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F) matrixField
  TypeBCentralKernelPairSplittingBinding.PairWitness Msys Ghat rootHat calibrationHat
    thetaHat WHat pairInclusion navarro blocks

end ModularRep.PaperProofs.TypeBRankThreePrincipalPhysicalPairBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
