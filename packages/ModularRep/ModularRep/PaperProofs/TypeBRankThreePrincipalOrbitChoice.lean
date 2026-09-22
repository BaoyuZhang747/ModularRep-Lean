import ModularRep.PaperProofs.TypeBRankThreePrincipalBSOnePairApplication
import ModularRep.PaperProofs.TypeBEmbeddedPairClassWitness
import ModularRep.PaperProofs.TypeBRankThreePrincipalConjugateCarrierBinding
import ModularRep.PaperProofs.TypeBPrincipalOrbitOrientation

/-!
# Orienting the actual principal correspondence

The lower correspondence is the existing count-derived seed, precomposed
with its orbitwise character switch. The switch tests the literal embedded
pair relation for one fixed specified catalogue family. The initial BS pair
and simultaneous transport prove the relation, including every original
raw representative. The computed upper SO correspondence is preserved.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitChoice

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open ModularRep.CharacterWeight
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldMatchingSplitting
open TypeBRankThreePrincipalFieldNaturality TypeBCliffordOrthogonalAmbientQuotient
open TypeBGreenPrincipalConstituentSource TypeBLocalReductionInstantiation
open TypeBFixedRootDefinitionFamily TypeBModularLinearCharacterLift
open TypeBLocalPhysicalBlockBinding TypeBCriterionHypotheses
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelTripleCarriers TypeBRankThreePrincipalMatchedInertia
open TypeBRankThreePrincipalAmbientFieldMatching
open TypeBCentralKernelInertia TypeBOrthogonalOmegaCarriers
open TypeBRankThreePrincipalBrauerOrbitBinding
open EvenFieldFLZ318FixedTheoremGate

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

local instance omegaOrdinaryRoots (F K : Type) [Field F] [Finite F] [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (H F))] :
    HasEnoughRootsOfUnity K (Nat.card (G F)) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))

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
  {parameters : OddFieldParameters F r f} {N : NormSource 3 F}
  {fieldSource : FieldActionSource 3 F r f parameters N}
  {C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N}
  {Msys : ModularSystem 2 K O k} [NeZero f]
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C
local notation "Ghat" => embeddedG (G F) matrixField
local notation "rootHat" => TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) matrixField root
local notation "calibrationHat" =>
  TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue
    (G F) matrixField Msys root rootCalibration
local notation "indexTwo" => TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C

variable
  (catalogues : TypeBEmbeddedPairClassWitness.CatalogueFamily
    (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C) root)
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The relation is the existing specified class witness on the exact embedded pair. -/
def pairRelation (theta : OmegaBrauer F root b) (w : OmegaWeight F S b) : Prop :=
  TypeBEmbeddedPairClassWitness.Relation Msys (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C) root
    rootCalibration catalogues navarro theta.val w.val

local notation "pairR" => pairRelation
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
  (rootCalibration := rootCalibration) catalogues navarro

variable (butterfly : TypeBCentralKernelButterflyCertificate.ButterflyCertificate 2 k K)
  {delta : H F} {outside : delta ∉ G F}

local notation "sigma" => brauerPermutation F S literal root b hb delta indexTwo
local notation "tau" => weightPermutation F S literal b hb delta indexTwo

include butterfly in
/-- The same inverse diagonal actor transports the two entries simultaneously. -/
theorem pairRelation_delta_iff (theta : OmegaBrauer F root b) (w : OmegaWeight F S b) :
    pairRelation
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro
      (brauerPermutation F S literal root b hb delta
        (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C) theta)
      (weightPermutation F S literal b hb delta
        (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C) w) ↔
    pairRelation
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro theta w := by
  have actor : (matrixAction).hom
      ((SemidirectProduct.inl (φ := matrixField) delta)⁻¹) =
      MulAut.conjNormal (H := G F) delta⁻¹ := by
    calc
      (matrixAction).hom ((SemidirectProduct.inl (φ := matrixField) delta)⁻¹) =
          (matrixAction).hom (SemidirectProduct.inl (φ := matrixField) delta⁻¹) :=
        congrArg (matrixAction).hom
          (map_inv (SemidirectProduct.inl (φ := matrixField)) delta).symm
      _ = _ := TypeBIndexTwoAmbientCommutator.naturalAction_inl
        (G F) matrixField matrixAction delta⁻¹
  have simultaneous := TypeBEmbeddedPairClassWitness.simultaneous_iff
    Msys (G F) matrixField matrixAction root rootCalibration catalogues navarro
    butterfly theta.val w.val (SemidirectProduct.inl (φ := matrixField) delta)
  rw [actor] at simultaneous
  exact simultaneous

variable
  (roots : TypeBGreenPrincipalConstituentSource.RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F)
      (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C)))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F)
      (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C)))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  {notThree : Nat.card F ≠ 3}
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta
    (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C) outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)

local notation "seed" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "seedDelta" =>
  TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv_delta covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction
local notation "simultaneous" => pairRelation_delta_iff
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
  (literal := literal) (hb := hb) (delta := delta)
  (rootCalibration := rootCalibration) catalogues navarro butterfly

/-- One orbitwise character switch is applied to the accepted lower seed. -/
def orientedOmegaEquiv : OmegaBrauer F root b ≃ OmegaWeight F S b :=
  TypeBPrincipalOrbitOrientation.orientedEquiv
    (brauerPermutation F S literal root b hb delta
      (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C))
    (weightPermutation F S literal b hb delta
      (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C))
    (brauerStep_involutive F S literal root b hb delta
      (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C))
    (TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv covering counts roots fieldScope
      green principalLift clifford principalRestriction)
    (TypeBRankThreePrincipalCoverSplitting.principalOmegaEquiv_delta
      covering counts roots fieldScope green principalLift clifford principalRestriction)
    (pairRelation
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro)
    (pairRelation_delta_iff
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (literal := literal) (hb := hb) (delta := delta)
      (rootCalibration := rootCalibration) catalogues navarro butterfly)

local notation "chosenMap" => orientedOmegaEquiv
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
  (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
  green principalLift clifford principalRestriction covering counts

theorem orientedOmegaEquiv_delta (theta : OmegaBrauer F root b) :
    chosenMap (sigma theta) = tau (chosenMap theta) :=
  TypeBPrincipalOrbitOrientation.orientedEquiv_equivariant sigma tau
    (brauerStep_involutive F S literal root b hb delta indexTwo)
    seed seedDelta pairR simultaneous theta

/-- Every SO covering class remains the one assigned by the same computed seed. -/
theorem orientedOmegaEquiv_sameSOCover (theta : OmegaBrauer F root b) :
    covering.cover (chosenMap theta) = covering.cover (seed theta) :=
  TypeBPrincipalOrbitOrientation.orientedEquiv_orbitLabel sigma tau
    (brauerStep_involutive F S literal root b hb delta indexTwo)
    seed seedDelta pairR simultaneous covering.cover covering.cover_action theta

/-- The unchanged upper correspondence has precisely the same restriction relation. -/
theorem orientedOmegaEquiv_occurs_iff_coversClass
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b) :
    NavarroCoveringBrauerExtension.BrauerOccursInRestriction
      (G F) rootH root Phi.val theta.val ↔
    TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val (chosenMap theta).val := by
  rw [covering.covers_iff, orientedOmegaEquiv_sameSOCover
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts theta]
  exact (TypeBRankThreePrincipalSOMatchingSplitting.occurs_iff_principalSOEquiv_eq
    covering counts roots fieldScope green principalLift clifford principalRestriction
    Phi theta).trans eq_comm

/-- The chosen lower map respects every actual SO actor. -/
theorem orientedOmegaEquiv_SO (m : H F) (theta : OmegaBrauer F root b) :
    chosenMap (brauerStep F S literal root b hb m theta) =
      weightStep F S literal b hb m (chosenMap theta) :=
  TypeBRankThreePrincipalOrbitBinding.seed_H_equivariant
    F S literal root b hb delta indexTwo outside chosenMap
    (orientedOmegaEquiv_delta
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts) m theta

section Field

variable
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb
    (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C))
  {coefficient : SpathCoefficientField 2 k Msys.prime}
  (fyz : TypeBRankThreePrincipalWeightFieldSplitting.FYZCorollary363SplittingSource
    F r f parameters Msys coefficient root rootH
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys root rootCalibration)
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys rootH rootHCalibration)
    S SH literal literalH guard guardH b hb bH hbH)

include gggr fyz in
/-- Full ambient equivariance follows from SO equivariance and the checked field fixation. -/
theorem orientedOmegaEquiv_ambient (a : Ambient matrixField) (theta : OmegaBrauer F root b) :
    letI := omegaBrauerAmbientAction F S literal root b hb parameters N fieldSource C
    letI := omegaWeightAmbientAction F S literal b hb parameters N fieldSource C
    chosenMap (a • theta) = a • chosenMap theta := by
  letI := omegaBrauerAmbientAction F S literal root b hb parameters N fieldSource C
  letI := omegaWeightAmbientAction F S literal b hb parameters N fieldSource C
  apply TypeBSemidirectFixedFieldFactorization.equivariant_of_inl_of_inr_fixed
    matrixField chosenMap _ _ _ a theta
  · intro m x
    rw [omegaBrauerAmbientAction_inl F S literal root b hb parameters N fieldSource C,
      omegaWeightAmbientAction_inl F S literal b hb parameters N fieldSource C]
    exact orientedOmegaEquiv_SO
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts m x
  · intro e x
    exact omegaBrauerAmbientAction_inr_fixed gggr e x
  · intro e w
    exact omegaWeightAmbientAction_inr_fixed (rootCalibration := rootCalibration)
      (rootHCalibration := rootHCalibration) fyz e w

variable
  [ambientRoots : HasEnoughRootsOfUnity K
    (Nat.card (TypeBMatrixAmbientOrdinaryRoots.MatrixAmbient parameters N fieldSource C))]
  (certificate : TypeBBSOnePairSplittingSource.Theorem46SplittingCertificate)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (centreClifford : TypeBCliffordCentreSource.CentreSource 3 F parameters (by decide))
  (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism fieldSource).ker =
    TypeBAutomorphismSource.embeddedCenter fieldSource)
  (naturalSurjective : Function.Surjective
    (TypeBAutomorphismSource.ambientAutomorphism fieldSource))
  (simple : IsSimpleGroup (Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (Omega 3 F))
  (brauerSource : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
  (ordinarySource : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)],
      TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K X)
  (ordinary : ∀ Q : Subgroup (H F), NormalizerOrdinarySource Msys SH.operations Q)
  (membership : OrdinaryInflationMembership Msys SH.operations ordinary)
  (productFormula : BrauerLinearTensorProductFormula rootH)

include gggr fyz ambientRoots certificate centreSpin fullCover centreClifford
  naturalKernel naturalSurjective simple nonabelian brauerSource ordinarySource
  ordinary membership productFormula in
/-- The initial pair selects one of the two actual character orientations,
with the seed weight and the global specified catalogue family held fixed. -/
theorem seed_oneOrientation (theta : OmegaBrauer F root b) :
    pairR theta (seed theta) ∨ pairR (sigma theta) (seed theta) := by
  classical
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F) matrixField
  have represented : ∃ W : CharacterWeight 2 K (G F),
      TypeBWeightCoveringSource.rawClass W = (seed theta).val := by
    refine Quotient.inductionOn (seed theta).val ?_
    intro iso
    refine Quotient.inductionOn iso ?_
    intro W
    exact ⟨W, rfl⟩
  obtain ⟨W, representative⟩ := represented
  let Phi := principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift theta
  have occurs : NavarroCoveringBrauerExtension.BrauerOccursInRestriction
      (G F) rootH root Phi.val theta.val :=
    principalAbove_occurs F root b hb rootH bH hbH roots fieldScope indexTwo
      green principalLift theta
  have covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val (seed theta).val :=
    (TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv_occurs_iff_coversClass
      covering counts roots fieldScope green principalLift clifford principalRestriction
      Phi theta).mp occurs
  let weightHat := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) matrixField W
  let thetaM : H F → IBr rootHat := fun m =>
    IrreducibleBrauerCharacter.twist rootHat
      (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root theta.val)
      (MulAut.conjNormal (H := Ghat)
        ((SemidirectProduct.inl (φ := matrixField) m)⁻¹))
  obtain ⟨m, hUT, witness⟩ :=
    TypeBRankThreePrincipalBSOnePairApplication.principalSOEquiv_someConjugatePairWitness
      (literalH := literalH) (hbH := hbH)
      (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration)
      gggr roots fieldScope green principalLift clifford principalRestriction fyz covering counts
      certificate centreSpin fullCover centreClifford naturalKernel naturalSurjective
      simple nonabelian brauerSource ordinarySource ordinary membership productFormula navarro
      Phi theta (seed theta) occurs covered W representative
      (fun m hUT => catalogues (thetaM m) weightHat hUT)
  have atStep : TypeBCentralKernelPairRepresentativeSplitting.WitnessAt
      Msys Ghat rootHat calibrationHat catalogues navarro
      (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root
        (brauerStep F S literal root b hb m theta).val) weightHat := by
    have oldWitness : TypeBCentralKernelPairRepresentativeSplitting.WitnessAt
        Msys Ghat rootHat calibrationHat catalogues navarro (thetaM m) weightHat :=
      ⟨hUT, witness⟩
    exact (congrArg (fun chi : IBr rootHat =>
      TypeBCentralKernelPairRepresentativeSplitting.WitnessAt
        Msys Ghat rootHat calibrationHat catalogues navarro chi weightHat)
      (TypeBRankThreePrincipalConjugateCarrierBinding.embedded_brauerStep
        F S literal root b hb parameters N fieldSource C theta m)).mpr oldWitness
  obtain ⟨stepInclusion, stepWitness⟩ := atStep
  have related : pairR (brauerStep F S literal root b hb m theta) (seed theta) :=
    TypeBEmbeddedPairClassWitness.of_rawWitness
      Msys (G F) matrixField matrixAction root rootCalibration catalogues navarro
      (brauerStep F S literal root b hb m theta).val W (seed theta).val
      representative stepInclusion stepWitness
  rcases (TypeBRankThreePrincipalOrbitBinding.exists_brauerStep_iff
    F S literal root b hb delta indexTwo outside theta
      (brauerStep F S literal root b hb m theta)).mp ⟨m, rfl⟩ with equal | equal
  · exact Or.inl ((congrArg (fun chi : OmegaBrauer F root b =>
      pairR chi (seed theta)) equal).mp related)
  · exact Or.inr ((congrArg (fun chi : OmegaBrauer F root b =>
      pairR chi (seed theta)) equal).mp related)

include gggr fyz ambientRoots certificate centreSpin fullCover centreClifford
  naturalKernel naturalSurjective simple nonabelian brauerSource ordinarySource
  ordinary membership productFormula in
/-- The computed equivariant correspondence satisfies the actual pair relation. -/
theorem orientedOmegaEquiv_related (theta : OmegaBrauer F root b) :
    pairR theta (chosenMap theta) := by
  apply TypeBPrincipalOrbitOrientation.orientedEquiv_related sigma tau
    (brauerStep_involutive F S literal root b hb delta indexTwo)
    seed seedDelta pairR simultaneous
  exact seed_oneOrientation
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
    catalogues navarro roots fieldScope green principalLift
    clifford principalRestriction covering counts gggr fyz certificate centreSpin fullCover
    centreClifford naturalKernel naturalSurjective simple nonabelian brauerSource
    ordinarySource ordinary membership productFormula

include gggr fyz ambientRoots certificate centreSpin fullCover centreClifford
  naturalKernel naturalSurjective simple nonabelian brauerSource ordinarySource
  ordinary membership productFormula in
/-- Every original raw representative receives the embedded specified pair witness
at its character under the same single chosen correspondence. -/
theorem orientedOmegaEquiv_allRepresentatives (theta : OmegaBrauer F root b)
    (W : CharacterWeight 2 K (G F))
    (representative : TypeBWeightCoveringSource.rawClass W = (chosenMap theta).val) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F) matrixField
    TypeBCentralKernelPairRepresentativeSplitting.WitnessAt
      Msys Ghat rootHat calibrationHat catalogues navarro
      (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root theta.val)
      (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) matrixField W) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F) matrixField
  exact TypeBEmbeddedPairClassWitness.all_representatives
    Msys (G F) matrixField matrixAction root rootCalibration catalogues navarro butterfly
    theta.val (chosenMap theta).val
    (orientedOmegaEquiv_related
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      catalogues navarro butterfly roots fieldScope green principalLift
      clifford principalRestriction covering counts gggr fyz certificate centreSpin fullCover
      centreClifford naturalKernel naturalSurjective simple nonabelian brauerSource
      ordinarySource ordinary membership productFormula theta)
    W representative

end Field

end ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitChoice


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
