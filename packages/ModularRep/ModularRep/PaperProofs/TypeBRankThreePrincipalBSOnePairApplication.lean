import ModularRep.PaperProofs.TypeBRankThreePrincipalBSUpperAntecedents
import ModularRep.PaperProofs.TypeBRankThreePrincipalRawInertiaBinding
import ModularRep.PaperProofs.TypeBMatrixOmegaBSStructure
import ModularRep.PaperProofs.TypeBMatrixOmegaEvenOrder
import ModularRep.PaperProofs.TypeBMatrixOmegaPrimeToTwoCover
import ModularRep.PaperProofs.TypeBBSOnePairSplittingSource

/-!
# The actual rank-three principal one-pair application

The same SO correspondence, upper character and original lower raw weight
supply the separate antecedents of the generic BS implication. The specified
catalogues keep their central characters. The index, even order, structural
matrix action, factorization, extensions and common quotient twist are
computed before the implication is applied.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalBSOnePairApplication

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
open EvenFieldFLZ318FixedTheoremGate

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section Catalogues

variable {k K X : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group X] [Finite X]
  (source : LocalBlockInductionSource
    (p := 2) (k := k) (K := K) (G := X) (Block := LiteralPrimitiveBlock k X))
  (literal : ∀ b, source.operations.ambientBlockData.blockIdempotent b = b.val)

/-- Repacking keeps every actual ambient block central character unchanged. -/
def ambientPhysicalBlocks : PhysicalBlocks k X := by
  letI := source.operations.ambientBlockData.fintypeBlock
  refine {
    blockFintype := source.operations.ambientBlockData.fintypeBlock
    decomposition := physicalDecomposition source literal
    catalogue := {
      centralCharacter := source.operations.ambientBlockData.catalogue.centralCharacter
      delta_own := ?_
      delta_other := ?_
      exhaustive := source.operations.ambientBlockData.catalogue.exhaustive } }
  · intro B
    have value : (physicalDecomposition source literal).blockIdempotentInCenter B =
        source.operations.ambientBlockData.blocks.blockIdempotentInCenter B :=
      Subtype.ext (literal B).symm
    rw [value]
    exact source.operations.ambientBlockData.catalogue.delta_own B
  · intro B C hne
    have value : (physicalDecomposition source literal).blockIdempotentInCenter C =
        source.operations.ambientBlockData.blocks.blockIdempotentInCenter C :=
      Subtype.ext (literal C).symm
    rw [value]
    exact source.operations.ambientBlockData.catalogue.delta_other B C hne

theorem ambientPhysicalBlocks_centralCharacter (b : LiteralPrimitiveBlock k X) :
    letI := source.operations.ambientBlockData.fintypeBlock
    (ambientPhysicalBlocks source literal).catalogue.centralCharacter b =
      source.operations.ambientBlockData.catalogue.centralCharacter b := rfl

/-- The normalizer blocks already have the required primitive-idempotent allocation. -/
def normalizerPhysicalBlocks (Q : Subgroup X) :
    PhysicalBlocks k (Subgroup.normalizer (Q : Set X)) where
  blockFintype := (source.operations.inflatedNormalizerBlockData Q).fintypeBlock
  decomposition := (source.operations.inflatedNormalizerBlockData Q).blocks
  catalogue := (source.operations.inflatedNormalizerBlockData Q).catalogue

theorem normalizerPhysicalBlocks_centralCharacter
    (Q : Subgroup X) (b : InflatedNormalizerBlock (k := k) Q) :
    letI := (source.operations.inflatedNormalizerBlockData Q).fintypeBlock
    (normalizerPhysicalBlocks source Q).catalogue.centralCharacter b =
      (source.operations.inflatedNormalizerBlockData Q).catalogue.centralCharacter b := rfl

/-- The induction relation has the same subgroup and the same two central characters. -/
theorem blockInducesTo_repacked
    (Q : Subgroup X) (b : InflatedNormalizerBlock (k := k) Q)
    (B : LiteralPrimitiveBlock k X) :
    letI := source.operations.ambientBlockData.fintypeBlock
    letI := (source.operations.inflatedNormalizerBlockData Q).fintypeBlock
    BlockInducesTo (Subgroup.normalizer (Q : Set X))
      (source.operations.inflatedNormalizerBlockData Q).catalogue
      source.operations.ambientBlockData.catalogue b B ↔
    BlockInducesTo (Subgroup.normalizer (Q : Set X))
      (normalizerPhysicalBlocks source Q).catalogue
      (ambientPhysicalBlocks source literal).catalogue b B := Iff.rfl

end Catalogues
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
  {Msys : ModularSystem 2 K O k}
  [NeZero f]
  [ambientRoots : HasEnoughRootsOfUnity K
    (Nat.card (TypeBMatrixAmbientOrdinaryRoots.MatrixAmbient parameters N fieldSource C))]
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C))
  (roots : TypeBGreenPrincipalConstituentSource.RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C)))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C)))
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
    F S SH root rootH b hb bH hbH literal literalH delta (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C) outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction

local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C
local notation "Ghat" => embeddedG (G F) matrixField
local notation "rootHat" => TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) matrixField root
local notation "calibrationHat" =>
  TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue
    (G F) matrixField Msys root rootCalibration

include gggr fyz ambientRoots in
/-- The generic BS implication produces a triple at some actual SO conjugate,
while the upper pair and the original raw lower weight are fixed beforehand. -/
theorem principalSOEquiv_someConjugatePairWitness
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
    (navarro : ∀ (X : Type) [Group X] [Finite X]
      [HasEnoughRootsOfUnity K (Nat.card X)]
      (iota : PrimeRegularRootEmbedding 2 k K X)
      (compatible : RootResidueCompatible Msys iota),
        ScopedDefectZeroReductionSource Msys iota compatible)
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b)
    (w : OmegaWeight F S b)
    (occurs : NavarroCoveringBrauerExtension.BrauerOccursInRestriction
      (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val w.val)
    (W : CharacterWeight 2 K (G F))
    (representative : TypeBWeightCoveringSource.rawClass W = w.val) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
    letI := TypeBBSOnePairSplittingSource.embeddedOrdinaryRoots (K := K) matrixField (G F)
    let thetaHat := TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) matrixField root theta.val
    let weightHat := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) matrixField W
    let thetaM : H F → IBr rootHat := fun m =>
      IrreducibleBrauerCharacter.twist rootHat thetaHat
        (MulAut.conjNormal (H := Ghat) ((SemidirectProduct.inl m : Ambient matrixField)⁻¹))
    ∀ (catalogues : ∀ (m : H F)
      (hUT : U Ghat weightHat ≤ T Ghat rootHat (thetaM m)),
      PhysicalBlockFamily (k := k)
        (inside Ghat (T Ghat rootHat (thetaM m)))
        (inside (U Ghat weightHat) (T Ghat rootHat (thetaM m)))),
      ∃ (m : H F) (hUT : U Ghat weightHat ≤ T Ghat rootHat (thetaM m)),
        Nonempty (TypeBCentralKernelPairSplittingBinding.PairWitness
          Msys Ghat rootHat calibrationHat (thetaM m) weightHat hUT navarro
          (catalogues m hUT)) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) matrixField matrixAction
  letI := TypeBBSOnePairSplittingSource.embeddedOrdinaryRoots (K := K) matrixField (G F)
  dsimp only
  intro catalogues
  obtain ⟨V, mu, lambda, representsV, occursOriginal, coverOriginal,
      extensionM, extensionGE, upperBlock, canonicalMu, selectedLift,
      equalOne, regularValues, twists⟩ :=
    TypeBRankThreePrincipalBSUpperAntecedents.principalSOEquiv_localUpperAntecedents
      (literalH := literalH) (hbH := hbH)
      (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration)
      gggr roots fieldScope green principalLift clifford principalRestriction fyz covering counts
      ordinarySource ordinary membership productFormula Phi theta w occurs covered W representative
  have brauerFactor : BrauerFactorization (G F) matrixField matrixAction root theta.val :=
    omegaBrauerInertia_factorization gggr theta
  have commutatorBound :
      ⁅brauerInertia (G F) matrixField matrixAction root theta.val, embeddedM matrixField⁆ ≤
        brauerInertia (G F) matrixField matrixAction root theta.val ⊓ embeddedM matrixField :=
    TypeBRankThreePrincipalRawInertiaBinding.omegaBrauerInertia_commutator_le
      (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (indexTwo := TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C) theta
  have extensionsM :=
    TypeBRankThreePrincipalRawInertiaBinding.omegaBrauer_all_SO_conjugates_extend_originalM
      (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (indexTwo := TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C)
      brauerSource theta
  have extensionsGE :=
    TypeBRankThreePrincipalRawInertiaBinding.omegaBrauer_all_SO_conjugates_extend_originalField
      (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (indexTwo := TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C)
      brauerSource theta
  have weightFactor : WeightClassFactorization (G F) matrixField matrixAction W := by
    unfold WeightClassFactorization
    change (weightClassInertia (G F) matrixField matrixAction
        (TypeBWeightCoveringSource.rawClass W) : Set (Ambient matrixField)) =
      (factorInertia matrixField (weightClassInertia (G F) matrixField matrixAction
        (TypeBWeightCoveringSource.rawClass W)) (embeddedM matrixField) : Set (Ambient matrixField)) *
      (factorInertia matrixField (weightClassInertia (G F) matrixField matrixAction
        (TypeBWeightCoveringSource.rawClass W)) (embeddedE matrixField) : Set (Ambient matrixField))
    rw [representative]
    exact
      (omegaWeightClassInertia_factorization
        (N := N) (fieldSource := fieldSource) (C := C)
        (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration) fyz w)
  have sameInertia : brauerInertia (G F) matrixField matrixAction root theta.val =
      weightClassInertia (G F) matrixField matrixAction (TypeBWeightCoveringSource.rawClass W) := by
    exact (principalSOEquiv_matched_ambient_inertia_eq
      gggr roots fieldScope green principalLift clifford principalRestriction fyz covering counts
      Phi theta w occurs covered).trans
        (congrArg (weightClassInertia (G F) matrixField matrixAction) representative.symm)
  have positiveTwists : ∀ e : FieldGroup f,
      ∃ (mu : IBr (TypeBModularGroupRootBinding.groupRoot Msys ((H F) ⧸ (G F))))
        (nu : (H F) ⧸ (G F) →* kˣ)
        (lambda : TypeCWeightTensorFieldAction.RadicalTensorCharacter
          (p := 2) (K := K) (G := H F)),
        mu.val = (TypeBModularGroupRootBinding.groupRoot Msys ((H F) ⧸ (G F))).liftedLinearCharacter nu ∧
        lambda.val = quotientLift rootH (G F)
          ((LinearCharactersTrivialOn.quotientMulEquiv (k := k) (G F)).symm nu) ∧
        (IrreducibleBrauerCharacter.twist rootH Phi.val (matrixField e)).val =
          PrimeRegularClassFunction.pointwiseMul
            (PrimeRegularClassFunction.pullback (QuotientGroup.mk' (G F)) mu.val) Phi.val.val ∧
        TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
            lambda (TypeBWeightCoveringSource.rawClass V) =
          CharacterWeight.rightTwistConjugacyClass (matrixField e)
            (TypeBWeightCoveringSource.rawClass V) := by
    intro e
    refine ⟨mu, TypeBPrincipalQuotientBrauerTwistBinding.quotientLinearCharacter (k := k) (G F),
      lambda, ?_, selectedLift, ?_, ?_⟩
    · exact (congrArg (fun chi : IBr (TypeBPrincipalQuotientBrauerTwistBinding.quotientRoot (G F) Msys) => chi.val) canonicalMu).trans
        (TypeBPrincipalQuotientBrauerTwistBinding.quotientBrauer_linearCharacter (G F) Msys)
    · simpa only [inv_inv] using (twists e⁻¹).1
    · simpa only [inv_inv] using (twists e⁻¹).2
  let cover := TypeBMatrixOmegaPrimeToTwoCover.identityEllPrimeCover
    3 F parameters le_rfl N C centreSpin fullCover simple nonabelian
  have primeDivides : 2 ∣ Nat.card cover.S :=
    TypeBMatrixOmegaEvenOrder.two_dvd_card 3 F N parameters le_rfl C
  have centreless : Subgroup.center (G F) = ⊥ :=
    TypeBMatrixOmegaBSStructure.omega_center_eq_bot N parameters fieldSource le_rfl C
      centreSpin fullCover centreClifford naturalKernel
  have centralizer : Subgroup.centralizer (Ghat : Set (Ambient matrixField)) =
      embeddedCenter matrixField :=
    TypeBMatrixOmegaFullAutomorphismBinding.centralizer_eq_embeddedSOCenter
      fieldSource le_rfl C centreSpin fullCover centreClifford naturalKernel
  have naturalKernelMatrix : (matrixAction).hom.ker = embeddedCenter matrixField :=
    (TypeBMatrixOmegaFullAutomorphismBinding.omegaAmbientAction_ker_eq_bot
      fieldSource le_rfl C centreSpin fullCover centreClifford naturalKernel).trans
      (TypeBMatrixOmegaFullAutomorphismBinding.embeddedSOCenter_eq_bot
        fieldSource le_rfl C centreSpin fullCover centreClifford naturalKernel).symm
  have naturalSurjectiveMatrix : Function.Surjective (matrixAction).hom :=
    TypeBMatrixOmegaFullAutomorphismBinding.omegaAmbientAction_surjective
      fieldSource le_rfl C centreSpin fullCover naturalSurjective
  exact certificate.someConjugate (G F) matrixField matrixAction Msys coefficient
    cover primeDivides centreless (TypeBMatrixOmegaBSStructure.omega_derived 3 F)
    inferInstance centralizer naturalKernelMatrix naturalSurjectiveMatrix
    root rootH rootCalibration rootHCalibration dgn navarro theta.val W
    brauerFactor commutatorBound extensionsM extensionsGE weightFactor extensionM extensionGE
    sameInertia Phi.val V occursOriginal coverOriginal positiveTwists
    (ambientPhysicalBlocks SH literalH) (normalizerPhysicalBlocks SH V.subgroup)
    (ordinary V.subgroup) upperBlock catalogues

end ModularRep.PaperProofs.TypeBRankThreePrincipalBSOnePairApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
