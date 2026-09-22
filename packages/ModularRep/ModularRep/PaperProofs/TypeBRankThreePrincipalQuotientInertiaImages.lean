import ModularRep.PaperProofs.TypeBRankThreePrincipalSelectedQuotient
import ModularRep.PaperProofs.TypeBQuotientInertiaConjugationImage
import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientComparison
import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientLocalPackets
import ModularRep.PaperProofs.TypeBCentrelessSelectedWeightBlockTransport

/-!
# Conjugation images of the actual principal quotient inertia

The full matrix action gives the surjectivity required by the quotient
inertia image theorems. The selected-pair application keeps its original
inertia inclusion and both complete witnesses.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientInertiaImages

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCriterionHypotheses
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open CyclicOuterLemma37LiteralLocalExtension
open TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalFieldMatchingSplitting TypeBCliffordOrthogonalAmbientQuotient
open TypeBGreenPrincipalConstituentSource TypeBLocalPhysicalBlockBinding
open TypeBRankThreePrincipalMatchedInertia TypeBRankThreePrincipalAmbientFieldMatching
open TypeBRankThreePrincipalBrauerOrbitBinding
open TypeBCentralKernelInertia TypeBOrthogonalOmegaCarriers
open EvenFieldFLZ318FixedTheoremGate
open TypeBCentralKernelTripleRootFamily TypeBCentralKernelTripleCertificate
open TypeBRankThreePrincipalFixedRootFamilyBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

local instance omegaOrdinaryRoots (F K : Type) [Field F] [Finite F] [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (H F))] :
    HasEnoughRootsOfUnity K (Nat.card (G F)) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))

open TypeBRankThreePrincipalSelectedQuotient
open TypeBQuotientInertiaConjugationImage

section Surjectivity

variable {M E : Type} [Group M] [Group E] [Finite M] [Finite E]
  (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
  (action : NaturalAction G field)

/-- The fixed base action square transports surjectivity. -/
theorem embeddedAction_surjective
    (full : Function.Surjective action.hom) :
    Function.Surjective
      (TypeBCriterionEmbeddedPairBinding.embeddedAction G field action) := by
  let e := TypeBCriterionEmbeddedPairBinding.baseEquiv G field
  intro alpha
  obtain ⟨a, ha⟩ := full ((MulAut.congr e).symm alpha)
  refine ⟨a, ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := e.surjective x
  have square := TypeBCriterionEmbeddedPairBinding.baseEquiv_action
    G field action a g
  have image : e (action.hom a g) = alpha (e g) := by
    rw [ha]
    change e (e.symm (alpha (e g))) = _
    exact e.apply_symm_apply _
  exact square.symm.trans image

end Surjectivity

/-- The literal matrix action gives all automorphisms of the embedded base. -/
theorem embedded_originalAction_surjective
    {F : Type} [Field F] [Finite F] {r f : ℕ} [CharP F r]
    (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
    (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
    (fullCover : IsUniversalCentralExtension
      (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
    (naturalSurjective : Function.Surjective
      (TypeBAutomorphismSource.ambientAutomorphism fieldSource)) :
    letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)
      (matrixNaturalAction F parameters N fieldSource C)
    Function.Surjective (TypeBCentralKernelCarriers.originalAction
      (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource))) := by
  letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)
  change Function.Surjective (TypeBCriterionEmbeddedPairBinding.embeddedAction
    (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
      (matrixNaturalAction F parameters N fieldSource C))
  exact embeddedAction_surjective (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)
    (TypeBMatrixOmegaFullAutomorphismBinding.omegaAmbientAction_surjective
      fieldSource le_rfl C centreSpin fullCover naturalSurjective)

section Selected

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
  (catalogues : TypeBEmbeddedPairClassWitness.CatalogueFamily
    (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C) root)
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (butterfly : TypeBCentralKernelButterflyCertificate.ButterflyCertificate 2 k K)
  {delta : H F} {outside : delta ∉ G F}
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

variable
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb
    (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C))
  {coefficient : SpathCoefficientField 2 k Msys.prime}
  (fyz : TypeBRankThreePrincipalWeightFieldSplitting.FYZCorollary363SplittingSource
    F r f parameters Msys coefficient root rootH
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys root rootCalibration)
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys rootH rootHCalibration)
    S SH literal literalH guard guardH b hb bH hbH)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (naturalSurjective : Function.Surjective
    (TypeBAutomorphismSource.ambientAutomorphism fieldSource))

variable
  [ambientRoots : HasEnoughRootsOfUnity K
    (Nat.card (TypeBMatrixAmbientOrdinaryRoots.MatrixAmbient parameters N fieldSource C))]
  (certificate : TypeBBSOnePairSplittingSource.Theorem46SplittingCertificate)
  (centreClifford : TypeBCliffordCentreSource.CentreSource 3 F parameters (by decide))
  (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism fieldSource).ker =
    TypeBAutomorphismSource.embeddedCenter fieldSource)
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
/-- The same selected inclusion and pair supply both complete action images. -/
theorem selectedQuotient_images
    (psi : Definition35Brauer
      ((family S SH literal literalH Msys root rootCalibration navarro guard).problem b))
    (quotientBlocks :
      letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
        (soFieldAction 3 F parameters le_rfl N C fieldSource)
        (matrixNaturalAction F parameters N fieldSource C)
      let Ghat := embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
      let rootHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F)
        (soFieldAction 3 F parameters le_rfl N C fieldSource) root
      let thetaHat := TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F)
        (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val
      let WHat := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F)
        (soFieldAction 3 F parameters le_rfl N C fieldSource)
        (selectedCharacterWeight S b
          (principalEquiv (S := S) (SH := SH)
            (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
            (C := C) (rootCalibration := rootCalibration)
            catalogues navarro butterfly roots fieldScope green principalLift clifford
            principalRestriction covering counts psi))
      let centreless := embedded_center_eq_bot parameters N fieldSource C
        centreSpin fullCover centreClifford naturalKernel
      PhysicalBlockFamily (k := k)
        (TypeBBSCentralQuotientPairTransport.quotientBase Ghat rootHat thetaHat centreless)
        (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient
          Ghat rootHat thetaHat centreless WHat)) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)
      (matrixNaturalAction F parameters N fieldSource C)
    letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)
    let Ghat := embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    let rootHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource) root
    let calibrationHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration
    let thetaHat := TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val
    let WHat := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)
      (selectedCharacterWeight S b
        (principalEquiv (S := S) (SH := SH)
          (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
          (C := C) (rootCalibration := rootCalibration)
          catalogues navarro butterfly roots fieldScope green principalLift clifford
          principalRestriction covering counts psi))
    let centreless := embedded_center_eq_bot parameters N fieldSource C
      centreSpin fullCover centreClifford naturalKernel
    ∃ hUT : U Ghat WHat ≤ T Ghat rootHat thetaHat,
      (sourceAction Ghat rootHat thetaHat centreless).range =
        brauerStabilizer (MonoidHom.id (MulAut Ghat)) rootHat thetaHat ∧
      (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient
        Ghat rootHat thetaHat centreless WHat).map
          (sourceAction Ghat rootHat thetaHat centreless) =
        rawStabilizer (MonoidHom.id (MulAut Ghat)) WHat ∧
      Nonempty (TypeBCentralKernelPairSplittingBinding.PairWitness
        Msys Ghat rootHat calibrationHat thetaHat WHat hUT navarro
        (catalogues thetaHat WHat hUT)) ∧
      Nonempty (BlockTripleWitness
        (TypeBBSCentralQuotientPairTransport.quotientData
          Ghat rootHat thetaHat centreless WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks)
        (TypeBBSCentralQuotientPairTransport.quotientTheta
          Ghat rootHat thetaHat centreless WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks)
        (TypeBBSCentralQuotientPairTransport.quotientPhi
          Ghat rootHat thetaHat centreless WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks navarro)) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
  obtain ⟨hUT, pair, triple⟩ :=
    TypeBRankThreePrincipalSelectedQuotient.selectedQuotient
      (S := S) (SH := SH) (root := root) (rootH := rootH)
      (b := b) (hb := hb) (bH := bH) (hbH := hbH)
      (literal := literal) (literalH := literalH)
      (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (Msys := Msys)
      (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration)
      (guard := guard) (guardH := guardH) (notThree := notThree) (dgn := dgn)
      (delta := delta) (outside := outside)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      certificate centreClifford naturalKernel simple nonabelian brauerSource
      ordinarySource ordinary membership productFormula psi quotientBlocks
  have full := embedded_originalAction_surjective parameters N fieldSource C
    centreSpin fullCover naturalSurjective
  exact ⟨hUT, sourceAction_range _ _ _ _ full,
    sourceLocalAction_image _ _ _ _ full _ hUT, pair, triple⟩


end Selected

section Reference

open TypeBRankThreePrincipalReferenceBinding
open TypeBCentralKernelButterflyCertificate

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  [HasEnoughRootsOfUnity K (Nat.card (H F))]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (rootCalibration : RootResidueCompatible Msys root)
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (guard : GuardedBlockCompatibility root S.operations)
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)

variable {r f : ℕ} [CharP F r] [NeZero f]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (fieldSource : FieldActionSource 3 F r f parameters N)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (centreClifford : TypeBCliffordCentreSource.CentreSource 3 F parameters (by decide))
  (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism fieldSource).ker =
    TypeBAutomorphismSource.embeddedCenter fieldSource)
  (simple : IsSimpleGroup (Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (Omega 3 F))
  (psi : Definition35Brauer (problem S SH literal literalH Msys root rootCalibration navarro guard b))


local instance embeddedNormal :
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)).Normal :=
  TypeBLocalOrdinaryGeometry.embeddedG_normal (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)

local notation "Ghat" => embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
local notation "rootHat" => TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root
local notation "thetaHat" => TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val
local notation "centreHat" => embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel
local notation "jBase" => TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
local notation "dRef" => TypeBRankThreePrincipalQuotientBrauerFibre.quotientEquiv S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb
local notation "cRef" => TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi
local notation "qpsi" => TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi
local notation "Hbar" => TypeBRankThreePrincipalQuotientComparison.commonQuotient
  S SH literal literalH Msys root rootCalibration navarro guard b hb
local notation "cBase" => sourceBaseEquiv Ghat rootHat thetaHat centreHat

/-- The embedded base reaches the common reference through the fixed pair base. -/
def referenceBaseEquiv : Ghat ≃* Hbar :=
  (cBase).trans (cRef).symm

local notation "eRef" => referenceBaseEquiv S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi

/-- This comparison is forced by the two existing literal projections. -/
theorem referenceBaseEquiv_original :
    (jBase).trans eRef = dRef := by
  apply MulEquiv.ext
  intro g
  have projected : cRef (dRef g) = cBase (jBase g) := by
    apply Subtype.ext
    exact (congrArg (fun z : Hbar => (cRef z).val)
      (TypeBRankThreePrincipalQuotientBrauerFibre.quotientEquiv_projection
        S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb g)).trans
          (TypeBRankThreePrincipalQuotientComparison.referenceToPairBase_projection
            S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi g)
  change (cRef).symm (cBase (jBase g)) = dRef g
  exact (congrArg (cRef).symm projected).symm.trans
    ((cRef).symm_apply_apply (dRef g))

/-- Both root lifts are the same original field-level lift. -/
theorem referenceBaseEquiv_lift :
    (qpsi).iota.lift = (rootHat).lift :=
  (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_root_lift
    S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).trans
      (TypeBCriterionEmbeddedPairBinding.embeddedRoot_lift (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root).symm

/-- The fixed reference map transports the actual embedded selected character. -/
theorem referenceBaseEquiv_brauer :
    TypeBCentralKernelSpinFibreIdentification.brauerEquiv eRef rootHat (qpsi).iota
      (referenceBaseEquiv_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover simple nonabelian psi) thetaHat = (qpsi).brauer := by
  apply Subtype.ext
  refine (TypeBCentralKernelSpinFibreIdentification.brauerEquiv_val
    eRef rootHat (qpsi).iota (referenceBaseEquiv_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover simple nonabelian psi)
      thetaHat).trans ?_
  refine (congrArg
    (fun phi : PrimeRegularClassFunction K Ghat 2 =>
      PrimeRegularClassFunction.pullback (eRef).symm.toMonoidHom phi)
    (TypeBCriterionEmbeddedPairBinding.brauerEquiv_val (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)).trans ?_
  have quotientValues : (qpsi).brauer.val =
      PrimeRegularClassFunction.pullback (dRef).symm.toMonoidHom psi.val.val := rfl
  refine Eq.trans ?_ quotientValues.symm
  apply PrimeRegularClassFunction.ext
  intro x
  change psi.val.val (PrimeRegularElement.map (jBase).symm.toMonoidHom
    (PrimeRegularElement.map (eRef).symm.toMonoidHom x)) =
      psi.val.val (PrimeRegularElement.map (dRef).symm.toMonoidHom x)
  congr 1
  apply Subtype.ext
  exact congrArg (fun e : (G F) ≃* Hbar => e.symm x.val)
    (referenceBaseEquiv_original S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi)

/-- Conjugation on the pair base is expressed in the same reference coordinates. -/
def referenceAction :
    (T Ghat rootHat thetaHat ⧸
      TypeBBSCentralQuotientPairTransport.ambientKernel
        Ghat rootHat thetaHat centreHat) →* MulAut Hbar :=
  (MulAut.congr cRef).symm.toMonoidHom.comp
    (firstAction (TypeBBSCentralQuotientPairTransport.quotientBase
      Ghat rootHat thetaHat centreHat))

/-- The reference action is the actual source action through the forced base map. -/
theorem referenceAction_source :
    referenceAction S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi =
      (MulAut.congr eRef).toMonoidHom.comp
        (sourceAction Ghat rootHat thetaHat centreHat) := by
  apply MonoidHom.ext
  intro t
  apply MulEquiv.ext
  intro x
  change (cRef).symm (firstAction _ t (cRef x)) =
    (cRef).symm (cBase ((cBase).symm
      (firstAction _ t (cBase ((cBase).symm (cRef x))))))
  simp only [MulEquiv.apply_symm_apply]

/-- Character fixation uses the same inverse automorphism on both sides. -/
theorem referenceBrauer_fixed_iff (alpha : MulAut Ghat) :
    alpha ∈ brauerStabilizer (MonoidHom.id (MulAut Ghat)) rootHat thetaHat ↔
      MulAut.congr eRef alpha ∈
        brauerStabilizer (MonoidHom.id (MulAut Hbar)) (qpsi).iota (qpsi).brauer := by
  rw [mem_brauerStabilizer, mem_brauerStabilizer]
  change IrreducibleBrauerCharacter.twist rootHat thetaHat alpha⁻¹ = thetaHat ↔
    IrreducibleBrauerCharacter.twist (qpsi).iota (qpsi).brauer
      (MulAut.congr eRef alpha)⁻¹ = (qpsi).brauer
  let eBrauer := TypeBCentralKernelSpinFibreIdentification.brauerEquiv
    eRef rootHat (qpsi).iota (referenceBaseEquiv_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover simple nonabelian psi)
  have square := TypeBCentralKernelSpinFibreIdentification.brauerEquiv_twist
    eRef rootHat (qpsi).iota (referenceBaseEquiv_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover simple nonabelian psi)
    alpha⁻¹ (MulAut.congr eRef alpha)⁻¹ (fun x => by
      rw [← map_inv]
      change eRef (alpha⁻¹ x) = eRef (alpha⁻¹ ((eRef).symm (eRef x)))
      rw [MulEquiv.symm_apply_apply]) thetaHat
  rw [referenceBaseEquiv_brauer S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi] at square
  constructor
  · intro h
    exact square.symm.trans
      ((congrArg eBrauer h).trans (referenceBaseEquiv_brauer S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi))
  · intro h
    apply eBrauer.injective
    exact square.trans (h.trans (referenceBaseEquiv_brauer S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).symm)

variable (naturalSurjective : Function.Surjective
  (TypeBAutomorphismSource.ambientAutomorphism fieldSource))

include naturalSurjective in
/-- The full first conjugation image is the positive reference Brauer stabilizer. -/
theorem referenceAction_range :
    (referenceAction S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).range =
      brauerStabilizer (MonoidHom.id (MulAut Hbar)) (qpsi).iota (qpsi).brauer := by
  rw [referenceAction_source, MonoidHom.range_comp,
    sourceAction_range Ghat rootHat thetaHat centreHat
      (embedded_originalAction_surjective parameters N fieldSource C
        centreSpin fullCover naturalSurjective)]
  ext alpha
  rw [Subgroup.mem_map_equiv]
  simpa only [MulEquiv.apply_symm_apply] using
    referenceBrauer_fixed_iff S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi ((MulAut.congr eRef).symm alpha)

variable (w : Definition35Weight
  (TypeBRankThreePrincipalReferenceBinding.problem
    S SH literal literalH Msys root rootCalibration navarro guard b))

local notation "WHat" => TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b w)
local notation "Wbar" => TypeBRankThreePrincipalQuotientLocalPackets.quotientRawWeight
  S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w

/-- The whole raw packet follows the same fixed reference base comparison. -/
theorem referenceBaseEquiv_raw :
    (WHat).mapGroupEquiv eRef = Wbar := by
  rw [TypeBRankThreePrincipalQuotientLocalPackets.quotientRawWeight_eq_referenceMap]
  change (TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv jBase
    (selectedCharacterWeight S b w)).mapGroupEquiv eRef = _
  rw [← TypeBCentrelessSelectedWeightBlockTransport.mapGroupEquiv_eq_rawWeightEquiv,
    CharacterWeight.mapGroupEquiv_trans, referenceBaseEquiv_original S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi]

/-- The raw weight and its own local character have the transported stabilizer. -/
theorem referenceRaw_fixed_iff (alpha : MulAut Ghat) :
    alpha ∈ rawStabilizer (MonoidHom.id (MulAut Ghat)) WHat ↔
      MulAut.congr eRef alpha ∈ rawStabilizer (MonoidHom.id (MulAut Hbar)) Wbar := by
  rw [mem_rawStabilizer, mem_rawStabilizer]
  change (WHat).rightTwist alpha⁻¹ = WHat ↔
    (Wbar).rightTwist (MulAut.congr eRef alpha)⁻¹ = Wbar
  have square := CharacterWeight.mapGroupEquiv_rightTwist WHat eRef alpha⁻¹
  rw [map_inv, referenceBaseEquiv_raw S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w] at square
  constructor
  · intro h
    exact square.symm.trans
      ((congrArg (fun W : CharacterWeight 2 K Ghat => W.mapGroupEquiv eRef) h).trans
        (referenceBaseEquiv_raw S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w))
  · intro h
    apply (CharacterWeight.rawGroupEquiv eRef).injective
    change ((WHat).rightTwist alpha⁻¹).mapGroupEquiv eRef = (WHat).mapGroupEquiv eRef
    exact square.trans (h.trans (referenceBaseEquiv_raw S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w).symm)

include naturalSurjective in
/-- The exact selected inclusion gives the full local image on the reference quotient. -/
theorem referenceLocalAction_image
    (hUT : U Ghat WHat ≤ T Ghat rootHat thetaHat) :
    (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient
      Ghat rootHat thetaHat centreHat WHat).map (referenceAction S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi) =
        rawStabilizer (MonoidHom.id (MulAut Hbar)) Wbar := by
  rw [referenceAction_source, ← Subgroup.map_map,
    sourceLocalAction_image Ghat rootHat thetaHat centreHat
      (embedded_originalAction_surjective parameters N fieldSource C
        centreSpin fullCover naturalSurjective) WHat hUT]
  ext alpha
  rw [Subgroup.mem_map_equiv]
  simpa only [MulEquiv.apply_symm_apply] using
    referenceRaw_fixed_iff S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w ((MulAut.congr eRef).symm alpha)

end Reference

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientInertiaImages


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
