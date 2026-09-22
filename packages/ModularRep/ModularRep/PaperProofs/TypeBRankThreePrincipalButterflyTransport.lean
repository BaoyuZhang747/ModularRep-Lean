import ModularRep.PaperProofs.TypeBButterflyTransportCore
import ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyAmbientImages
import ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyLocalCharacter
import ModularRep.PaperProofs.TypeBButterflyHonestTargetRoots

/-!
# The selected block triple on the actual honest normalizer

The Butterfly application uses the existing selected triple, the same
reference character, and the prescribed target characters. Equality of the
local subgroup is transported before applying the exact source theorem.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyTransport

open ModularRep
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelButterflyCertificate




open scoped MonoidAlgebra Pointwise
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


open EvenFieldFLZBAWGoodFamily

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

local instance selectedEmbeddedNormal :
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)).Normal :=
  TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)

local instance problemAlgebra : Algebra O
    (TypeBRankThreePrincipalReferenceBinding.problem
      (F := F) (K := K) (O := O) (k := k)
      S SH literal literalH Msys root rootCalibration navarro guard b).K :=
  (inferInstance : Algebra O K)

variable (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b))

variable
  (quotientBlocks : PhysicalBlockFamily (k := k) (TypeBBSCentralQuotientPairTransport.quotientBase
  (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient
  (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)))))
  (ambient : SpathAmbientGroup (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi))
  (targetBlocks : PhysicalBlockFamily (k := k) ambient.base
    (AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ambient))

include S SH root rootH b hb bH hbH literal literalH parameters N fieldSource C
  Msys rootCalibration rootHCalibration guard guardH notThree dgn delta outside
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts gggr fyz ambientRoots certificate
  centreSpin fullCover centreClifford naturalKernel naturalSurjective simple nonabelian
  brauerSource ordinarySource ordinary membership productFormula
  psi quotientBlocks ambient targetBlocks in
/-- The same selected principal triple holds on the chosen honest ambient's
actual full radical normalizer, with the prescribed quotient and local characters. -/
theorem selected_blockTriple_on_honest_normalizer :
    Nonempty (BlockTripleWitness (TypeBButterflyHonestTargetRoots.targetData
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks) (TypeBButterflyHonestTargetRoots.baseTheta
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks) (TypeBButterflyHonestTargetRoots.localPhi
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks)) := by
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
  let sourceBlocks := catalogues (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))) hUT
  let D1 := TypeBBSCentralQuotientPairTransport.quotientData
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) sourceBlocks quotientBlocks
  let theta1 := TypeBBSCentralQuotientPairTransport.quotientTheta
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) sourceBlocks quotientBlocks
  let phi1 := TypeBBSCentralQuotientPairTransport.quotientPhi
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) sourceBlocks quotientBlocks navarro
  let e := ((TypeBRankThreePrincipalQuotientComparison.referenceToPairBase
  S SH literal literalH Msys root rootCalibration navarro guard b hb
  parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
  simple nonabelian psi)).symm.trans ambient.baseEquiv
  have images : SameConjugationImage (TypeBBSCentralQuotientPairTransport.quotientBase
  (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel)) ambient.base e :=
    TypeBRankThreePrincipalButterflyAmbientImages.selected_sameConjugationImage
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      (navarro := navarro) (centreSpin := centreSpin) (fullCover := fullCover)
      (simple := simple) (nonabelian := nonabelian)
      (naturalSurjective := naturalSurjective) (psi := psi) (ambient := ambient)
      (centreClifford := centreClifford) (naturalKernel := naturalKernel)
  have localEq : secondLocalAmbient (TypeBBSCentralQuotientPairTransport.quotientBase
  (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel)) ambient.base e (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient
  (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)))) =
      AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ambient :=
    TypeBRankThreePrincipalButterflyAmbientImages.selected_secondLocalAmbient_eq_normalizer
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective)
      (centreClifford := centreClifford) (naturalKernel := naturalKernel)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts centreSpin fullCover simple nonabelian
      psi ambient hUT
  let localId := TypeBRankThreePrincipalButterflyLocalCharacter.honestLocalIdentification
    S SH literal literalH Msys root rootCalibration navarro guard b hb
    parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
    simple nonabelian psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) hUT ambient
  have baseId : CharacterIdentification e D1.base ((TypeBButterflyHonestTargetRoots.targetData
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks)).base theta1 (TypeBButterflyHonestTargetRoots.baseTheta
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks) :=
    baseCharacterIdentification ((TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi)).iota ((TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi)).brauer (TypeBRankThreePrincipalQuotientComparison.referenceToPairBase
  S SH literal literalH Msys root rootCalibration navarro guard b hb
  parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
  simple nonabelian psi) ambient.baseEquiv
      D1.base theta1 targetBlocks.base
      (TypeBRankThreePrincipalQuotientComparison.pairRoot_lift
        S SH literal literalH Msys root rootCalibration navarro guard b hb
        parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
        simple nonabelian psi (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) hUT sourceBlocks quotientBlocks)
      (TypeBRankThreePrincipalQuotientComparison.pairTheta_character
        S SH literal literalH Msys root rootCalibration navarro guard b hb
        parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
        simple nonabelian psi (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) hUT sourceBlocks quotientBlocks)
  have localChar : CharacterIdentification localId.equiv D1.localData
      ((TypeBButterflyHonestTargetRoots.targetData
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks)).localData phi1 (TypeBButterflyHonestTargetRoots.localPhi
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks) :=
    TypeBRankThreePrincipalButterflyLocalCharacter.localCharacterIdentification
      S SH literal literalH Msys root rootCalibration navarro guard b hb
      parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
      simple nonabelian psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) hUT sourceBlocks quotientBlocks ambient targetBlocks.localData
  have ambientAgree : AmbientRootsCompatible D1 (TypeBButterflyHonestTargetRoots.targetData
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks) :=
    TypeBButterflyHonestTargetRoots.ambientRootsCompatible
      (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks
      D1 (TypeBBSCentralQuotientPairTransport.quotientData_ambient_residue
        (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) sourceBlocks quotientBlocks)
  exact transfer_to_actualLocal (TypeBBSCentralQuotientPairTransport.quotientBase
  (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel)) ambient.base e (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient
  (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (embedded_center_eq_bot parameters N fieldSource C
  centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv
  (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))))
    (AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ambient)
    butterfly localEq D1 (TypeBButterflyHonestTargetRoots.targetData
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks) localId theta1 phi1 (TypeBButterflyHonestTargetRoots.baseTheta
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks) (TypeBButterflyHonestTargetRoots.localPhi
  (TypeBRankThreePrincipalReferenceBinding.problem
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
  (F := F) (K := K) (O := O) (k := k)
  S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
  (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)) ambient Msys (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb psi) ((show RootResidueCompatible Msys ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation
  S SH literal literalH Msys root rootCalibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
  (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi))).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)) targetBlocks)
    images ambientAgree baseId localChar triple

end Selected

end ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
