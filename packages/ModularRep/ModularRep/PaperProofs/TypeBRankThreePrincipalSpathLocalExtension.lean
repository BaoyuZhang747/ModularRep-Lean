import ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyTransport
import ModularRep.PaperProofs.TypeBHonestSpathLocalExtension

/-!
# The actual selected local extension and all intermediate blocks

The accepted selected triple is derived first. The fixed global character
then determines one local extension for every actual intermediate subgroup,
with the separate centralizer constituent-support conclusion retained.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalSpathLocalExtension

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

attribute [local instance]
  TypeBRankThreePrincipalButterflyTransport.groupFintype
  TypeBRankThreePrincipalButterflyTransport.omegaOrdinaryRoots
  TypeBRankThreePrincipalButterflyTransport.selectedEmbeddedNormal
  TypeBRankThreePrincipalButterflyTransport.problemAlgebra

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

variable
  (global : SpathPositiveQTopBlockChoice.ChosenGlobalExtensionData ambient)
  (globalRoot : global.ambientRoot =
    TypeBModularGroupRootBinding.groupRoot Msys ambient.A)
  (localCertificate :
    TypeBSpathHonestLocalExtensionSource.HonestLocalExtensionCertificate 2 k K)

include S SH root rootH b hb bH hbH literal literalH parameters N fieldSource C
  Msys rootCalibration rootHCalibration guard guardH notThree dgn delta outside
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts gggr fyz ambientRoots certificate
  centreSpin fullCover centreClifford naturalKernel naturalSurjective simple nonabelian
  brauerSource ordinarySource ordinary membership productFormula
  psi quotientBlocks ambient targetBlocks global globalRoot localCertificate in
/-- For the same selected principal pair and fixed global character, one
local extension satisfies all actual intermediate-block and support clauses. -/
theorem selected_extensions_all_intermediate :
    ∃ extensions : SpathCharacterExtensions
    (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b)
    (TypeBRankThreePrincipalReferenceBinding.reference
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b hb)
    psi
    (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
    (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    ambient,
      extensions.ambientRoot = global.ambientRoot ∧
      extensions.globalExtension.val.val = global.globalExtension.val.val ∧
      Nonempty (IntermediateBlockSource
    (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b)
    (TypeBRankThreePrincipalReferenceBinding.reference
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b hb)
    psi
    (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
    (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    ambient extensions) ∧
      ∀ nu : IBr (TypeBSpathHonestLocalExtensionSource.centralizerRoot
    (TypeBButterflyHonestTargetRoots.targetData
    (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b)
    (TypeBRankThreePrincipalReferenceBinding.reference
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b hb)
    psi
    (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
    (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    ambient
    Msys
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (show RootResidueCompatible Msys (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)
    targetBlocks)),
        OccursAlong (Subgroup.centralizer (ambient.base : Set ambient.A)).subtype
          global.ambientRoot
          (TypeBSpathHonestLocalExtensionSource.centralizerRoot
    (TypeBButterflyHonestTargetRoots.targetData
    (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b)
    (TypeBRankThreePrincipalReferenceBinding.reference
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b hb)
    psi
    (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
    (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    ambient
    Msys
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (show RootResidueCompatible Msys (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)
    targetBlocks))
          global.globalExtension.val nu ↔
        OccursAlong (TypeBHonestCentralizerLocalBinding.centralizerToLocal
          (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi) ambient)
          extensions.localAmbientRoot
          (TypeBSpathHonestLocalExtensionSource.centralizerRoot
    (TypeBButterflyHonestTargetRoots.targetData
    (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b)
    (TypeBRankThreePrincipalReferenceBinding.reference
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b hb)
    psi
    (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
    (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    ambient
    Msys
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (show RootResidueCompatible Msys (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)
    targetBlocks))
          extensions.localExtension.val nu := by
  obtain ⟨witness⟩ :=
    TypeBRankThreePrincipalButterflyTransport.selected_blockTriple_on_honest_normalizer
      (F := F)
      (K := K)
      (O := O)
      (k := k)
      (r := r)
      (f := f)
      (S := S)
      (SH := SH)
      (root := root)
      (rootH := rootH)
      (b := b)
      (hb := hb)
      (bH := bH)
      (hbH := hbH)
      (literal := literal)
      (literalH := literalH)
      (parameters := parameters)
      (N := N)
      (fieldSource := fieldSource)
      (C := C)
      (Msys := Msys)
      (rootCalibration := rootCalibration)
      (rootHCalibration := rootHCalibration)
      (delta := delta)
      (outside := outside)
      (guard := guard)
      (guardH := guardH)
      (notThree := notThree)
      (dgn := dgn)
      (coefficient := coefficient)
      (catalogues := catalogues)
      (navarro := navarro)
      (butterfly := butterfly)
      (roots := roots)
      (fieldScope := fieldScope)
      (green := green)
      (principalLift := principalLift)
      (clifford := clifford)
      (principalRestriction := principalRestriction)
      (covering := covering)
      (counts := counts)
      (gggr := gggr)
      (fyz := fyz)
      (centreSpin := centreSpin)
      (fullCover := fullCover)
      (naturalSurjective := naturalSurjective)
      (ambientRoots := ambientRoots)
      (certificate := certificate)
      (centreClifford := centreClifford)
      (naturalKernel := naturalKernel)
      (simple := simple)
      (nonabelian := nonabelian)
      (brauerSource := brauerSource)
      (ordinarySource := ordinarySource)
      (ordinary := ordinary)
      (membership := membership)
      (productFormula := productFormula)
      (psi := psi)
      (quotientBlocks := quotientBlocks)
      (ambient := ambient)
      (targetBlocks := targetBlocks)
  exact TypeBHonestSpathLocalExtension.exists_extensions_all_intermediate
    (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b)
    (TypeBRankThreePrincipalReferenceBinding.reference
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b hb)
    psi
    (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
    (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi))
    ambient
    Msys
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi)
    (show RootResidueCompatible Msys (TypeBRankThreePrincipalQuotientLocalPackets.localInflation
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb (principalEquiv (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
    (C := C) (rootCalibration := rootCalibration)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts psi)).iota from
    TypeBModularGroupRootBinding.groupRoot_residue Msys _)
    targetBlocks
    global globalRoot fieldScope localCertificate witness

end Selected

end ModularRep.PaperProofs.TypeBRankThreePrincipalSpathLocalExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
