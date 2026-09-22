import ModularRep.PaperProofs.TypeBRankThreePrincipalFullAutMatching
import ModularRep.PaperProofs.TypeBFixedRootCriterionFamilySplitting

/-!
# The principal correspondence in its literal fixed-root family

The two existing weight catalogues determine the criterion's primitive
block data. The downstairs family retains its prescribed calibrated root,
the same modular system and the scoped reductions of the selected weights'
own ordinary characters. The principal map is the accepted oriented map,
transported only across the equality of support and specified block membership.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalFixedRootFamilyBinding

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCriterionHypotheses
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open CyclicOuterLemma37LiteralLocalExtension

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section Family

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)

/-- Both decompositions come from the already prescribed specified operations. -/
def blockData :
    letI := S.operations.ambientBlockData.fintypeBlock
    letI := SH.operations.ambientBlockData.fintypeBlock
    BlockData (ell := 2) (k := k) (K := K) (G F) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := SH.operations.ambientBlockData.fintypeBlock
  exact {
    downstairs := physicalDecomposition S literal
    upstairs := physicalDecomposition SH literalH
    weightDownstairs := S
    weightUpstairs := SH
    downstairs_idempotent := literal
    upstairs_idempotent := literalH }

variable (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card (G F))]
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (guard : GuardedBlockCompatibility root S.operations)

/-- The family keeps the original root and derives its own-character reductions. -/
def family : Definition35Family 2 := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := SH.operations.ambientBlockData.fintypeBlock
  let blocks := blockData S SH literal literalH
  exact TypeBFixedRootCriterionFamilySplitting.downstairsFamily
    (G F) root blocks Nat.prime_two
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    (localReductionData (G F) Msys root calibration navarro blocks guard)

@[simp] theorem family_iota :
    (family S SH literal literalH Msys root calibration navarro guard).iota = root := rfl

@[simp] theorem family_blockSource :
    (family S SH literal literalH Msys root calibration navarro guard).blockSource = S := rfl

@[simp] theorem family_localReduction (b : LiteralPrimitiveBlock k (G F))
    (w : S.Fibre b) :
    (family S SH literal literalH Msys root calibration navarro guard).localReduction b w =
      selectedReduction Msys root calibration navarro S b w := rfl

/-- The same prescribed guard interprets the family's specified local blocks. -/
theorem family_blockCompatibility :
    GuardedBlockCompatibility
      (family S SH literal literalH Msys root calibration navarro guard).iota
      (family S SH literal literalH Msys root calibration navarro guard).blockSource.operations :=
  guard

/-- The local root agrees with the prescribed root on its actual quotient. -/
theorem family_rootAgreement (b : LiteralPrimitiveBlock k (G F)) (w : S.Fibre b) :
    QuotientRootAgreement root (SelectedRadical S b w)
      ((family S SH literal literalH Msys root calibration navarro guard).localReduction b w).iota := by
  letI := S.operations.ambientBlockData.fintypeBlock
  exact selectedReduction_rootAgreement Msys root calibration navarro S b w

/-- Specified support and the family's Brauer block membership are equivalent. -/
def brauerFibreEquiv (b : LiteralPrimitiveBlock k (G F)) :
    OmegaBrauer F root b ≃
      Definition35Brauer
        ((family S SH literal literalH Msys root calibration navarro guard).problem b) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  exact TypeBCentralKernelBrauerBlocks.supportedEquivIBrBlock
    root (physicalDecomposition S literal) b

@[simp] theorem brauerFibreEquiv_val (b : LiteralPrimitiveBlock k (G F))
    (theta : OmegaBrauer F root b) :
    (brauerFibreEquiv S SH literal literalH Msys root calibration navarro guard b theta).val =
      theta.val := rfl

/-- The family acts by the actual opposite-automorphism block stabilizer. -/
def stabilizerAdapter (b : LiteralPrimitiveBlock k (G F)) :
    Definition35AutomorphismStabilizerAdapter
      ((family S SH literal literalH Msys root calibration navarro guard).problem b) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := SH.operations.ambientBlockData.fintypeBlock
  exact TypeBFixedRootCriterionFamilySplitting.downstairsFamily_stabilizerAdapter
    (G F) root (blockData S SH literal literalH) Nat.prime_two
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    (localReductionData (G F) Msys root calibration navarro
      (blockData S SH literal literalH) guard) b

end Family

section Principal

open TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalFieldMatchingSplitting TypeBCliffordOrthogonalAmbientQuotient
open TypeBGreenPrincipalConstituentSource TypeBLocalPhysicalBlockBinding
open TypeBRankThreePrincipalMatchedInertia TypeBRankThreePrincipalAmbientFieldMatching
open TypeBRankThreePrincipalBrauerOrbitBinding
open TypeBCentralKernelInertia TypeBOrthogonalOmegaCarriers
open EvenFieldFLZ318FixedTheoremGate

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

local notation "principalFamily" =>
  family S SH literal literalH Msys root rootCalibration navarro guard
local notation "fibreMap" =>
  brauerFibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
local notation "chosenMap" => TypeBRankThreePrincipalOrbitChoice.orientedOmegaEquiv
  (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
  (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
  green principalLift clifford principalRestriction covering counts

/-- The newly oriented map on the same family's complete principal fibres. -/
def principalEquiv :
    Definition35Brauer
        ((family S SH literal literalH Msys root rootCalibration navarro guard).problem b) ≃
      Definition35Weight
        ((family S SH literal literalH Msys root rootCalibration navarro guard).problem b) := by
  let omega : OmegaBrauer F root b ≃ OmegaWeight F S b :=
    TypeBRankThreePrincipalOrbitChoice.orientedOmegaEquiv
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts
  exact (brauerFibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b).symm.trans
    omega

local notation "familyMap" => principalEquiv
  (S := S) (SH := SH)
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
  (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
  green principalLift clifford principalRestriction covering counts

/-- The family conversion leaves the matched actual weight class unchanged. -/
theorem principalEquiv_apply_supported (theta : OmegaBrauer F root b) :
    familyMap (fibreMap theta) = chosenMap theta :=
  congrArg chosenMap ((fibreMap).symm_apply_apply theta)

@[simp] theorem principalEquiv_apply_symm_apply
    (w : Definition35Weight ((principalFamily).problem b)) :
    familyMap ((familyMap).symm w) = w :=
  (familyMap).apply_symm_apply w

@[simp] theorem principalEquiv_symm_apply_apply
    (psi : Definition35Brauer ((principalFamily).problem b)) :
    (familyMap).symm (familyMap psi) = psi :=
  (familyMap).symm_apply_apply psi

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

include gggr fyz centreSpin fullCover naturalSurjective in
/-- The criterion action is the same full actual primitive-block stabilizer action. -/
theorem principalEquiv_equivariant :
    Definition35Equivariant ((principalFamily).problem b) familyMap := by
  letI := definition35BrauerAction ((principalFamily).problem b)
  letI := definition35WeightAction ((principalFamily).problem b)
  intro a psi
  have h := TypeBRankThreePrincipalFullAutMatching.orientedOmegaEquiv_blockStabilizer
    (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
    a ((fibreMap).symm psi)
  apply Subtype.ext
  exact congrArg Subtype.val h

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
/-- The family's own selected raw representative has the complete embedded pair witness. -/
theorem principalEquiv_selectedRepresentative
    (psi : Definition35Brauer ((principalFamily).problem b)) :
    letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)
      (matrixNaturalAction F parameters N fieldSource C)
    letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)
    TypeBCentralKernelPairRepresentativeSplitting.WitnessAt
      Msys (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource))
      (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F)
        (soFieldAction 3 F parameters le_rfl N C fieldSource) root)
      (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F)
        (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration)
      catalogues navarro
      (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F)
        (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)
      (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F)
        (soFieldAction 3 F parameters le_rfl N C fieldSource)
        (selectedCharacterWeight S b (familyMap psi))) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
  exact TypeBRankThreePrincipalOrbitChoice.orientedOmegaEquiv_allRepresentatives
    (S := S) (SH := SH)
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts gggr fyz certificate centreSpin fullCover
    centreClifford naturalKernel naturalSurjective simple nonabelian brauerSource
    ordinarySource ordinary membership productFormula ((fibreMap).symm psi)
    (selectedCharacterWeight S b (familyMap psi))
    (selectedCharacterWeight_spec S b (familyMap psi))

end Principal

end ModularRep.PaperProofs.TypeBRankThreePrincipalFixedRootFamilyBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
