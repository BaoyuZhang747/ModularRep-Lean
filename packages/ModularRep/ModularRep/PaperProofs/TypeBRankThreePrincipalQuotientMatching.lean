import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerAction
import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientWeightFibre
import ModularRep.PaperProofs.TypeBRankThreePrincipalFixedRootFamilyBinding

/-!
# The complete principal correspondence on the common reference quotient

The map composes the complete inverse Brauer fibre, the prescribed principal
source theorem and the computed specified quotient weight fibre. The actions
use the same actual quotient automorphisms. Every quotient automorphism has
an original principal-block stabilizer representative, which gives the full
automorphism equation for the graph on actual characters and weight classes.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientMatching

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCriterionHypotheses TypeBCliffordCarriers TypeBCentralKernelBlockSource
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open CyclicOuterLemma37Concrete CyclicOuterLemma37ActualBlockFibres
open TypeBRankThreePrincipalFieldMatchingSplitting TypeBCliffordOrthogonalAmbientQuotient
open TypeBGreenPrincipalConstituentSource TypeBLocalPhysicalBlockBinding
open TypeBRankThreePrincipalMatchedInertia TypeBRankThreePrincipalAmbientFieldMatching
open TypeBRankThreePrincipalBrauerOrbitBinding
open TypeBCentralKernelInertia TypeBOrthogonalOmegaCarriers
open EvenFieldFLZ318FixedTheoremGate
open TypeBRankThreePrincipalQuotientBrauerFibre

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section QuotientActions

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card (G F))]
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (guard : GuardedBlockCompatibility root S.operations)
  (b : LiteralPrimitiveBlock k (G F))
  {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (hb : IsPrincipal b)

/-- The complete computed quotient weight fibre at the original specified label. -/
abbrev QuotientWeightFibre :=
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
  (TypeBRankThreePrincipalQuotientWeightFibre.quotientSource S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).Fibre b

/-- The complete weight equivalence uses the computed quotient operations. -/
def weightEquiv : Definition35Weight (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b) ≃ (QuotientWeightFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
  exact TypeBRankThreePrincipalQuotientWeightFibre.fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb b

@[simp] theorem weightEquiv_val (w : Definition35Weight (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b)) :
    ((weightEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) w).val = CharacterWeight.conjugacyClassGroupEquiv (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) w.val := rfl

/-- The target label is fixed under the actual original-family quotient actor. -/
theorem quotientBlock_fixed (a : (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).Gamma) :
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
    inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • b = b := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
  let alpha : MulAut (G F) :=
    (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).gamma a⁻¹
  have cancel : MulAut.congr (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm
      (MulAut.congr (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) alpha) = alpha := by
    simpa only [MulEquiv.symm_symm] using
      (OddTwoGroupEquivWeightBlocks.congr_symm_congr
        (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb).symm alpha)
  change MulOpposite.op (MulAut.congr (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm
    (MulAut.congr (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) alpha)) • b = b
  rw [cancel]
  exact (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).gammaBlock_fixed a

/-- The weight fibre action restricts actual quotient automorphisms. -/
def quotientWeightAction : MulAction (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).Gamma (QuotientWeightFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
  exact rightWeightFibreMulAction (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) (TypeBRankThreePrincipalQuotientWeightFibre.quotientSource S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) b
    (quotientBlock_fixed S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)

@[simp] theorem quotientWeightAction_val (a : (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).Gamma) (w : (QuotientWeightFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    letI := quotientWeightAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    (a • w).val = inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • w.val := rfl

/-- The full weight equivalence has the prescribed opposite-automorphism value. -/
theorem weightEquiv_inverseOp_val (a : (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).Gamma)
    (w : Definition35Weight (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b)) :
    letI := definition35WeightAction (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b)
    ((weightEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) (a • w)).val = inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • ((weightEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) w).val := by
  letI := definition35WeightAction (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b)
  exact TypeBRankThreePrincipalQuotientWeightFibre.allWeights_op_smul
    S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (inverseOpHom (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).gamma a) w.val

/-- The complete original and quotient weight fibres have the same action. -/
theorem weightEquiv_equivariant (a : (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).Gamma)
    (w : Definition35Weight (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b)) :
    letI := definition35WeightAction (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b)
    letI := quotientWeightAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    (weightEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) (a • w) = a • ((weightEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) w) := by
  letI := definition35WeightAction (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b)
  letI := quotientWeightAction S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  apply Subtype.ext
  exact weightEquiv_inverseOp_val S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb a w

/-- Every actual quotient opposite automorphism comes from the principal stabilizer. -/
theorem quotientActor_surjective : Function.Surjective (inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) := by
  letI := physicalBlockFintype S
  intro alpha
  let original : (MulAut (G F))ᵐᵒᵖ :=
    MulOpposite.op (MulAut.congr (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm alpha.unop)
  have fixed : original ∈ PrimitiveBlockStabilizer b := by
    exact TypeBCentralKernelPrincipalStability.principal_op_smul_eq
      (physicalDecomposition S literal) b hb original
  let a : (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).Gamma := ⟨original, fixed⟩
  refine ⟨a, ?_⟩
  have old : inverseOpHom (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root calibration navarro guard b).gamma a = original :=
    inverseOpHom_primitiveStabilizerHom b a
  rw [TypeBRankThreePrincipalQuotientBrauerAction.gammaQ_inverseOp
    S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb, old]
  exact congrArg MulOpposite.op
    (OddTwoGroupEquivWeightBlocks.congr_symm_congr (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) alpha.unop)

end QuotientActions

local instance omegaOrdinaryRoots (F K : Type) [Field F] [Finite F] [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (H F))] :
    HasEnoughRootsOfUnity K (Nat.card (G F)) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))

section Principal

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
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (Omega 3 F))

/-- The complete quotient map is the actual three existing equivalences in sequence. -/
def matching : (QuotientBrauerFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) ≃ (QuotientWeightFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) :=
  (TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm.trans ((TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts).trans (weightEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb))

/-- Its value is the actual group image of the source theorem's matched weight class. -/
theorem matching_val (phi : (QuotientBrauerFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) phi).val =
      CharacterWeight.conjugacyClassGroupEquiv (quotientEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
        ((TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts) ((TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi)).val := rfl

/-- The original character and its actual descended fibre have the same matched image. -/
theorem matching_on_original (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b)) :
    (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) ((TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) psi) = (weightEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) ((TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts) psi) := by
  change (weightEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) ((TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts) ((TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm ((TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) psi))) =
    (weightEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) ((TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts) psi)
  rw [Equiv.symm_apply_apply]

@[simp] theorem matching_apply_symm_apply (w : (QuotientWeightFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm w) = w :=
  (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).apply_symm_apply w

@[simp] theorem matching_symm_apply_apply (phi : (QuotientBrauerFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) phi) = phi :=
  (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm_apply_apply phi

/-- Every member of the complete computed quotient weight fibre has one preimage. -/
theorem matching_existsUnique (w : (QuotientWeightFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    ∃! phi : (QuotientBrauerFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb), (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) phi = w := by
  refine ⟨(matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm w, (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).apply_symm_apply w, ?_⟩
  intro phi value
  exact (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).injective
    (value.trans ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).apply_symm_apply w).symm)

/-- The graph is on actual quotient characters and actual quotient weight classes. -/
def Graph (phi : IBr (quotientRoot S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := (quotientGroup S SH literal literalH Msys root rootCalibration navarro guard b hb))) : Prop :=
  ∃ chi : (QuotientBrauerFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb), chi.val = phi ∧ ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) chi).val = w

/-- On the complete fibres the raw graph is exactly this matching. -/
theorem graph_iff (phi : (QuotientBrauerFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) (w : (QuotientWeightFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    (Graph (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) phi.val w.val ↔ (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) phi = w := by
  constructor
  · rintro ⟨chi, character, weight⟩
    have hchi : chi = phi := Subtype.ext character
    subst chi
    exact Subtype.ext weight
  · intro matched
    exact ⟨phi, rfl, congrArg Subtype.val matched⟩

variable
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb
    (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C))
  {coefficient : SpathCoefficientField 2 k Msys.prime}
  (fyz : TypeBRankThreePrincipalWeightFieldSplitting.FYZCorollary363SplittingSource
    F r f parameters Msys coefficient root rootH
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys root rootCalibration)
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys rootH rootHCalibration)
    S SH literal literalH guard guardH b hb bH hbH)
  (naturalSurjective : Function.Surjective
    (TypeBAutomorphismSource.ambientAutomorphism fieldSource))

include gggr fyz naturalSurjective in
/-- Both complete quotient fibres use the same actual Gamma homomorphism. -/
theorem matching_equivariant (a : (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b).Gamma) (phi : (QuotientBrauerFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    letI := TypeBRankThreePrincipalQuotientBrauerAction.quotientAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    letI := quotientWeightAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) (a • phi) = a • ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) phi) := by
  letI := definition35BrauerAction (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b)
  letI := definition35WeightAction (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b)
  letI := TypeBRankThreePrincipalQuotientBrauerAction.quotientAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  letI := quotientWeightAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  change (weightEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) ((TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts) ((TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm (a • phi))) =
    a • ((weightEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) ((TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts) ((TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi)))
  rw [TypeBRankThreePrincipalQuotientBrauerAction.fibreEquiv_symm_equivariant S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb]
  have source := TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv_equivariant
    (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
  rw [source a ((TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi)]
  exact weightEquiv_equivariant S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb a ((TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts) ((TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi))

include gggr fyz naturalSurjective in
/-- The inverse correspondence respects the same actual quotient action. -/
theorem matching_symm_equivariant (a : (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b).Gamma) (w : (QuotientWeightFibre S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    letI := TypeBRankThreePrincipalQuotientBrauerAction.quotientAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    letI := quotientWeightAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm (a • w) = a • ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm w) := by
  letI := TypeBRankThreePrincipalQuotientBrauerAction.quotientAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  letI := quotientWeightAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  apply (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).injective
  calc
    (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm (a • w)) = a • w := (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).apply_symm_apply (a • w)
    _ = a • ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm w)) :=
      congrArg (fun v => a • v) ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).apply_symm_apply w).symm
    _ = (matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) (a • ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm w)) :=
      (matching_equivariant (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian a ((matching (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian).symm w)).symm

include gggr fyz naturalSurjective in
/-- The actual raw graph is stable under the prescribed Gamma actor. -/
theorem graph_gamma_forward (a : (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b).Gamma)
    (phi : IBr (quotientRoot S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := (quotientGroup S SH literal literalH Msys root rootCalibration navarro guard b hb)))
    (h : (Graph (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) phi w) :
    (Graph (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) (inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • phi) (inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • w) := by
  letI := TypeBRankThreePrincipalQuotientBrauerAction.quotientAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  letI := quotientWeightAction S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  rcases h with ⟨chi, character, weight⟩
  refine ⟨a • chi, ?_, ?_⟩
  · change inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • chi.val =
      inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • phi
    exact congrArg (fun theta => inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • theta) character
  · have acted := congrArg Subtype.val
      (matching_equivariant (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian a chi)
    exact acted.trans
      (congrArg (fun v => inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • v) weight)

include gggr fyz naturalSurjective in
/-- Every actual quotient automorphism preserves the complete correspondence graph. -/
theorem graph_opAut (alpha : (MulAut (quotientGroup S SH literal literalH Msys root rootCalibration navarro guard b hb))ᵐᵒᵖ)
    (phi : IBr (quotientRoot S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := (quotientGroup S SH literal literalH Msys root rootCalibration navarro guard b hb))) :
    (Graph (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) (alpha • phi) (alpha • w) ↔ (Graph (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) phi w := by
  obtain ⟨a, rfl⟩ := quotientActor_surjective S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb alpha
  constructor
  · intro h
    have back := graph_gamma_forward (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian a⁻¹
      (inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • phi) (inverseOpHom (TypeBRankThreePrincipalQuotientBrauerAction.gammaQ S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) a • w) h
    simpa only [map_inv, inv_smul_smul] using back
  · intro h
    exact graph_gamma_forward (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian a phi w h

end Principal

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
