import ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitChoice
import ModularRep.PaperProofs.TypeBMatrixOmegaFullAutomorphismBinding

/-!
# The oriented principal correspondence under full automorphisms

Surjectivity of the prescribed matrix ambient action promotes the accepted
ambient equivariance to every actual automorphism. The positive right twist
uses an ambient lift of the inverse automorphism. The same map is then
equivariant under the full opposite automorphism group and the actual
primitive-block stabilizer, with its prescribed inverse homomorphism.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalFullAutMatching

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
open TypeBCentralKernelPrincipalStability TypeBCliffordOrthogonalAmbientActionBinding
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

include S literal hb in
/-- The stabilizer is the full actual opposite automorphism group. -/
theorem principalBlockStabilizer_eq_top : PrimitiveBlockStabilizer b = ⊤ := by
  letI := S.operations.ambientBlockData.fintypeBlock
  apply top_unique
  intro alpha _
  exact principal_op_smul_eq (physicalDecomposition S literal) b hb alpha

variable
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

local notation "chosenMap" => TypeBRankThreePrincipalOrbitChoice.orientedOmegaEquiv
  (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
  (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
  green principalLift clifford principalRestriction covering counts

include gggr fyz centreSpin fullCover naturalSurjective in
/-- Every positive right twist is induced by an inverse ambient actor. -/
theorem orientedOmegaEquiv_autTwist (alpha : MulAut (G F))
    (theta : OmegaBrauer F root b) :
    chosenMap (brauerTwistEquiv S literal root b hb alpha theta) =
      weightTwistEquiv S literal b hb alpha (chosenMap theta) := by
  letI := omegaBrauerAmbientAction F S literal root b hb parameters N fieldSource C
  letI := omegaWeightAmbientAction F S literal b hb parameters N fieldSource C
  obtain ⟨a, ha⟩ :=
    TypeBMatrixOmegaFullAutomorphismBinding.omegaAmbientAction_surjective
      fieldSource le_rfl C centreSpin fullCover naturalSurjective alpha⁻¹
  have actor : omegaAmbientAction fieldSource le_rfl C a⁻¹ = alpha := by
    rw [map_inv, ha, inv_inv]
  have characterAction : a • theta =
      brauerTwistEquiv S literal root b hb alpha theta := by
    apply Subtype.ext
    change IrreducibleBrauerCharacter.twist root theta.val
      (omegaAmbientAction fieldSource le_rfl C a⁻¹) =
      IrreducibleBrauerCharacter.twist root theta.val alpha
    rw [actor]
  have weightAction : a • chosenMap theta =
      weightTwistEquiv S literal b hb alpha (chosenMap theta) := by
    apply Subtype.ext
    change CharacterWeight.rightTwistConjugacyClass
      (omegaAmbientAction fieldSource le_rfl C a⁻¹) (chosenMap theta).val =
      CharacterWeight.rightTwistConjugacyClass alpha (chosenMap theta).val
    rw [actor]
  have equivariant := TypeBRankThreePrincipalOrbitChoice.orientedOmegaEquiv_ambient
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts gggr fyz a theta
  rw [characterAction, weightAction] at equivariant
  exact equivariant

include gggr fyz centreSpin fullCover naturalSurjective in
/-- The full opposite automorphism action uses the same literal fibre actions. -/
theorem orientedOmegaEquiv_opAut (alpha : (MulAut (G F))ᵐᵒᵖ)
    (theta : OmegaBrauer F root b) :
    letI := S.operations.ambientBlockData.fintypeBlock
    letI := principalFibreMulAction (physicalDecomposition S literal) root b hb
    letI := principalWeightOpAction S literal b hb
    chosenMap (alpha • theta) = alpha • chosenMap theta := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := principalFibreMulAction (physicalDecomposition S literal) root b hb
  letI := principalWeightOpAction S literal b hb
  exact orientedOmegaEquiv_autTwist
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
    alpha.unop theta

include gggr fyz centreSpin fullCover naturalSurjective in
/-- The actual block stabilizer acts through its prescribed inverse homomorphism. -/
theorem orientedOmegaEquiv_blockStabilizer (a : PrimitiveBlockStabilizer b)
    (theta : OmegaBrauer F root b) :
    letI := brauerFieldAction S literal root b hb (primitiveStabilizerHom b)
    letI := weightFieldAction S literal b hb (primitiveStabilizerHom b)
    chosenMap (a • theta) = a • chosenMap theta := by
  letI := brauerFieldAction S literal root b hb (primitiveStabilizerHom b)
  letI := weightFieldAction S literal b hb (primitiveStabilizerHom b)
  change chosenMap
      (brauerTwistEquiv S literal root b hb (primitiveStabilizerHom b a⁻¹) theta) =
    weightTwistEquiv S literal b hb (primitiveStabilizerHom b a⁻¹) (chosenMap theta)
  exact orientedOmegaEquiv_autTwist
    (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
    catalogues navarro butterfly roots fieldScope green principalLift clifford
    principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
    (primitiveStabilizerHom b a⁻¹) theta

end ModularRep.PaperProofs.TypeBRankThreePrincipalFullAutMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
