import ModularRep.PaperProofs.TypeBRankThreePrincipalRelativeBlockBinding
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# Fixed Brauer descent for the actual principal relative record

The relative record stores the canonical reference quotient for every
character. Its fixed root and complete reverse Brauer fibre are therefore
constructed from the existing quotient equivalence. The original prescribed
root remains the value convention on the quotient's finite root domain.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalRelativeBrauerBinding

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

open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open TypeBRankThreePrincipalFixedRootFamilyBinding TypeBFullBlockCondition

attribute [local instance]
  TypeBRankThreePrincipalFixedRootFamilyBinding.groupFintype
  TypeBRankThreePrincipalFixedRootFamilyBinding.omegaOrdinaryRoots

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
  (simple : IsSimpleGroup (Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (Omega 3 F))
  (tails : ∀ psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem
      S SH literal literalH Msys root rootCalibration navarro guard b),
    SpathMatchedBlockConditionTail
      (TypeBRankThreePrincipalReferenceBinding.problem
      S SH literal literalH Msys root rootCalibration navarro guard b)
      (TypeBRankThreePrincipalReferenceBinding.reference
      S SH literal literalH Msys root rootCalibration navarro guard b hb) psi
      (principalEquiv (S := S) (SH := SH)
        (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
        (C := C) (rootCalibration := rootCalibration)
        catalogues navarro butterfly roots fieldScope green principalLift clifford
        principalRestriction covering counts psi)
      (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi))

/-- Every matched quotient has the one canonical reference root. -/
def fixedRoots :
    FixedQuotientRootSource
      (TypeBRankThreePrincipalRelativeBlockBinding.relative
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails) where
  matchedRoot_eq_reference _ := rfl

/-- Root transport preserves the already constructed quotient character. -/
theorem fixedDescendedBrauer_eq_quotientBrauer
    (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem
      S SH literal literalH Msys root rootCalibration navarro guard b)) :
    fixedDescendedBrauer
      (TypeBRankThreePrincipalRelativeBlockBinding.relative
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails)
      (fixedRoots
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails) psi =
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).brauer := by
  apply Subtype.ext
  exact fixedDescendedBrauer_val
    (TypeBRankThreePrincipalRelativeBlockBinding.relative
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails)
    (fixedRoots
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails) psi

/-- The complete quotient fibre supplies the reverse implication for this record. -/
def brauerReverse :
    QuotientBlockFibreReverseSource
      (TypeBRankThreePrincipalRelativeBlockBinding.relative
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails)
      (fixedRoots
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails) := by
  letI := TypeBRankThreePrincipalQuotientBrauerFibre.physicalBlockFintype S
  refine { of_quotientBlock := ?_ }
  intro phi membership
  obtain ⟨psi, character, _⟩ :=
    (TypeBRankThreePrincipalQuotientBrauerFibre.quotientBrauer_existsUnique
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb phi).mp membership
  exact ⟨psi, (fixedDescendedBrauer_eq_quotientBrauer
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails psi).trans character⟩

/-- The actual quotient uses the original root on its required finite domain. -/
theorem quotientRoots_agree :
    RootLiftAgreement
      (fixedQuotientRoot
        (TypeBRankThreePrincipalRelativeBlockBinding.relative
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
      (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails))
      (family S SH literal literalH Msys root rootCalibration navarro guard).iota := by
  intro zeta
  exact congrFun
    (TypeBRankThreePrincipalQuotientBrauerFibre.quotientRoot_lift
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
    zeta.val.val

end ModularRep.PaperProofs.TypeBRankThreePrincipalRelativeBrauerBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
