import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerFibre

/-!
# The actual principal relative block condition

The checked principal correspondence and canonical reference quotient supply
the relative witness. Its matched conditions retain the prescribed quotient
and the intermediate tails derived for that quotient.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalRelativeBlockBinding

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCriterionHypotheses
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily CyclicOuterLemma37LiteralLocalExtension
open TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalFieldMatchingSplitting TypeBCliffordOrthogonalAmbientQuotient
open TypeBGreenPrincipalConstituentSource TypeBLocalPhysicalBlockBinding
open TypeBRankThreePrincipalMatchedInertia TypeBRankThreePrincipalAmbientFieldMatching
open TypeBRankThreePrincipalBrauerOrbitBinding
open TypeBCentralKernelInertia TypeBOrthogonalOmegaCarriers
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

/-- The actual relative witness keeps the canonical quotient in every match. -/
def relative
    (tails : ∀ psi : Definition35Brauer
        (TypeBRankThreePrincipalReferenceBinding.problem
          S SH literal literalH Msys root rootCalibration navarro guard b),
      SpathMatchedBlockConditionTail
        (TypeBRankThreePrincipalReferenceBinding.problem
          S SH literal literalH Msys root rootCalibration navarro guard b)
        (TypeBRankThreePrincipalReferenceBinding.reference
          S SH literal literalH Msys root rootCalibration navarro guard b hb)
        psi
        (TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv
          (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
          (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
          catalogues navarro butterfly roots fieldScope
          green principalLift clifford principalRestriction covering counts psi)
        (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
          S SH literal literalH Msys root rootCalibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb psi)) :
    RelativeBlockConditionWitness
      (TypeBRankThreePrincipalFixedRootFamilyBinding.family
        S SH literal literalH Msys root rootCalibration navarro guard)
      (TypeBRankThreePrincipalReferenceBinding.cover
        S SH literal literalH Msys root rootCalibration navarro guard
        parameters N C centreSpin fullCover simple nonabelian) b where
  automorphismStabilizer :=
    TypeBRankThreePrincipalFixedRootFamilyBinding.stabilizerAdapter
      S SH literal literalH Msys root rootCalibration navarro guard b
  omega :=
    TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts
  equivariant :=
    TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv_equivariant
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts
      gggr fyz centreSpin fullCover naturalSurjective
  reference :=
    TypeBRankThreePrincipalReferenceBinding.reference
      S SH literal literalH Msys root rootCalibration navarro guard b hb
  commonCentralKernel :=
    TypeBRankThreePrincipalReferenceBinding.commonKernel
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  quotientCover :=
    TypeBRankThreePrincipalReferenceBinding.quotientCover
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  QuotientBlock := LiteralPrimitiveBlock k (G F)
  fintypeQuotientBlock := TypeBRankThreePrincipalQuotientBrauerFibre.physicalBlockFintype S
  quotientBlockIdempotent :=
    TypeBRankThreePrincipalQuotientBrauerFibre.quotientIdempotent
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  quotientBlocks :=
    TypeBRankThreePrincipalQuotientBrauerFibre.quotientBlocks
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  quotientBlock := b
  matched := fun psi => {
    quotient := TypeBRankThreePrincipalReferenceBinding.quotientBrauer
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi
    tail := tails psi }
  descendedBrauer_liesInQuotientBlock :=
    TypeBRankThreePrincipalQuotientBrauerFibre.quotientBrauer_block
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb

end ModularRep.PaperProofs.TypeBRankThreePrincipalRelativeBlockBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
