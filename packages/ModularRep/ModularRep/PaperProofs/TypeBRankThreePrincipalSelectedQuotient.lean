import ModularRep.PaperProofs.TypeBRankThreePrincipalFixedRootFamilyBinding
import ModularRep.PaperProofs.TypeBBSCentralQuotientPairTransport

/-!
# The computed quotient of the actual principal selected pair

The selected weight is the representative of the accepted principal
correspondence in its fixed-root specified family. Its derived embedded
pair supplies the actual inertia inclusion. The quotient uses the kernel
computed from that embedded character, mapped into that same inertia.
The prescribed quotient catalogues are fixed before extracting the pair.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalSelectedQuotient

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

/-- Centrelessness is transported through the actual criterion base embedding. -/
theorem embedded_center_eq_bot
    {F : Type} [Field F] [Finite F] {r f : ℕ} [CharP F r]
    (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
    (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
    (fullCover : IsUniversalCentralExtension
      (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
    (centreClifford : TypeBCliffordCentreSource.CentreSource 3 F parameters (by decide))
    (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism fieldSource).ker =
      TypeBAutomorphismSource.embeddedCenter fieldSource) :
    Subgroup.center (embeddedG (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)) = ⊥ := by
  let e := TypeBCriterionEmbeddedPairBinding.baseEquiv (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
  have originalCentre : Subgroup.center (G F) = ⊥ :=
    TypeBMatrixOmegaBSStructure.omega_center_eq_bot N parameters fieldSource le_rfl C
      centreSpin fullCover centreClifford naturalKernel
  apply le_antisymm ?_ bot_le
  intro z hz
  have central : e.symm z ∈ Subgroup.center (G F) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      (Subgroup.mem_center_iff.mp hz (e x))
  rw [originalCentre] at central
  change e.symm z = 1 at central
  change z = 1
  apply e.symm.injective
  exact central.trans (map_one e.symm).symm

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
/-- The actual selected representative and its complete pair descend together. -/
theorem selectedQuotient
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
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K) (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
  obtain ⟨hUT, ⟨witness⟩⟩ :=
    TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv_selectedRepresentative
      (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      certificate centreClifford naturalKernel simple nonabelian brauerSource
      ordinarySource ordinary membership productFormula psi
  refine ⟨hUT, ⟨witness⟩, ?_⟩
  exact TypeBBSCentralQuotientPairTransport.quotientPairWitness
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource))
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource) root)
    (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)
    (embedded_center_eq_bot parameters N fieldSource C
      centreSpin fullCover centreClifford naturalKernel)
    (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource)
      (selectedCharacterWeight S b
        (principalEquiv (S := S) (SH := SH)
          (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource)
          (C := C) (rootCalibration := rootCalibration)
          catalogues navarro butterfly roots fieldScope green principalLift clifford
          principalRestriction covering counts psi)))
    hUT Msys
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F)
      (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration)
    _ quotientBlocks navarro witness butterfly

end ModularRep.PaperProofs.TypeBRankThreePrincipalSelectedQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
