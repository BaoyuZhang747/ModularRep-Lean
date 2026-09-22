import ModularRep.PaperProofs.TypeBCentrelessCharacterQuotientEquiv
import ModularRep.PaperProofs.TypeBRankThreePrincipalReferenceBinding
import ModularRep.PaperProofs.TypeBRankThreePrincipalSelectedQuotient

/-!
# The principal common reference quotient and the selected embedded pair

The source is the family's constructed common reference quotient. Its actual
projection is compared with the embedded selected-character quotient and the
base image in the quotient inertia. The selected pair's root and character
are identified with the same-reference quotient Brauer data.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientComparison

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCriterionHypotheses
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily
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
open TypeBRankThreePrincipalReferenceBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

local instance omegaOrdinaryRoots (F K : Type) [Field F] [Finite F] [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (H F))] :
    HasEnoughRootsOfUnity K (Nat.card (G F)) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))

local instance embeddedNormal
    {F : Type} [Field F] [Finite F] {r f : ℕ} [CharP F r] [NeZero f]
    (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N) :
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)).Normal :=
  TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)

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

/-- The source group is the constructed reference quotient of the actual family. -/
abbrev commonQuotient : Type :=
  CentralCharacterQuotient (problem S SH literal literalH Msys root rootCalibration navarro guard b) (reference S SH literal literalH Msys root rootCalibration navarro guard b hb)

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

/-- The first comparison uses the common reference and the embedded selected character. -/
def referenceToEmbedded :
    commonQuotient S SH literal literalH Msys root rootCalibration navarro guard b hb ≃*
      (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) ⧸ (TypeBBSCentralCharacterQuotient.centralKernel (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)) :=
  TypeBCentrelessCharacterQuotientEquiv.quotientEquiv
    (TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) root (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root)
    (reference S SH literal literalH Msys root rootCalibration navarro guard b hb).val (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (centreless parameters N C centreSpin fullCover simple nonabelian) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)

/-- The first comparison commutes with the two literal quotient projections. -/
theorem referenceToEmbedded_mk (g : G F) :
    (referenceToEmbedded S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi)
        (centralCharacterQuotientMap (problem S SH literal literalH Msys root rootCalibration navarro guard b) (reference S SH literal literalH Msys root rootCalibration navarro guard b hb) g) =
      QuotientGroup.mk' (TypeBBSCentralCharacterQuotient.centralKernel (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)) ((TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) g) :=
  TypeBCentrelessCharacterQuotientEquiv.quotientEquiv_mk
    (TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) root (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root)
    (reference S SH literal literalH Msys root rootCalibration navarro guard b hb).val (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (centreless parameters N C centreSpin fullCover simple nonabelian) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) g

/-- The inverse comparison has the same two canonical projections. -/
theorem referenceToEmbedded_symm_mk (g : embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) :
    (referenceToEmbedded S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).symm
        (QuotientGroup.mk' (TypeBBSCentralCharacterQuotient.centralKernel (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)) g) =
      centralCharacterQuotientMap (problem S SH literal literalH Msys root rootCalibration navarro guard b) (reference S SH literal literalH Msys root rootCalibration navarro guard b hb)
        ((TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)).symm g) :=
  TypeBCentrelessCharacterQuotientEquiv.quotientEquiv_symm_mk
    (TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) root (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root)
    (reference S SH literal literalH Msys root rootCalibration navarro guard b hb).val (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (centreless parameters N C centreSpin fullCover simple nonabelian) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) g

/-- Composition identifies the common reference quotient with the actual pair base image. -/
def referenceToPairBase :
    commonQuotient S SH literal literalH Msys root rootCalibration navarro guard b hb ≃* (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) :=
  (referenceToEmbedded S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).trans (TypeBBSCentralQuotientPairTransport.baseQuotientEquiv (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel))

/-- Its forward map is exactly the ambient projection of the embedded original element. -/
theorem referenceToPairBase_projection (g : G F) :
    ((referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi)
      (centralCharacterQuotientMap (problem S SH literal literalH Msys root rootCalibration navarro guard b) (reference S SH literal literalH Msys root rootCalibration navarro guard b hb) g)).val =
      QuotientGroup.mk' (TypeBBSCentralQuotientPairTransport.ambientKernel (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel))
        ((TypeBBSCentralQuotientPairTransport.baseInclusion (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)) ((TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) g)) := by
  exact (congrArg
    (fun x : (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) ⧸ (TypeBBSCentralCharacterQuotient.centralKernel (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)) =>
      ((TypeBBSCentralQuotientPairTransport.baseQuotientEquiv (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) x).val)
    (referenceToEmbedded_mk S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi g)).trans
      (TypeBBSCentralQuotientPairTransport.baseQuotientEquiv_projection
        (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) ((TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) g))

/-- The embedded quotient character is the descent of psi on the one common reference quotient. -/
theorem embeddedQuotient_character :
    (TypeBBSCentralCharacterQuotient.quotientCharacter (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)).val =
      PrimeRegularClassFunction.pullback (referenceToEmbedded S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).symm.toMonoidHom
        (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val := by
  rw [quotientBrauer_val S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi]
  exact TypeBCentrelessCharacterQuotientEquiv.descendedBrauer_pullback
    (TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) root (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root)
    (reference S SH literal literalH Msys root rootCalibration navarro guard b hb).val (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (centreless parameters N C centreSpin fullCover simple nonabelian) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)
    psi.val (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)
    (TypeBCriterionEmbeddedPairBinding.brauerEquiv_val (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)

/-- The embedded quotient root has the same full lift as the common-reference root. -/
theorem embeddedQuotient_root_lift :
    (TypeBBSCentralCharacterQuotient.quotientRoot (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)).lift = (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).iota.lift :=
  (TypeBBSCentralCharacterQuotient.quotientRoot_lift
    (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)).trans
      ((TypeBCriterionEmbeddedPairBinding.embeddedRoot_lift (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root).trans
        (quotientBrauer_root_lift S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).symm)

section Pair

variable (W : CharacterWeight 2 K (G F))
  (hUT : U (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) ≤ T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val))
  (blocks : PhysicalBlockFamily (k := k)
    (TypeBCentralKernelTripleCarriers.inside (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)))
    (TypeBCentralKernelTripleCarriers.inside (U (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W)) (T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val))))
  (quotientBlocks : PhysicalBlockFamily (k := k)
    (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W)))

/-- The actual quotient pair uses the common reference's prescribed root lift. -/
theorem pairRoot_lift :
    (TypeBBSCentralQuotientPairTransport.quotientData (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) blocks quotientBlocks).base.iota.lift = (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).iota.lift :=
  (TypeBBSCentralQuotientPairTransport.quotientTheta_quotientRoot_lift
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) blocks quotientBlocks).trans
      (embeddedQuotient_root_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi)

/-- The actual base comparison transports the common-reference root exactly. -/
theorem pairRoot_along :
    (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).iota.alongMulEquiv (referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi) =
      (TypeBBSCentralQuotientPairTransport.quotientData (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) blocks quotientBlocks).base.iota :=
  TypeBCentralKernelSpinFibreIdentification.root_eq_of_lift_eq _ _
    ((funext ((quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).iota.alongMulEquiv_lift (referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi))).trans
      (pairRoot_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi W hUT blocks quotientBlocks).symm)

/-- The pair's character is precisely the common-reference descent under the base comparison. -/
theorem pairTheta_character :
    (TypeBBSCentralQuotientPairTransport.quotientTheta (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) blocks quotientBlocks).val =
      PrimeRegularClassFunction.pullback (referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).symm.toMonoidHom
        (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val := by
  exact (TypeBBSCentralQuotientPairTransport.quotientTheta_quotientCharacter
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) blocks quotientBlocks).trans
      (congrArg
        (fun phi : PrimeRegularClassFunction K
            ((embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) ⧸ (TypeBBSCentralCharacterQuotient.centralKernel (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val))) 2 =>
          PrimeRegularClassFunction.pullback (TypeBBSCentralQuotientPairTransport.baseQuotientEquiv (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)).symm.toMonoidHom phi)
        (embeddedQuotient_character S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi))

/-- The same comparison identifies the irreducible characters at their actual roots. -/
theorem pairTheta_brauer :
    TypeBCentralKernelSpinFibreIdentification.brauerEquiv
        (referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi) (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).iota (TypeBBSCentralQuotientPairTransport.quotientData (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) blocks quotientBlocks).base.iota
        (pairRoot_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi W hUT blocks quotientBlocks)
        (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).brauer =
      TypeBBSCentralQuotientPairTransport.quotientTheta (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) blocks quotientBlocks := by
  apply Subtype.ext
  exact (TypeBCentralKernelSpinFibreIdentification.brauerEquiv_val
    (referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi) (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).iota (TypeBBSCentralQuotientPairTransport.quotientData (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration) blocks quotientBlocks).base.iota
    (pairRoot_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi W hUT blocks quotientBlocks) (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).brauer).trans
      (pairTheta_character S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi W hUT blocks quotientBlocks).symm

end Pair


/-- Attach the proved common-reference equations before specializing the raw weight. -/
theorem pairExistence_comparison
    (catalogues : TypeBEmbeddedPairClassWitness.CatalogueFamily
      (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (matrixNaturalAction F parameters N fieldSource C) root)
    (W : CharacterWeight 2 K (G F))
    (quotientBlocks : PhysicalBlockFamily (k := k) (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W)))
    (witnesses :
    letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K)
      (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    let Ghat := embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    let rootHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root
    let thetaHat := TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val
    let WHat := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W
    let calibrationHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration
    let centrelessHat := TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
    ∃ hUT : U Ghat WHat ≤ T Ghat rootHat thetaHat,
      Nonempty (TypeBCentralKernelPairSplittingBinding.PairWitness
        Msys Ghat rootHat calibrationHat thetaHat WHat hUT navarro
        (catalogues thetaHat WHat hUT)) ∧
      Nonempty (BlockTripleWitness
        (TypeBBSCentralQuotientPairTransport.quotientData
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks)
        (TypeBBSCentralQuotientPairTransport.quotientTheta
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks)
        (TypeBBSCentralQuotientPairTransport.quotientPhi
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks navarro))) :
    letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K)
      (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    let Ghat := embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    let rootHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root
    let thetaHat := TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val
    let WHat := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W
    let calibrationHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration
    let centrelessHat := TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
    ∃ hUT : U Ghat WHat ≤ T Ghat rootHat thetaHat,
      Nonempty (TypeBCentralKernelPairSplittingBinding.PairWitness
        Msys Ghat rootHat calibrationHat thetaHat WHat hUT navarro
        (catalogues thetaHat WHat hUT)) ∧
      Nonempty (BlockTripleWitness
        (TypeBBSCentralQuotientPairTransport.quotientData
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks)
        (TypeBBSCentralQuotientPairTransport.quotientTheta
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks)
        (TypeBBSCentralQuotientPairTransport.quotientPhi
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks navarro)) ∧
      (TypeBBSCentralQuotientPairTransport.quotientData
        Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
        (catalogues thetaHat WHat hUT) quotientBlocks).base.iota.lift =
          (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).iota.lift ∧
      (TypeBBSCentralQuotientPairTransport.quotientTheta
        Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
        (catalogues thetaHat WHat hUT) quotientBlocks).val =
          PrimeRegularClassFunction.pullback (referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).symm.toMonoidHom
            (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val := by
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K)
    (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  obtain ⟨hUT, originalWitness, quotientWitness⟩ := witnesses
  exact ⟨hUT, originalWitness, quotientWitness,
    pairRoot_lift S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi W hUT
      (catalogues (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT) quotientBlocks,
    pairTheta_character S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi W hUT
      (catalogues (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W) hUT) quotientBlocks⟩


section Selected

variable (rootH : PrimeRegularRootEmbedding 2 k K (H F))
  (rootHCalibration : RootResidueCompatible Msys rootH)
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  (guardH : GuardedBlockCompatibility rootH SH.operations)
  (notThree : Nat.card F ≠ 3)
  (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys)
  (catalogues : TypeBEmbeddedPairClassWitness.CatalogueFamily
    (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (matrixNaturalAction F parameters N fieldSource C) root)
  (butterfly : TypeBCentralKernelButterflyCertificate.ButterflyCertificate 2 k K)
  (delta : H F) (outside : delta ∉ G F)
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
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta
    (TypeBMatrixOmegaBSStructure.omega_index_two N parameters le_rfl C)
    outside parameters notThree Msys rootCalibration rootHCalibration guard guardH dgn)
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
  (naturalSurjective : Function.Surjective
    (TypeBAutomorphismSource.ambientAutomorphism fieldSource))
  [ambientRoots : HasEnoughRootsOfUnity K
    (Nat.card (TypeBMatrixAmbientOrdinaryRoots.MatrixAmbient parameters N fieldSource C))]
  (certificate : TypeBBSOnePairSplittingSource.Theorem46SplittingCertificate)
  (brauerSource : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
  (ordinarySource : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)],
      TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K X)
  (ordinary : ∀ Q : Subgroup (H F), NormalizerOrdinarySource Msys SH.operations Q)
  (membership : OrdinaryInflationMembership Msys SH.operations ordinary)
  (productFormula : BrauerLinearTensorProductFormula rootH)

include gggr fyz naturalSurjective ambientRoots certificate brauerSource ordinarySource
  ordinary membership productFormula in
/-- The selected pair and its complete quotient witness use the constructed common reference. -/
theorem selectedQuotient_comparison
    (quotientBlocks :
      let W := selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH) (f := f) (parameters := parameters)
  (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)
      PhysicalBlockFamily (k := k) (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W))) :
    letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K)
      (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    let W := selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH) (f := f) (parameters := parameters)
  (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts psi)
    let Ghat := embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
    let rootHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root
    let thetaHat := TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val
    let WHat := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) W
    let calibrationHat := TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root rootCalibration
    let centrelessHat := TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
    ∃ hUT : U Ghat WHat ≤ T Ghat rootHat thetaHat,
      Nonempty (TypeBCentralKernelPairSplittingBinding.PairWitness
        Msys Ghat rootHat calibrationHat thetaHat WHat hUT navarro
        (catalogues thetaHat WHat hUT)) ∧
      Nonempty (BlockTripleWitness
        (TypeBBSCentralQuotientPairTransport.quotientData
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks)
        (TypeBBSCentralQuotientPairTransport.quotientTheta
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks)
        (TypeBBSCentralQuotientPairTransport.quotientPhi
          Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
          (catalogues thetaHat WHat hUT) quotientBlocks navarro)) ∧
      (TypeBBSCentralQuotientPairTransport.quotientData
        Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
        (catalogues thetaHat WHat hUT) quotientBlocks).base.iota.lift =
          (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).iota.lift ∧
      (TypeBBSCentralQuotientPairTransport.quotientTheta
        Ghat rootHat thetaHat centrelessHat WHat hUT Msys calibrationHat
        (catalogues thetaHat WHat hUT) quotientBlocks).val =
          PrimeRegularClassFunction.pullback (referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).symm.toMonoidHom
            (quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val := by
  exact pairExistence_comparison S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi
    catalogues (selectedCharacterWeight S b (principalEquiv (S := S) (SH := SH) (f := f) (parameters := parameters)
      (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts psi)) quotientBlocks
    (TypeBRankThreePrincipalSelectedQuotient.selectedQuotient
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
      ordinarySource ordinary membership productFormula psi quotientBlocks)

end Selected

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientComparison


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
