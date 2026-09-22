import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientComparison
import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientLocalPackets
import ModularRep.PaperProofs.TypeBCentralKernelButterflyCharacterIdentification
import ModularRep.PaperProofs.CanonicalLocalBaseTransport

/-!
# The selected local character on the same reference quotient

The source pair and the reference packet reduce the same original ordinary
character. Their comparison uses the literal normalizer coordinates and the
residue convention of the original modular system.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyLocalCharacter

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCriterionHypotheses
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZCentrelessLocalPackets
open CyclicOuterLemma37LiteralLocalExtension
open TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalFieldMatchingSplitting TypeBCliffordOrthogonalAmbientQuotient
open TypeBGreenPrincipalConstituentSource TypeBLocalPhysicalBlockBinding
open TypeBRankThreePrincipalMatchedInertia TypeBRankThreePrincipalAmbientFieldMatching
open TypeBRankThreePrincipalBrauerOrbitBinding
open TypeBCentralKernelInertia TypeBOrthogonalOmegaCarriers
open EvenFieldFLZ318FixedTheoremGate
open TypeBCentralKernelTripleRootFamily TypeBCentralKernelTripleCertificate
open TypeBCentralKernelButterflyCertificate
open TypeBRankThreePrincipalFixedRootFamilyBinding
open TypeBRankThreePrincipalReferenceBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section PairCoordinates

variable {p : ℕ} {K O k A : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A]
  (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root)
  (centreless : Subgroup.center G = ⊥)
  (W : CharacterWeight p K G) (hUT : U G W ≤ T G root theta)

/-- The actual two carrier transports, with no choice of a local map. -/
def pairNormalizerEquiv :
    Subgroup.normalizer (W.subgroup : Set G) ≃*
      localBase (TypeBBSCentralQuotientPairTransport.quotientBase G root theta centreless)
        (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient G root theta centreless W) :=
  (TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT).trans
    (TypeBBSCentralQuotientPairTransport.localEquiv G root theta centreless W)

theorem pairNormalizerEquiv_projection
    (n : Subgroup.normalizer (W.subgroup : Set G)) :
    (pairNormalizerEquiv G root theta centreless W hUT n).val.val =
      QuotientGroup.mk'
        (TypeBBSCentralQuotientPairTransport.ambientKernel G root theta centreless)
        (TypeBBSCentralQuotientPairTransport.baseInclusion G root theta n.val) := rfl

variable (Msys : ModularSystem p K O k)
  (calibration : RootResidueCompatible Msys root)
  (blocks : PhysicalBlockFamily (k := k)
    (TypeBCentralKernelTripleCarriers.inside G (T G root theta))
    (TypeBCentralKernelTripleCarriers.inside (U G W) (T G root theta)))
  (quotientBlocks : PhysicalBlockFamily (k := k)
    (TypeBBSCentralQuotientPairTransport.quotientBase G root theta centreless)
    (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient G root theta centreless W))
  [HasEnoughRootsOfUnity K (Nat.card G)]
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding p k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The actual quotient-pair value is the original weight's ordinary value. -/
theorem pairNormalizerEquiv_value
    (x : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set G)) p) :
    (TypeBBSCentralQuotientPairTransport.quotientPhi
      G root theta centreless W hUT Msys calibration blocks quotientBlocks navarro).val
      (PrimeRegularElement.map
        (pairNormalizerEquiv G root theta centreless W hUT).toMonoidHom x) =
      W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup x.val) := by
  let e := TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT
  let eq := TypeBBSCentralQuotientPairTransport.localEquiv G root theta centreless W
  let y := PrimeRegularElement.map e.toMonoidHom x
  have reduction := TypeBCentralKernelPairSplittingBinding.localCharacter_reduction
    Msys G root calibration theta W hUT navarro blocks y
  have cancel : e.symm y.val = x.val := e.symm_apply_apply x.val
  rw [cancel] at reduction
  change (TypeBCentralKernelPairSplittingBinding.localCharacter
    Msys G root calibration theta W hUT navarro blocks).val
      (PrimeRegularElement.map eq.symm.toMonoidHom
        (PrimeRegularElement.map eq.toMonoidHom y)) = _
  have hy : PrimeRegularElement.map eq.symm.toMonoidHom
      (PrimeRegularElement.map eq.toMonoidHom y) = y := by
    apply Subtype.ext
    exact eq.symm_apply_apply y.val
  rw [hy]
  exact reduction.symm

end PairCoordinates

local instance omegaOrdinaryRoots (F K : Type) [Field F] [Finite F] [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (H F))] :
    HasEnoughRootsOfUnity K (Nat.card (G F)) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))

local instance embeddedRoots
    {F K : Type} [Field F] [Finite F] [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (H F))]
    {r f : ℕ} [CharP F r] [NeZero f]
    (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N) :
    HasEnoughRootsOfUnity K
      (Nat.card (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource))) :=
  TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K)
    (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)

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
  (calibration : RootResidueCompatible Msys root)
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (guard : GuardedBlockCompatibility root S.operations)
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  {r f : ℕ} [CharP F r] [NeZero f]
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
  (psi : Definition35Brauer
    (problem S SH literal literalH Msys root calibration navarro guard b))
  (w : Definition35Weight
    (problem S SH literal literalH Msys root calibration navarro guard b))

variable (hUT : U (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) ≤ T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val))

/-- The reference normalizer maps to the local base of the actual quotient pair. -/
def sourceLocalEquiv :
    Subgroup.normalizer ((quotientRadical (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w) : Set (CentralCharacterQuotient (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb))) ≃*
      localBase (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w))) :=
  ((ModularRep.normalizerEquiv (TypeBRankThreePrincipalQuotientLocalPackets.quotientMapEquiv S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb) (SelectedRadical S b w)).symm.trans (ModularRep.normalizerEquiv (TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (SelectedRadical S b w))).trans (pairNormalizerEquiv (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT)

/-- The local equivalence covers the previously fixed base comparison. -/
theorem sourceLocalEquiv_base
    (n : Subgroup.normalizer ((quotientRadical (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w) : Set (CentralCharacterQuotient (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb)))) :
    localToBase (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w))) ((sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT) n) = (TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi) n.val := by
  let n0 := (ModularRep.normalizerEquiv (TypeBRankThreePrincipalQuotientLocalPackets.quotientMapEquiv S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb) (SelectedRadical S b w)).symm n
  have hn : centralCharacterQuotientMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) n0.val = n.val :=
    congrArg Subtype.val ((ModularRep.normalizerEquiv (TypeBRankThreePrincipalQuotientLocalPackets.quotientMapEquiv S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb) (SelectedRadical S b w)).apply_symm_apply n)
  have hproj := pairNormalizerEquiv_projection
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT ((ModularRep.normalizerEquiv (TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (SelectedRadical S b w)) n0)
  have hp := TypeBRankThreePrincipalQuotientComparison.referenceToPairBase_projection
    S SH literal literalH Msys root calibration navarro guard b hb
    parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
    simple nonabelian psi n0.val
  have hc := congrArg
    (fun z : (CentralCharacterQuotient (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb)) => ((TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi) z).val) hn
  apply Subtype.ext
  exact hproj.trans (hp.symm.trans hc)

variable
  (blocks : PhysicalBlockFamily (k := k)
    (TypeBCentralKernelTripleCarriers.inside (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)))
    (TypeBCentralKernelTripleCarriers.inside (U (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)))
      (T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val))))
  (quotientBlocks : PhysicalBlockFamily (k := k) (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w))))

/-- Both Brauer values are computed from the same original ordinary character. -/
theorem sourcePhi_pullback :
    PrimeRegularClassFunction.pullback (sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT).toMonoidHom (TypeBBSCentralQuotientPairTransport.quotientPhi (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks navarro).val =
      (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).brauer.val := by
  letI := TypeBCriterionEmbeddedPairBinding.embeddedOrdinaryRoots (K := K)
    (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)
  ext x
  let nRef := ModularRep.normalizerEquiv (TypeBRankThreePrincipalQuotientLocalPackets.quotientMapEquiv S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb) (SelectedRadical S b w)
  let nEmb := ModularRep.normalizerEquiv (TypeBCriterionEmbeddedPairBinding.baseEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (SelectedRadical S b w)
  let x0 := PrimeRegularElement.map nRef.symm.toMonoidHom x
  let xh := PrimeRegularElement.map nEmb.toMonoidHom x0
  have hp := pairNormalizerEquiv_value
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT
    Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks navarro xh
  have he := TypeBCriterionEmbeddedPairBinding.rawWeightEquiv_localCharacter
    (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w) x0.val xh.val rfl
  have ho := (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).ordinaryDescends
    (TypeBCentralKernelWeightTransport.localMk (SelectedRadical S b w) x0.val)
  have hs :
      quotientNormalizerMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w
        (TypeBCentralKernelWeightTransport.localMk (SelectedRadical S b w) x0.val) =
      quotientLocalInflationMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w x.val := by
    change quotientLocalInflationMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w
      (nRef x0.val) = quotientLocalInflationMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w x.val
    rw [show nRef x0.val = x.val from nRef.apply_symm_apply x.val]
  rw [hs] at ho
  have hr := (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).reduction
    (PrimeRegularElement.map (quotientLocalInflationMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w) x)
  have hi := congrArg
    (fun f : PrimeRegularClassFunction K
      (Subgroup.normalizer ((quotientRadical (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w) : Set (CentralCharacterQuotient (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb)))) 2 => f x)
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).inflation
  exact hp.trans (he.trans (ho.symm.trans (hr.trans hi)))

/-- The two local roots agree on their actual common carrier. -/
theorem sourceLocalRoot_along :
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota.alongMulEquiv (sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT) = (TypeBBSCentralQuotientPairTransport.quotientData (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks).localData.iota := by
  have hi : RootResidueCompatible Msys (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota :=
    TypeBModularGroupRootBinding.groupRoot_residue Msys _
  have hs := TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
    Msys (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota hi (sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT)
  have ht := TypeBBSCentralQuotientPairTransport.quotientData_local_residue
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT
    Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks
  exact (TypeBModularGroupRootBinding.eq_groupRoot_of_residue Msys _ _ hs).trans
    (TypeBModularGroupRootBinding.eq_groupRoot_of_residue Msys _ _ ht).symm

/-- Full lift equality follows from the proved root identity on the local carrier. -/
theorem sourceLocalRoot_lift :
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota.lift = (TypeBBSCentralQuotientPairTransport.quotientData (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks).localData.iota.lift := by
  have h := congrArg
    (fun iota : PrimeRegularRootEmbedding 2 k K (localBase (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)))) => iota.lift)
    (sourceLocalRoot_along S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT blocks quotientBlocks)
  exact (funext ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota.alongMulEquiv_lift (sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT))).symm.trans h


variable (ambient : SpathAmbientGroup (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) psi (quotientBrauer S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi))

/-- The target is the local base in this same supplied ambient group. -/
def honestLocalEquiv : localBase (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w))) ≃* (AmbientLocalBase (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) psi w (quotientBrauer S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) :=
  (sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT).symm.trans (canonicalLocalBaseEquiv (w := w) ambient)

theorem honestLocalEquiv_apply_source
    (n : Subgroup.normalizer ((quotientRadical (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w) : Set (CentralCharacterQuotient (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb)))) :
    (honestLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT ambient) ((sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT) n) = (canonicalLocalBaseEquiv (w := w) ambient) n := by
  change (canonicalLocalBaseEquiv (w := w) ambient) ((sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT).symm ((sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT) n)) = _
  rw [MulEquiv.symm_apply_apply]

/-- Its local-to-base square uses exactly the existing base comparison. -/
theorem honestLocalEquiv_base (x : localBase (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)))) :
    localToBase ambient.base (AmbientLocalGroup (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) psi w (quotientBrauer S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) ((honestLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT ambient) x) =
      ((TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).symm.trans ambient.baseEquiv)
        (localToBase (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w))) x) := by
  let e := sourceLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT
  let c := TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi
  let l1 : localBase (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w))) →* (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) := localToBase (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)))
  let l2 : (AmbientLocalBase (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) psi w (quotientBrauer S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) →* ambient.base := localToBase ambient.base (AmbientLocalGroup (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) psi w (quotientBrauer S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient)
  let n := e.symm x
  have hn : e n = x := e.apply_symm_apply x
  have hs : l1 (e n) = c n.val :=
    sourceLocalEquiv_base S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT n
  have hb : l1 x = c n.val := (congrArg l1 hn).symm.trans hs
  have ht : l2 ((canonicalLocalBaseEquiv (w := w) ambient) n) = ambient.baseEquiv n.val := by
    apply Subtype.ext
    exact canonicalLocalBaseEquiv_natural ambient n
  have hc : n.val = c.symm (l1 x) :=
    (c.symm_apply_apply n.val).symm.trans (congrArg c.symm hb.symm)
  change l2 ((canonicalLocalBaseEquiv (w := w) ambient) n) = ambient.baseEquiv (c.symm (l1 x))
  exact ht.trans (congrArg ambient.baseEquiv hc)

/-- All carrier guards are derived for the local base in the prescribed ambient. -/
def honestLocalIdentification :
    LocalIdentification (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) ambient.base
      ((TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi).symm.trans ambient.baseEquiv) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w))) (AmbientLocalGroup (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) psi w (quotientBrauer S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) where
  equiv := honestLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT ambient
  base_value := honestLocalEquiv_base S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT ambient

/-- The prescribed transported inflation agrees with the actual source character. -/
theorem honestLocal_character :
    (IrreducibleBrauerCharacter.equivAlongMulEquiv (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota (canonicalLocalBaseEquiv (w := w) ambient) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).brauer).val =
      PrimeRegularClassFunction.pullback (honestLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT ambient).symm.toMonoidHom (TypeBBSCentralQuotientPairTransport.quotientPhi (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks navarro).val := by
  ext y
  have hv := congrArg
    (fun f : PrimeRegularClassFunction K
      (Subgroup.normalizer ((quotientRadical (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) w) : Set (CentralCharacterQuotient (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb)))) 2 =>
        f (PrimeRegularElement.map (canonicalLocalBaseEquiv (w := w) ambient).symm.toMonoidHom y))
    (sourcePhi_pullback S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT blocks quotientBlocks)
  exact hv.symm

/-- The target specified catalogue selects the transported source block. -/
theorem localCharacterIdentification
    (localBlocks : PhysicalBlocks k (AmbientLocalBase (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) psi w (quotientBrauer S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient)) :
    CharacterIdentification (honestLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT ambient) (TypeBBSCentralQuotientPairTransport.quotientData (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks).localData
      (TypeBCentralKernelTripleRootFamily.characterData ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota.alongMulEquiv (canonicalLocalBaseEquiv (w := w) ambient)) localBlocks) (TypeBBSCentralQuotientPairTransport.quotientPhi (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks navarro) (IrreducibleBrauerCharacter.equivAlongMulEquiv (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota (canonicalLocalBaseEquiv (w := w) ambient) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).brauer) := by
  apply TypeBCentralKernelButterflyCharacterIdentification.of_lift_eq
    (honestLocalEquiv S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT ambient) (TypeBBSCentralQuotientPairTransport.quotientData (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks).localData (TypeBCentralKernelTripleRootFamily.characterData ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota.alongMulEquiv (canonicalLocalBaseEquiv (w := w) ambient)) localBlocks) (TypeBBSCentralQuotientPairTransport.quotientPhi (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (selectedCharacterWeight S b w)) hUT Msys (TypeBCriterionEmbeddedPairBinding.embeddedRoot_residue (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) Msys root calibration) blocks quotientBlocks navarro) (IrreducibleBrauerCharacter.equivAlongMulEquiv (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota (canonicalLocalBaseEquiv (w := w) ambient) (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).brauer)
  · exact (funext ((TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root calibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb w).iota.alongMulEquiv_lift (canonicalLocalBaseEquiv (w := w) ambient))).trans
      (sourceLocalRoot_lift S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT blocks quotientBlocks)
  · exact honestLocal_character S SH literal literalH Msys root calibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi w hUT blocks quotientBlocks ambient

end ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyLocalCharacter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
