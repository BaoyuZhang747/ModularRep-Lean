import ModularRep.PaperProofs.TypeBRankThreePrincipalMatchedPacket
import ModularRep.PaperProofs.TypeBRankThreePrincipalRelativeBrauerBinding
import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBlockAutomorphism
import ModularRep.PaperProofs.TypeBRankThreePrincipalHonestNormalizerBinding

/-!
# The complete actual principal block witness

The same selected matched tails retain their canonical quotient packets and
finite root agreements. The existing complete quotient fibres supply the
weight range and the invariant correspondence graph.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalFullBlockAssembly

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

variable
  (quotientBlockProvider : ∀ psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b),
    PhysicalBlockFamily (k := k) (TypeBBSCentralQuotientPairTransport.quotientBase
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

  (targetBlockProvider : ∀ (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b)),
    ∀ ambient : SpathAmbientGroup
    (TypeBRankThreePrincipalReferenceBinding.problem
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference
    (F := F) (K := K) (O := O) (k := k)
    S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (TypeBRankThreePrincipalReferenceBinding.quotientBrauer
    (F := F) (K := K) (O := O) (k := k) (r := r) (f := f)
    S SH literal literalH Msys root rootCalibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi),
    PhysicalBlockFamily (k := k) ambient.base
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
  (ksCertificate : TypeBKoshitaniSpathHonestAmbientSource.ModularExistenceCertificate)
  (localCertificate :
    TypeBSpathHonestLocalExtensionSource.HonestLocalExtensionCertificate 2 k K)


open TypeBFullBlockCondition TypeBModularGroupRootBinding
open EvenFieldFLZQuotientBlockFibre

include S SH root rootH b hb bH hbH literal literalH parameters N fieldSource C
  Msys rootCalibration rootHCalibration guard guardH notThree dgn delta outside
  catalogues navarro butterfly roots fieldScope green principalLift clifford
  principalRestriction covering counts gggr fyz ambientRoots certificate
  centreSpin fullCover centreClifford naturalKernel naturalSurjective simple nonabelian
  brauerSource ordinarySource ordinary membership productFormula
  quotientBlockProvider targetBlockProvider ksCertificate localCertificate in
/-- The actual rank-three principal sources supply all eighteen block clauses. -/
theorem exists_full_principal_block_witness :
    Nonempty (BlockWitness
      (TypeBRankThreePrincipalFixedRootFamilyBinding.family
        S SH literal literalH Msys root rootCalibration navarro guard)
      (TypeBRankThreePrincipalReferenceBinding.cover
        S SH literal literalH Msys root rootCalibration navarro guard
        parameters N C centreSpin fullCover simple nonabelian) b) := by
  classical
  let P := TypeBRankThreePrincipalReferenceBinding.problem
    S SH literal literalH Msys root rootCalibration navarro guard b
  let reference : Definition35Brauer P :=
    TypeBRankThreePrincipalReferenceBinding.reference
      S SH literal literalH Msys root rootCalibration navarro guard b hb
  let principal := TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts
  let selected (psi : Definition35Brauer P) :=
    Classical.indefiniteDescription _
      (TypeBRankThreePrincipalMatchedPacket.exists_matched_tail_with_roots
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
        (quotientBlocks := quotientBlockProvider psi)
        (targetBlockProvider := targetBlockProvider psi)
        (ksCertificate := ksCertificate)
        (localCertificate := localCertificate))
  let tails (psi : Definition35Brauer P) := (selected psi).val
  let relative := TypeBRankThreePrincipalRelativeBlockBinding.relative
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails
  let fixedRoots := TypeBRankThreePrincipalRelativeBrauerBinding.fixedRoots
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails
  let quotientRoot := TypeBRankThreePrincipalQuotientBrauerFibre.quotientRoot
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  let quotientEquiv := TypeBRankThreePrincipalQuotientBrauerFibre.quotientEquiv
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  letI := TypeBRankThreePrincipalQuotientBrauerFibre.physicalBlockFintype S
  letI quotientBlockAction :=
    OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) quotientEquiv
  let quotientSource := TypeBRankThreePrincipalQuotientWeightFibre.quotientSource
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  let weightEquiv := TypeBRankThreePrincipalQuotientMatching.weightEquiv
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  let brauerEquiv := TypeBRankThreePrincipalQuotientBrauerFibre.fibreEquiv
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
  let completeWeight := principal.trans weightEquiv
  have weightClass (psi : Definition35Brauer P) :
      quotientWeightClass relative psi = (completeWeight psi).val := by
    let rawOf (packet : QuotientWeightBrauerSource P reference (principal psi)) :
        CharacterWeight 2 K (CentralCharacterQuotient P reference) := {
      prime := root.prime
      subgroup := quotientRadical P reference (principal psi)
      radical := packet.radical
      localCharacter := packet.ordinary
      defectZero := packet.defectZero }
    have packetEquality := congrArg rawOf (selected psi).property.1
    change quotientRawWeight relative psi =
      TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight
        (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts
        centreSpin fullCover simple nonabelian psi at packetEquality
    exact (congrArg TypeBCentralKernelInertia.classOf packetEquality).trans
      (TypeBRankThreePrincipalHonestNormalizerBinding.matchedRaw_class
        (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts
        centreSpin fullCover simple nonabelian psi)
  have descendedBrauer (psi : Definition35Brauer P) :
      fixedDescendedBrauer relative fixedRoots psi = (brauerEquiv psi).val :=
    TypeBRankThreePrincipalRelativeBrauerBinding.fixedDescendedBrauer_eq_quotientBrauer
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails psi
  refine ⟨{
    relative := relative
    roots := fixedRoots
    brauerReverse := TypeBRankThreePrincipalRelativeBrauerBinding.brauerReverse
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails
    quotientBlockAction := quotientBlockAction
    quotientBlockSource := quotientSource
    quotientBlockIdempotent := ?_
    quotientBlockCompatibility :=
      TypeBRankThreePrincipalQuotientWeightFibre.quotientSource_guard
        S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb
    quotientRoots_agree := TypeBRankThreePrincipalRelativeBrauerBinding.quotientRoots_agree
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts gggr fyz centreSpin fullCover naturalSurjective
      simple nonabelian tails
    quotientWeight_roots := ?_
    quotientInflation_roots := ?_
    quotientAmbient_roots := ?_
    localAmbient_roots := ?_
    intermediate_roots := ?_
    quotientBrauerBlock_transport := ?_
    weight_liesInQuotientBlock := ?_
    weight_injective := ?_
    weight_reverse := ?_
    quotient_equivariant := ?_ }⟩
  · intro c
    exact TypeBRankThreePrincipalQuotientWeightFibre.quotientOperations_idempotent
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb c
  · intro psi
    have rootEquality := congrArg
      (fun packet : QuotientWeightBrauerSource P reference (principal psi) => packet.iota)
      (selected psi).property.1
    change QuotientRootAgreement quotientRoot
      (quotientRadical P reference (principal psi)) (tails psi).weight.iota
    rw [rootEquality]
    exact TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight_rootAgreement
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (principal psi)
  · intro psi
    let canonicalWeight := TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (principal psi)
    let canonicalInflation := TypeBRankThreePrincipalQuotientLocalPackets.localInflation
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (principal psi)
    have inflationRootEquality :
        ∀ (packet : QuotientWeightBrauerSource P reference (principal psi))
          (inflation : QuotientLocalInflationSource P reference (principal psi) packet),
          packet = canonicalWeight → HEq inflation canonicalInflation →
            inflation.iota = canonicalInflation.iota := by
      intro packet inflation packetEquality inflationEquality
      subst packet
      exact congrArg
        (fun value : QuotientLocalInflationSource P reference (principal psi)
          canonicalWeight => value.iota)
        (eq_of_heq inflationEquality)
    have rootEquality := inflationRootEquality
      (tails psi).weight (tails psi).localInflation
      (selected psi).property.1 (selected psi).property.2.1
    change NormalizerRootAgreement quotientRoot
      (quotientRadical P reference (principal psi)) (tails psi).localInflation.iota
    rw [rootEquality]
    exact TypeBRankThreePrincipalQuotientLocalPackets.localInflation_rootAgreement
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (principal psi)
  · intro psi
    exact (selected psi).property.2.2.2.1
  · intro psi
    exact (selected psi).property.2.2.2.2.1
  · intro psi J hJ
    exact (selected psi).property.2.2.2.2.2 J hJ
  · intro alpha phi
    exact TypeBRankThreePrincipalQuotientBlockAutomorphism.quotientBrauerBlock_transport
      S SH literal literalH Msys root rootCalibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb alpha phi
  · intro psi
    rw [weightClass psi]
    exact (completeWeight psi).property
  · intro psi chi equality
    apply completeWeight.injective
    apply Subtype.ext
    exact (weightClass psi).symm.trans (equality.trans (weightClass chi))
  · intro w
    exact ⟨completeWeight.symm w, (weightClass (completeWeight.symm w)).trans
      (congrArg Subtype.val (completeWeight.apply_symm_apply w))⟩
  · intro alpha psi chi characterEquality
    have originalGraph : TypeBRankThreePrincipalQuotientMatching.Graph
        (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts
        centreSpin fullCover simple nonabelian
        (brauerEquiv psi).val (quotientWeightClass relative psi) := by
      refine ⟨brauerEquiv psi, rfl, ?_⟩
      exact (congrArg Subtype.val
        (TypeBRankThreePrincipalQuotientMatching.matching_on_original
          (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts
          centreSpin fullCover simple nonabelian psi)).trans (weightClass psi).symm
    have translatedGraph :=
      (TypeBRankThreePrincipalQuotientMatching.graph_opAut
        (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective)
        (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts
        centreSpin fullCover simple nonabelian alpha
        (brauerEquiv psi).val (quotientWeightClass relative psi)).mpr originalGraph
    rw [descendedBrauer chi, descendedBrauer psi] at characterEquality
    obtain ⟨quotientCharacter, quotientCharacterEquality, quotientWeightEquality⟩ :=
      translatedGraph
    have quotientCharacter_eq : quotientCharacter = brauerEquiv chi :=
      Subtype.ext (quotientCharacterEquality.trans characterEquality.symm)
    subst quotientCharacter
    exact (weightClass chi).trans
      ((congrArg Subtype.val
        (TypeBRankThreePrincipalQuotientMatching.matching_on_original
          (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts
          centreSpin fullCover simple nonabelian chi)).symm.trans quotientWeightEquality)

end Selected

end ModularRep.PaperProofs.TypeBRankThreePrincipalFullBlockAssembly



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
