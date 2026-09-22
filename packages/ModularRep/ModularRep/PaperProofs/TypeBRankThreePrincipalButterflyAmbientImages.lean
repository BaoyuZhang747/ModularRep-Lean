import ModularRep.PaperProofs.TypeBRankThreePrincipalHonestNormalizerBinding
import ModularRep.PaperProofs.TypeBCentralKernelButterflyLocalIdentification
import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientInertiaImages

/-!
# Conjugation images in the same principal Späth ambient

The prescribed base maps identify the two conjugation images. The Butterfly
local preimage is the raw stabilizer, hence the full normalizer of the same
selected radical in the already chosen ambient group.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyAmbientImages

open ModularRep CharacterWeight
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily TypeBCentralKernelInertia
open TypeBCentralKernelButterflyCertificate

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section Ambient

variable {P : Definition35Problem} {reference psi : Definition35Brauer P}
  {quotient : CentralQuotientBrauerSource P reference psi}
  (ambient : SpathAmbientGroup P reference psi quotient)

/-- The actual ambient action has the full positive Brauer stabilizer as image. -/
theorem ambientAction_range :
    ambient.conjugation.range =
      brauerStabilizer (MonoidHom.id (MulAut (CentralCharacterQuotient P reference)))
        quotient.iota quotient.brauer := by
  apply le_antisymm
  · rintro alpha ⟨a, rfl⟩
    rw [mem_brauerStabilizer]
    have fixed := TypeBRankThreePrincipalHonestNormalizerBinding.ambientBrauer_fixed
      ambient a
    change IrreducibleBrauerCharacter.twist quotient.iota quotient.brauer
      (ambient.conjugation a⁻¹) = quotient.brauer at fixed
    simpa only [MonoidHom.id_apply, map_inv] using fixed
  · intro alpha fixed
    let actor : QuotientBrauerAutomorphismStabilizer P reference psi quotient :=
      ⟨MulOpposite.op alpha⁻¹, by
        change IrreducibleBrauerCharacter.twist quotient.iota quotient.brauer
          alpha⁻¹ = quotient.brauer
        exact (mem_brauerStabilizer _ _ _ _).mp fixed⟩
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center ambient.A)
      (ambient.automorphismQuotientEquiv.symm actor)
    have value : ambient.automorphismQuotientEquiv
        (QuotientGroup.mk' (Subgroup.center ambient.A) a) = actor := by
      rw [ha, ambient.automorphismQuotientEquiv.apply_symm_apply]
    have opposite := congrArg Subtype.val value
    rw [ambient.automorphismQuotientEquiv_natural] at opposite
    have inverseValue := congrArg MulOpposite.unop opposite
    change ambient.conjugation a⁻¹ = alpha⁻¹ at inverseValue
    refine ⟨a, ?_⟩
    have value := congrArg (fun x : MulAut (CentralCharacterQuotient P reference) =>
      x⁻¹) inverseValue
    simpa only [map_inv, inv_inv] using value

variable {T1 : Type} [Group T1] (N1 : Subgroup T1) [N1.Normal]
  (c : CentralCharacterQuotient P reference ≃* N1)

/-- The base equivalence is forced by the reference coordinates and this ambient. -/
def referenceBaseEquiv : N1 ≃* ambient.base := c.symm.trans ambient.baseEquiv

/-- Conjugation on the first base, expressed on the common reference quotient. -/
def normalizedFirstAction : T1 →* MulAut (CentralCharacterQuotient P reference) :=
  (MulAut.congr c).symm.toMonoidHom.comp (firstAction N1)

/-- The second literal conjugation becomes the given action of the same ambient. -/
theorem secondAction_reference (a : ambient.A) :
    (MulAut.congr c).symm
      (secondAction N1 ambient.base (referenceBaseEquiv ambient N1 c) a) =
        ambient.conjugation a := by
  apply MulEquiv.ext
  intro h
  apply ambient.baseEquiv.injective
  apply Subtype.ext
  change (ambient.baseEquiv
      (c.symm (secondAction N1 ambient.base (referenceBaseEquiv ambient N1 c) a
        (c h))) : ambient.A) = (ambient.baseEquiv (ambient.conjugation a h) : ambient.A)
  calc
    _ = a * (ambient.baseEquiv h : ambient.A) * a⁻¹ := by
      have value := congrArg Subtype.val
        (secondAction_value N1 ambient.base (referenceBaseEquiv ambient N1 c) a (c h))
      simpa only [referenceBaseEquiv, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] using value
    _ = _ := (ambient.conjugation_on_base a h).symm

/-- Equal normalized images give the exact Butterfly conjugation-image guard. -/
theorem sameConjugationImage_of_reference_range
    (firstRange : (normalizedFirstAction N1 c).range =
      brauerStabilizer (MonoidHom.id (MulAut (CentralCharacterQuotient P reference)))
        quotient.iota quotient.brauer) :
    SameConjugationImage N1 ambient.base (referenceBaseEquiv ambient N1 c) := by
  apply le_antisymm
  · rintro alpha ⟨t, rfl⟩
    have member : normalizedFirstAction N1 c t ∈
        (normalizedFirstAction N1 c).range := ⟨t, rfl⟩
    rw [firstRange, ← ambientAction_range ambient] at member
    rcases member with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (MulAut.congr c).symm.injective
    exact (secondAction_reference ambient N1 c a).trans ha
  · rintro alpha ⟨a, rfl⟩
    have member : ambient.conjugation a ∈ ambient.conjugation.range := ⟨a, rfl⟩
    rw [ambientAction_range ambient, ← firstRange] at member
    rcases member with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply (MulAut.congr c).symm.injective
    exact ht.trans (secondAction_reference ambient N1 c a).symm

/-- The full prescribed local preimage is exactly the actual raw stabilizer. -/
theorem secondLocalAmbient_eq_rawStabilizer (U1 : Subgroup T1)
    (W : CharacterWeight P.p P.K (CentralCharacterQuotient P reference))
    (localImage : U1.map (normalizedFirstAction N1 c) =
      rawStabilizer (MonoidHom.id (MulAut (CentralCharacterQuotient P reference))) W) :
    secondLocalAmbient N1 ambient.base (referenceBaseEquiv ambient N1 c) U1 =
      rawStabilizer ambient.conjugation W := by
  ext a
  have membership :
      a ∈ secondLocalAmbient N1 ambient.base (referenceBaseEquiv ambient N1 c) U1 ↔
        ambient.conjugation a ∈ U1.map (normalizedFirstAction N1 c) := by
    rw [mem_secondLocalAmbient, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, value⟩
      exact ⟨t, ht, (congrArg (MulAut.congr c).symm value).trans
        (secondAction_reference ambient N1 c a)⟩
    · rintro ⟨t, ht, value⟩
      exact ⟨t, ht, (MulAut.congr c).symm.injective
        (value.trans (secondAction_reference ambient N1 c a).symm)⟩
  rw [membership, localImage, mem_rawStabilizer, mem_rawStabilizer]
  simp only [MonoidHom.id_apply, map_inv]

end Ambient

section Normalizer

variable {p : ℕ} {K H A : Type} [Field K] [CharZero K]
  [Group H] [Fintype H] [Group A]
  (X : Subgroup A) (e : H ≃* X) (rho : A →* MulAut H)
  (conjugation : ∀ (a : A) (h : H),
    X.subtype.comp e.toMonoidHom (rho a h) =
      a * X.subtype.comp e.toMonoidHom h * a⁻¹)

include conjugation in
/-- A fixed raw weight forces normalization of its literal embedded radical. -/
theorem rawStabilizer_le_embeddedNormalizer (W : CharacterWeight p K H) :
    rawStabilizer rho W ≤
      Subgroup.normalizer (W.subgroup.map (X.subtype.comp e.toMonoidHom) : Set A) := by
  intro a ha
  have fixed := (mem_rawStabilizer rho W a).mp ha
  have stable := congrArg CharacterWeight.subgroup fixed
  have mapped : W.subgroup.map (rho a).toMonoidHom = W.subgroup := by
    calc
      _ = W.subgroup.comap ((rho a)⁻¹).toMonoidHom :=
        Subgroup.map_equiv_eq_comap_symm (rho a) W.subgroup
      _ = W.subgroup := by
        simpa only [CharacterWeight.rightTwist_subgroup, map_inv] using stable
  have square : (X.subtype.comp e.toMonoidHom).comp (rho a).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (X.subtype.comp e.toMonoidHom) := by
    apply MonoidHom.ext
    exact conjugation a
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  calc
    _ = W.subgroup.map ((MulAut.conj a).toMonoidHom.comp
        (X.subtype.comp e.toMonoidHom)) := Subgroup.map_map _ _ _
    _ = W.subgroup.map ((X.subtype.comp e.toMonoidHom).comp
        (rho a).toMonoidHom) := congrArg W.subgroup.map square.symm
    _ = (W.subgroup.map (rho a).toMonoidHom).map
        (X.subtype.comp e.toMonoidHom) := (Subgroup.map_map _ _ _).symm
    _ = _ := congrArg (fun Q : Subgroup H => Q.map
        (X.subtype.comp e.toMonoidHom)) mapped

end Normalizer

open FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCriterionHypotheses TypeBCliffordCarriers TypeBCentralKernelBlockSource
open EvenFieldFLZSourceConditions
open CyclicOuterLemma37Concrete CyclicOuterLemma37ActualBlockFibres
open TypeBRankThreePrincipalFieldMatchingSplitting TypeBCliffordOrthogonalAmbientQuotient
open TypeBGreenPrincipalConstituentSource TypeBLocalPhysicalBlockBinding
open TypeBRankThreePrincipalMatchedInertia TypeBRankThreePrincipalAmbientFieldMatching
open TypeBRankThreePrincipalBrauerOrbitBinding TypeBOrthogonalOmegaCarriers
open EvenFieldFLZ318FixedTheoremGate

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
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (Omega 3 F))
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


variable (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b))


variable (ambient : SpathAmbientGroup (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (TypeBRankThreePrincipalReferenceBinding.quotientBrauer (F := F) (K := K) (O := O) (k := k) (r := r) (f := f) S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi))

include S SH literal literalH Msys root rootCalibration navarro guard b hb
  parameters N fieldSource C catalogues butterfly roots fieldScope green principalLift
  clifford principalRestriction covering counts centreSpin fullCover simple nonabelian
  gggr fyz naturalSurjective psi ambient in
/-- The actual matching supplies raw fixation on the full radical normalizer. -/
theorem matched_rawStabilizer_eq_normalizer :
    @Eq (Subgroup ambient.A)
      (rawStabilizer (p := 2) (K := K) (H := (CentralCharacterQuotient (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb))) (A := ambient.A)
        ambient.conjugation (TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi))
      (AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (TypeBRankThreePrincipalHonestNormalizerBinding.matchedWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer (F := F) (K := K) (O := O) (k := k) (r := r) (f := f) S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) := by
  apply le_antisymm
  · exact rawStabilizer_le_embeddedNormalizer
      (p := 2) (K := K) (H := (CentralCharacterQuotient (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb))) (A := ambient.A)
      ambient.base ambient.baseEquiv
      ambient.conjugation ambient.conjugation_on_base (TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi)
  · intro a ha
    apply (mem_rawStabilizer (p := 2) (K := K) (H := (CentralCharacterQuotient (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb))) (A := ambient.A)
      ambient.conjugation (TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) a).mpr
    have fixed : ((TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi)).rightTwist (ambient.conjugation a)⁻¹ = (TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) :=
      TypeBRankThreePrincipalHonestNormalizerBinding.normalizer_raw_fixed
      (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective)
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts centreSpin fullCover simple nonabelian
      psi ambient ⟨a, ha⟩
    simpa only [map_inv] using fixed

variable
  (centreClifford : TypeBCliffordCentreSource.CentreSource 3 F parameters (by decide))
  (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism fieldSource).ker =
    TypeBAutomorphismSource.embeddedCenter fieldSource)

local instance selectedEmbeddedNormal :
    (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)).Normal :=
  TypeBLocalOrdinaryGeometry.embeddedG_normal (G F)
    (soFieldAction 3 F parameters le_rfl N C fieldSource)
    (matrixNaturalAction F parameters N fieldSource C)


include S SH literal literalH Msys root rootCalibration navarro guard b hb
  parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
  simple nonabelian naturalSurjective psi ambient in
/-- The actual selected quotient and the same chosen ambient induce the same automorphisms. -/
theorem selected_sameConjugationImage :
    SameConjugationImage (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) ambient.base
      (((TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi)).symm.trans ambient.baseEquiv) := by
  have firstRange :
      (normalizedFirstAction (P := (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b)) (reference := (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb)) (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi)).range =
        brauerStabilizer (MonoidHom.id (MulAut (CentralCharacterQuotient (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb)))) ((TypeBRankThreePrincipalReferenceBinding.quotientBrauer (F := F) (K := K) (O := O) (k := k) (r := r) (f := f) S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi)).iota ((TypeBRankThreePrincipalReferenceBinding.quotientBrauer (F := F) (K := K) (O := O) (k := k) (r := r) (f := f) S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi)).brauer :=
    TypeBRankThreePrincipalQuotientInertiaImages.referenceAction_range
      S SH literal literalH Msys root rootCalibration navarro guard b hb
      parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
      simple nonabelian psi naturalSurjective
  exact sameConjugationImage_of_reference_range
    (P := (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b)) (reference := (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb)) (psi := psi) (quotient := (TypeBRankThreePrincipalReferenceBinding.quotientBrauer (F := F) (K := K) (O := O) (k := k) (r := r) (f := f) S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi))
    ambient (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi) firstRange

include S SH literal literalH Msys root rootCalibration navarro guard b hb
  parameters N fieldSource C catalogues butterfly roots fieldScope green principalLift
  clifford principalRestriction covering counts centreSpin fullCover centreClifford
  naturalKernel simple nonabelian gggr fyz naturalSurjective psi ambient in
/-- The selected quotient's prescribed Butterfly preimage is the full normalizer
in this same ambient. The inclusion is the one returned with the selected pair. -/
theorem selected_secondLocalAmbient_eq_normalizer
    (hUT : U (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (CyclicOuterLemma37LiteralLocalExtension.selectedCharacterWeight S b (TypeBRankThreePrincipalHonestNormalizerBinding.matchedWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts psi))) ≤ T (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val)) :
    secondLocalAmbient (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) ambient.base
        (((TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi)).symm.trans ambient.baseEquiv) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (CyclicOuterLemma37LiteralLocalExtension.selectedCharacterWeight S b (TypeBRankThreePrincipalHonestNormalizerBinding.matchedWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts psi)))) =
      AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (TypeBRankThreePrincipalHonestNormalizerBinding.matchedWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer (F := F) (K := K) (O := O) (k := k) (r := r) (f := f) S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient := by
  have localImage :
      ((TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (CyclicOuterLemma37LiteralLocalExtension.selectedCharacterWeight S b (TypeBRankThreePrincipalHonestNormalizerBinding.matchedWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts psi))))).map (normalizedFirstAction (P := (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b)) (reference := (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb)) (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi)) =
        rawStabilizer (p := 2) (K := K) (H := (CentralCharacterQuotient (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb)))
          (MonoidHom.id (MulAut (CentralCharacterQuotient (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb)))) (TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) :=
    TypeBRankThreePrincipalQuotientInertiaImages.referenceLocalAction_image
      S SH literal literalH Msys root rootCalibration navarro guard b hb
      parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel
      simple nonabelian psi naturalSurjective (TypeBRankThreePrincipalHonestNormalizerBinding.matchedWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts psi) hUT
  calc
    _ = rawStabilizer (p := 2) (K := K) (H := (CentralCharacterQuotient (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb))) (A := ambient.A)
        ambient.conjugation (TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) :=
      secondLocalAmbient_eq_rawStabilizer
        (P := (TypeBRankThreePrincipalReferenceBinding.problem (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b)) (reference := (TypeBRankThreePrincipalReferenceBinding.reference (F := F) (K := K) (O := O) (k := k) S SH literal literalH Msys root rootCalibration navarro guard b hb)) (psi := psi) (quotient := (TypeBRankThreePrincipalReferenceBinding.quotientBrauer (F := F) (K := K) (O := O) (k := k) (r := r) (f := f) S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi))
        ambient (TypeBBSCentralQuotientPairTransport.quotientBase (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel)) (TypeBRankThreePrincipalQuotientComparison.referenceToPairBase S SH literal literalH Msys root rootCalibration navarro guard b hb parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel simple nonabelian psi) (TypeBBSCentralQuotientPairTransport.quotientLocalAmbient (embeddedG (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource)) (TypeBCriterionEmbeddedPairBinding.embeddedRoot (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root) (TypeBCriterionEmbeddedPairBinding.brauerEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) root psi.val) (TypeBRankThreePrincipalSelectedQuotient.embedded_center_eq_bot parameters N fieldSource C centreSpin fullCover centreClifford naturalKernel) (TypeBCriterionEmbeddedPairBinding.rawWeightEquiv (G F) (soFieldAction 3 F parameters le_rfl N C fieldSource) (CyclicOuterLemma37LiteralLocalExtension.selectedCharacterWeight S b (TypeBRankThreePrincipalHonestNormalizerBinding.matchedWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts psi)))) (TypeBRankThreePrincipalHonestNormalizerBinding.matchedRawWeight (F := F) (K := K) (O := O) (k := k) (r := r) (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) localImage
    _ = _ := matched_rawStabilizer_eq_normalizer
      (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective)
      (S := S) (SH := SH) (f := f) (parameters := parameters) (N := N)
      (fieldSource := fieldSource) (C := C) (rootCalibration := rootCalibration)
      catalogues navarro butterfly roots fieldScope green principalLift clifford
      principalRestriction covering counts centreSpin fullCover simple nonabelian
      psi ambient

end Principal

end ModularRep.PaperProofs.TypeBRankThreePrincipalButterflyAmbientImages


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
