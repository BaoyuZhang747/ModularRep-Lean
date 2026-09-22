import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientMatching
import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientLocalPackets
import ModularRep.PaperProofs.TypeBRankThreePrincipalHonestAmbientBinding
import ModularRep.PaperProofs.TypeCActualFrattiniFromWeightOrbit
import ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
import ModularRep.PaperProofs.TypeBCentralKernelNormalizerInertia

/-!
# Normalizers in the actual honest principal ambient

The prescribed quotient matching fixes the class of the same selected raw
weight. Its literal embedded radical determines the ambient normalizer.
Orbit and subgroup uniqueness give whole raw fixation there, hence fixation
of its own ordinary character and its constructed local Brauer reduction.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalHonestNormalizerBinding

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
open EvenFieldFLZ318FixedTheoremGate TypeBCentralKernelNormalizerInertia
open TypeBRankThreePrincipalQuotientBrauerFibre

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section Elementary

variable {p : ℕ} {K H : Type} [Field K] [CharZero K] [Group H] [Fintype H]

/-- The orbit and its literal radical determine the entire raw character weight. -/
theorem raw_eq_of_class_and_subgroup (W : CharacterWeight p K H) (alpha : MulAut H)
    (fixed : rightTwistConjugacyClass alpha (classOf W) = classOf W)
    (stable : W.subgroup.comap alpha.toMonoidHom = W.subgroup) :
    W.rightTwist alpha = W := by
  have iso : isoOf (W.rightTwist alpha) = isoOf W :=
    CyclicOuterRawPairNormalizer.isoClass_eq_of_conjugacyClass_eq_of_rawSubgroup_eq
      (isoOf (W.rightTwist alpha)) (isoOf W) fixed stable
  exact CharacterWeight.eq_of_isomorphic
    (Quotient.exact
      (s := CharacterWeight.isomorphicSetoid (p := p) (K := K) (G := H))
      (a := W.rightTwist alpha) (b := W) iso)

variable {A : Type} [Group A]
  (X : Subgroup A) (e : H ≃* X) (rho : A →* MulAut H)
  (conjugation : ∀ (a : A) (h : H),
    X.subtype.comp e.toMonoidHom (rho a h) =
      a * X.subtype.comp e.toMonoidHom h * a⁻¹)

include conjugation in
/-- Membership in the actual embedded normalizer gives the inverse-action subgroup equation. -/
theorem embedded_normalizer_stable (Q : Subgroup H) (a : A)
    (ha : a ∈ Subgroup.normalizer
      (Q.map (X.subtype.comp e.toMonoidHom) : Set A)) :
    Q.comap ((rho a)⁻¹).toMonoidHom = Q := by
  have square : (X.subtype.comp e.toMonoidHom).comp (rho a).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (X.subtype.comp e.toMonoidHom) := by
    apply MonoidHom.ext
    exact conjugation a
  have mapped : Q.map (rho a).toMonoidHom = Q := by
    apply Subgroup.map_injective (f := X.subtype.comp e.toMonoidHom)
      (X.subtype_injective.comp e.injective)
    calc
      (Q.map (rho a).toMonoidHom).map (X.subtype.comp e.toMonoidHom) =
          Q.map ((X.subtype.comp e.toMonoidHom).comp (rho a).toMonoidHom) :=
        Subgroup.map_map _ _ _
      _ = Q.map ((MulAut.conj a).toMonoidHom.comp
          (X.subtype.comp e.toMonoidHom)) := congrArg (Q.map) square
      _ = (Q.map (X.subtype.comp e.toMonoidHom)).map (MulAut.conj a).toMonoidHom :=
        (Subgroup.map_map _ _ _).symm
      _ = Q.map (X.subtype.comp e.toMonoidHom) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp ha
  exact (Subgroup.map_equiv_eq_comap_symm (rho a) Q).symm.trans mapped

variable {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

/-- Literal reduction carries fixed ordinary values to the same Brauer character. -/
theorem brauer_fixed_of_raw (W : CharacterWeight p K H)
    (iota : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phi : IBr iota)
    (reduction : SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      iota W.localCharacter phi)
    (alpha : MulAut H)
    (stable : W.subgroup.comap alpha.toMonoidHom = W.subgroup)
    (fixed : W.rightTwist alpha = W) :
    IrreducibleBrauerCharacter.twist iota phi (localAut W.subgroup alpha stable) = phi := by
  have ordinary := (rightTwist_eq_iff_local_fixed W alpha stable).mp fixed
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  change phi.val (PrimeRegularElement.map
    (localAut W.subgroup alpha stable).toMonoidHom x) = phi.val x
  calc
    _ = W.localCharacter (localAut W.subgroup alpha stable x.val) := (reduction _).symm
    _ = W.localCharacter x.val := congrArg
      (fun chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient W.subgroup) =>
        chi x.val) ordinary
    _ = phi.val x := reduction x

/-- The same quotient square transfers fixation to the prescribed normalizer inflation. -/
theorem inflation_fixed_of_local (W : CharacterWeight p K H)
    (iotaQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (phiQ : IBr iotaQ)
    (iotaN : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (W.subgroup : Set H)))
    (phiN : IBr iotaN)
    (inflation : PrimeRegularClassFunction.pullback
      (TypeBCentralKernelWeightTransport.localMk W.subgroup) phiQ.val = phiN.val)
    (alpha : MulAut H)
    (stable : W.subgroup.comap alpha.toMonoidHom = W.subgroup)
    (fixed : IrreducibleBrauerCharacter.twist iotaQ phiQ
      (localAut W.subgroup alpha stable) = phiQ) :
    IrreducibleBrauerCharacter.twist iotaN phiN
      (normalizerAut W.subgroup alpha stable) = phiN := by
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  have square : PrimeRegularElement.map
      (TypeBCentralKernelWeightTransport.localMk W.subgroup)
      (PrimeRegularElement.map (normalizerAut W.subgroup alpha stable).toMonoidHom x) =
    PrimeRegularElement.map (localAut W.subgroup alpha stable).toMonoidHom
      (PrimeRegularElement.map (TypeBCentralKernelWeightTransport.localMk W.subgroup) x) := by
    apply Subtype.ext
    exact (localAut_mk W.subgroup alpha stable x.val).symm
  have fixedValue := congrArg
    (fun chi : IBr iotaQ => chi.val
      (PrimeRegularElement.map (TypeBCentralKernelWeightTransport.localMk W.subgroup) x))
    fixed
  change phiN.val (PrimeRegularElement.map
    (normalizerAut W.subgroup alpha stable).toMonoidHom x) = phiN.val x
  calc
    _ = phiQ.val (PrimeRegularElement.map
        (TypeBCentralKernelWeightTransport.localMk W.subgroup)
        (PrimeRegularElement.map (normalizerAut W.subgroup alpha stable).toMonoidHom x)) :=
      (congrArg
        (fun value : PrimeRegularClassFunction K
            (Subgroup.normalizer (W.subgroup : Set H)) p =>
          value (PrimeRegularElement.map
            (normalizerAut W.subgroup alpha stable).toMonoidHom x)) inflation).symm
    _ = phiQ.val (PrimeRegularElement.map (localAut W.subgroup alpha stable).toMonoidHom
        (PrimeRegularElement.map (TypeBCentralKernelWeightTransport.localMk W.subgroup) x)) :=
      congrArg phiQ.val square
    _ = phiQ.val (PrimeRegularElement.map
        (TypeBCentralKernelWeightTransport.localMk W.subgroup) x) := fixedValue
    _ = phiN.val x := congrArg
      (fun value : PrimeRegularClassFunction K
        (Subgroup.normalizer (W.subgroup : Set H)) p => value x) inflation

end Elementary

/-- The prescribed ambient quotient action fixes its own descended character. -/
theorem ambientBrauer_fixed
    {P : Definition35Problem} {reference psi : Definition35Brauer P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) (a : ambient.A) :
    inverseOpHom ambient.conjugation a • quotient.brauer = quotient.brauer := by
  have h := (ambient.automorphismQuotientEquiv
    (QuotientGroup.mk' (Subgroup.center ambient.A) a)).property
  change ((ambient.automorphismQuotientEquiv
    (QuotientGroup.mk' (Subgroup.center ambient.A) a)) :
      (MulAut (CentralCharacterQuotient P reference))ᵐᵒᵖ) •
        quotient.brauer = quotient.brauer at h
  rw [ambient.automorphismQuotientEquiv_natural] at h
  exact h

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


/-- The original weight is the existing coherent principal selection. -/
def matchedWeight (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b)) : Definition35Weight (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b) :=
  TypeBRankThreePrincipalFixedRootFamilyBinding.principalEquiv (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi

/-- The same selected weight has its prescribed raw packet on the reference quotient. -/
def matchedRawWeight (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b)) :
    CharacterWeight 2 K (quotientGroup S SH literal literalH Msys root rootCalibration navarro guard b hb) :=
  TypeBRankThreePrincipalQuotientLocalPackets.quotientRawWeight
    S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)

/-- Its class is exactly the actual complete quotient weight-fibre image. -/
theorem matchedRaw_class (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b)) :
    classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) =
      (TypeBRankThreePrincipalQuotientMatching.weightEquiv S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).val := by
  letI : Fintype (LiteralPrimitiveBlock k (G F)) := physicalBlockFintype S
  unfold matchedRawWeight
  rw [TypeBRankThreePrincipalQuotientLocalPackets.quotientRawWeight_eq_referenceMap]
  exact (CharacterWeight.conjugacyClassGroupEquiv_mk (quotientEquiv S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb)
    (CyclicOuterLemma37LiteralLocalExtension.selectedCharacterWeight S b (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi))).symm.trans
      ((congrArg (CharacterWeight.conjugacyClassGroupEquiv (quotientEquiv S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb))
        (CyclicOuterLemma37LiteralLocalExtension.selectedCharacterWeight_spec S b (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi))).trans
          (TypeBRankThreePrincipalQuotientMatching.weightEquiv_val
            S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).symm)

/-- This graph point is constructed from the actual original selected pair. -/
theorem matchedGraph (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b)) :
    (TypeBRankThreePrincipalQuotientMatching.Graph (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).brauer (classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi)) := by
  refine ⟨(fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi), rfl, ?_⟩
  exact (congrArg Subtype.val
    (TypeBRankThreePrincipalQuotientMatching.matching_on_original (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi)).trans
      (matchedRaw_class (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).symm

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


variable (psi : Definition35Brauer (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b)) (ambient : SpathAmbientGroup (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi))

include gggr fyz naturalSurjective in
/-- Every actual ambient element fixes the class of this same raw quotient weight. -/
theorem matchedClass_fixed (a : ambient.A) :
    inverseOpHom ambient.conjugation a • classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) = classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) := by
  have acted := (TypeBRankThreePrincipalQuotientMatching.graph_opAut (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective)
    (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian (inverseOpHom ambient.conjugation a)
      (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi).brauer (classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi))).mpr (matchedGraph (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi)
  rcases acted with ⟨chi, character, weight⟩
  have hchi : chi = (fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) :=
    Subtype.ext (character.trans (ambientBrauer_fixed ambient a))
  subst chi
  have original := matchedGraph (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi
  rcases original with ⟨eta, character, value⟩
  have heta : eta = (fibreEquiv S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) := Subtype.ext character
  subst eta
  exact weight.symm.trans value

/-- The subgroup equation uses the actual inverse action and literal ambient normalizer. -/
theorem normalizer_stable (a : AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) :
    (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).subgroup.comap ((ambient.conjugation (a : ambient.A))⁻¹).toMonoidHom =
      (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).subgroup := by
  exact embedded_normalizer_stable ambient.base ambient.baseEquiv ambient.conjugation
    ambient.conjugation_on_base (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).subgroup (a : ambient.A) a.property

include gggr fyz naturalSurjective in
/-- Fixation of its class and actual radical fixes the entire chosen raw pair. -/
theorem normalizer_raw_fixed (a : AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) :
    (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).rightTwist (ambient.conjugation (a : ambient.A))⁻¹ = (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) := by
  apply raw_eq_of_class_and_subgroup
  · have fixed := matchedClass_fixed (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient (a : ambient.A)
    change rightTwistConjugacyClass (ambient.conjugation (a : ambient.A)⁻¹)
      (classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi)) = classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) at fixed
    simpa only [map_inv] using fixed
  · exact normalizer_stable (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a

include gggr fyz naturalSurjective in
/-- The actual honest ambient is generated by its base and this radical normalizer. -/
theorem matched_frattini :
    ambient.base ⊔ (AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) = ⊤ := by
  apply TypeCActualFrattiniFromWeightOrbit.frattini_of_weightClass_fixed
    ambient.base ambient.baseEquiv ambient.conjugation ambient.conjugation_on_base (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi)
  intro a
  have fixed := matchedClass_fixed (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a
  change rightTwistConjugacyClass (ambient.conjugation a⁻¹) (classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi)) =
    classOf (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) at fixed
  simpa only [map_inv, OddTwoSelectedWeightAutomorphismCoordinates.weightClass,
    TypeBCentralKernelInertia.classOf, TypeBCentralKernelInertia.isoOf] using fixed

include gggr fyz naturalSurjective in
/-- Every member of the actual normalizer fixes the own local ordinary character. -/
theorem normalizer_ordinary_fixed (a : AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) :
    OrdinaryIrreducibleCharacter.twist K _ (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).localCharacter
      (localAut (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).subgroup (ambient.conjugation (a : ambient.A))⁻¹
        (normalizer_stable (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)) = (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).localCharacter :=
  (rightTwist_eq_iff_local_fixed (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) (ambient.conjugation (a : ambient.A))⁻¹
    (normalizer_stable (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)).mp
      (normalizer_raw_fixed (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)

include gggr fyz naturalSurjective in
/-- The same normalizer fixes the constructed quotient local Brauer reduction. -/
theorem normalizer_brauer_fixed (a : AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) :
    IrreducibleBrauerCharacter.twist (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).iota (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).brauer
      (localAut (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).subgroup (ambient.conjugation (a : ambient.A))⁻¹
        (normalizer_stable (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)) = (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).brauer :=
  brauer_fixed_of_raw (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).iota (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).brauer (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).reduction
    (ambient.conjugation (a : ambient.A))⁻¹
    (normalizer_stable (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)
    (normalizer_raw_fixed (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)

include gggr fyz naturalSurjective in
/-- The actual inflated normalizer character is fixed under the same inverse conjugation. -/
theorem normalizer_inflated_fixed (a : AmbientLocalGroup (TypeBRankThreePrincipalReferenceBinding.problem S SH literal literalH Msys root rootCalibration navarro guard b) (TypeBRankThreePrincipalReferenceBinding.reference S SH literal literalH Msys root rootCalibration navarro guard b hb) psi (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) :
    IrreducibleBrauerCharacter.twist (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).iota (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).brauer
      (normalizerAut (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi).subgroup (ambient.conjugation (a : ambient.A))⁻¹
        (normalizer_stable (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)) = (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).brauer :=
  inflation_fixed_of_local (matchedRawWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi) (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).iota (TypeBRankThreePrincipalQuotientLocalPackets.quotientWeight S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).brauer (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).iota (TypeBRankThreePrincipalQuotientLocalPackets.localInflation S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi)).brauer
    (TypeBRankThreePrincipalQuotientLocalPackets.localInflation_inflation
      S SH literal literalH Msys root rootCalibration navarro guard b parameters N C centreSpin fullCover simple nonabelian hb (matchedWeight (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts psi))
    (ambient.conjugation (a : ambient.A))⁻¹
    (normalizer_stable (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)
    (normalizer_brauer_fixed (gggr := gggr) (fyz := fyz) (naturalSurjective := naturalSurjective) (S := S) (SH := SH)
      (f := f) (parameters := parameters) (N := N) (fieldSource := fieldSource) (C := C)
      (rootCalibration := rootCalibration) catalogues navarro butterfly roots fieldScope
      green principalLift clifford principalRestriction covering counts centreSpin fullCover simple nonabelian psi ambient a)


end Principal

end ModularRep.PaperProofs.TypeBRankThreePrincipalHonestNormalizerBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
