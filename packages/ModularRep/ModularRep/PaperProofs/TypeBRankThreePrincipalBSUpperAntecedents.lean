import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerTwist
import ModularRep.PaperProofs.TypeBRankThreePrincipalLocalExtensions
import ModularRep.PaperProofs.TypeBPrincipalUpperPairBlockBinding

/-!
# Local and upper antecedents for the same principal SO pair

One upper raw weight is selected from the actual covering relation before
the common quotient character and all field actors. Both local extensions
use the original lower raw weight and its own ordinary character. The
upper ordinary block induces to the specified block of the original upper
Brauer character. Every map, root and block operation is the existing one.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalBSUpperAntecedents

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldMatchingSplitting
open TypeBRankThreePrincipalFieldNaturality
open TypeBCliffordOrthogonalAmbientQuotient TypeBGreenPrincipalConstituentSource
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBModularLinearCharacterLift TypeBLocalPhysicalBlockBinding
open TypeBCriterionHypotheses

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

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
  {indexTwo : (G F).index = 2}
  {parameters : OddFieldParameters F r f} {N : NormSource 3 F}
  {fieldSource : FieldActionSource 3 F r f parameters N}
  {C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N}
  {Msys : ModularSystem 2 K O k}
  [NeZero f]
  [ambientRoots : HasEnoughRootsOfUnity K
    (Nat.card (TypeBMatrixAmbientOrdinaryRoots.MatrixAmbient parameters N fieldSource C))]
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb indexTwo)
  (roots : TypeBGreenPrincipalConstituentSource.RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)
  {coefficient : SpathCoefficientField 2 k Msys.prime}
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  (fyz : TypeBRankThreePrincipalWeightFieldSplitting.FYZCorollary363SplittingSource
    F r f parameters Msys coefficient root rootH
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys root rootCalibration)
    (TypeBPrincipalRootLiftBinding.root_eq_groupRoot Msys rootH rootHCalibration)
    S SH literal literalH guard guardH b hb bH hbH)
  {delta : H F} {outside : delta ∉ G F} {notThree : Nat.card F ≠ 3}
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta indexTwo outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource
local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction

include gggr fyz ambientRoots in
/-- The chosen upper pair, its specified block and common quotient twist
accompany both ordinary extensions of the unchanged lower raw weight. -/
theorem principalSOEquiv_localUpperAntecedents
    (ordinarySource : ∀ (X : Type) [Group X] [Finite X]
      [HasEnoughRootsOfUnity K (Nat.card X)],
        TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K X)
    (ordinary : ∀ Q : Subgroup (H F), NormalizerOrdinarySource Msys SH.operations Q)
    (membership : OrdinaryInflationMembership Msys SH.operations ordinary)
    (productFormula : BrauerLinearTensorProductFormula rootH)
    (Phi : SOBrauer F rootH bH) (theta : OmegaBrauer F root b)
    (w : OmegaWeight F S b)
    (occurs : NavarroCoveringBrauerExtension.BrauerOccursInRestriction
      (G F) rootH root Phi.val theta.val)
    (covered : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (soMap Phi).val w.val)
    (W : CharacterWeight 2 K (G F))
    (representative : TypeBWeightCoveringSource.rawClass W = w.val) :
    ∃ V : CharacterWeight 2 K (H F),
      ∃ mu : IBr (TypeBPrincipalQuotientBrauerTwistBinding.quotientRoot (G F) Msys),
        ∃ lambda : TypeCWeightTensorFieldAction.RadicalTensorCharacter
            (p := 2) (K := K) (G := H F),
          TypeBWeightCoveringSource.rawClass V = (soMap Phi).val ∧
          NavarroCoveringBrauerExtension.BrauerOccursInRestriction
            (G F) rootH root Phi.val theta.val ∧
          TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
            (TypeBWeightCoveringSource.rawClass V) (TypeBWeightCoveringSource.rawClass W) ∧
          Nonempty (LocalOrdinaryExtension (ell := 2) (K := K) (G F) matrixField W
            (TypeBRankThreePrincipalLocalExtensions.MInertia
              (K := K) parameters N fieldSource C W)) ∧
          Nonempty (LocalOrdinaryExtension (ell := 2) (K := K) (G F) matrixField W
            (TypeBRankThreePrincipalLocalExtensions.GEInertia
              (K := K) parameters N fieldSource C W)) ∧
          (letI := SH.operations.ambientBlockData.fintypeBlock
           letI := (SH.operations.inflatedNormalizerBlockData V.subgroup).fintypeBlock
           BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (H F)))
             (SH.operations.inflatedNormalizerBlockData V.subgroup).catalogue
             SH.operations.ambientBlockData.catalogue
             (ordinaryNormalizerBlock Msys SH.operations V.subgroup (ordinary V.subgroup)
               (inflatedOrdinary V.subgroup V.localCharacter))
             (TypeBCentralKernelBrauerBlocks.block rootH
               (physicalDecomposition SH literalH) Phi.val)) ∧
          mu = TypeBPrincipalQuotientBrauerTwistBinding.quotientBrauer (G F) Msys ∧
          lambda.val = quotientLift rootH (G F)
            (TypeBPrincipalQuotientBrauerTwistBinding.quotientLambda (k := k) (G F)) ∧
          lambda = 1 ∧
          (∀ h : PrimeRegularElement (G := H F) 2,
            (lambda.val h.val : K) =
              mu.val (PrimeRegularElement.map (QuotientGroup.mk' (G F)) h)) ∧
          ∀ e : FieldGroup f,
            (IrreducibleBrauerCharacter.twist rootH Phi.val (matrixField e⁻¹)).val =
              PrimeRegularClassFunction.pointwiseMul
                (PrimeRegularClassFunction.pullback (QuotientGroup.mk' (G F)) mu.val)
                Phi.val.val ∧
            TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
                lambda (TypeBWeightCoveringSource.rawClass V) =
              CharacterWeight.rightTwistConjugacyClass (matrixField e⁻¹)
                (TypeBWeightCoveringSource.rawClass V) := by
  obtain ⟨V, W0, representsV, representsW0, rawCover⟩ := covered
  have coverOriginal : TypeBWeightCoveringSplittingSource.CoversClass (G F) dgn
      (TypeBWeightCoveringSource.rawClass V) (TypeBWeightCoveringSource.rawClass W) :=
    ⟨V, W0, rfl, representsW0.trans representative.symm, rawCover⟩
  obtain ⟨extensionM, extensionGE⟩ :=
    TypeBRankThreePrincipalLocalExtensions.ordinary_extensions
      parameters N fieldSource C W ordinarySource indexTwo
  have upperBlock :=
    TypeBPrincipalUpperPairBlockBinding.principalSOEquiv_upperPair_ordinaryBlockInducesTo
      covering counts roots fieldScope green principalLift clifford principalRestriction
      ordinary membership Phi V representsV
  obtain ⟨mu, lambda, canonicalMu, selectedLift, equalOne, regularValues, twists⟩ :=
    TypeBRankThreePrincipalQuotientBrauerTwist.principalSOEquiv_quotientBrauerTwist_allField
      (literalH := literalH) (hbH := hbH) (indexTwo := indexTwo)
      (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration)
      gggr roots fieldScope green principalLift clifford principalRestriction fyz
      covering counts productFormula Phi
  refine ⟨V, mu, lambda, representsV, occurs, coverOriginal, extensionM, extensionGE,
    upperBlock, canonicalMu, selectedLift, equalOne, regularValues, ?_⟩
  intro e
  exact ⟨(twists e⁻¹).1, by simpa only [representsV] using (twists e⁻¹).2⟩

end ModularRep.PaperProofs.TypeBRankThreePrincipalBSUpperAntecedents


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
