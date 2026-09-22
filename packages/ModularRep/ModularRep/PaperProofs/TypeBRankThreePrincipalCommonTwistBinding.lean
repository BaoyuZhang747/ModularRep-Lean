import ModularRep.PaperProofs.TypeBPrincipalCommonTrivialTwist
import ModularRep.PaperProofs.TypeBRankThreePrincipalFieldMatchingSplitting

/-!
# One common quotient twist on the actual principal SO fibres

The accepted specified GGGR and FYZ deductions fix the actual upper Brauer
character and ordinary weight conjugacy class under the same SO field
automorphism. The index-two characteristic-two calculation consequently
chooses the identity quotient character once, before all field elements.
Its ordinary character is precisely the selected prime-to-two lift.

The final specialization keeps the previously constructed principal SO map.
No new map, fixedness, raw representative or character triple is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalCommonTwistBinding

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCentralKernelInertia TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalBrauerOrbitBinding TypeBRankThreePrincipalFieldNaturality
open TypeBRankThreePrincipalFieldMatchingSplitting TypeBCliffordOrthogonalAmbientQuotient
open TypeBGreenPrincipalConstituentSource NavarroCoveringBrauerExtension
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBPrincipalCommonTrivialTwist TypeBModularLinearCharacterLift

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {r f : ℕ} [CharP F r]
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
  (gggr : GGGRInputs S literal parameters N fieldSource Msys C root b hb indexTwo)
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

local notation "matrixField" => soFieldAction 3 F parameters le_rfl N C fieldSource

include literalH hbH gggr roots fieldScope green principalLift clifford principalRestriction in
/-- Forgetting the supported-fibre subtype keeps the same SO automorphism. -/
theorem soBrauer_positiveField_fixed (e : FieldGroup f) (Phi : SOBrauer F rootH bH) :
    IrreducibleBrauerCharacter.twist rootH Phi.val (matrixField e) = Phi.val := by
  exact congrArg Subtype.val
    (soBrauerFieldTwist_fixed (literalH := literalH) (hbH := hbH)
      gggr roots fieldScope green principalLift clifford principalRestriction e Phi)

variable
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

include fyz in
/-- FYZ fixes this actual upper ordinary weight class, without choosing a raw weight. -/
theorem soWeight_positiveField_fixed (e : FieldGroup f) (v : SOWeight F SH bH) :
    CharacterWeight.rightTwistConjugacyClass (matrixField e) v.val = v.val := by
  exact congrArg Subtype.val
    (soWeightFieldTwist_fixed (literalH := literalH) (hbH := hbH)
      (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration) fyz e v)

include gggr roots fieldScope green principalLift clifford principalRestriction fyz in
/-- The same identity quotient character works for every actual field element. -/
theorem commonTrivialTwist_allField
    (productFormula : BrauerLinearTensorProductFormula rootH)
    (Phi : SOBrauer F rootH bH) (v : SOWeight F SH bH) :
    ∃ lambda : linearCharactersTrivialOn (k := k) (G F),
      lambda = 1 ∧ quotientLift rootH (G F) lambda = (1 : H F →* Kˣ) ∧
        ∀ e : FieldGroup f,
          IrreducibleBrauerCharacter.twist rootH Phi.val (matrixField e) =
            IrreducibleBrauerCharacter.linearTwist rootH productFormula Phi.val lambda.val ∧
          TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
              (radicalLift (G F) indexTwo rootH lambda) v.val =
            CharacterWeight.rightTwistConjugacyClass (matrixField e) v.val := by
  refine ⟨1, rfl, selectedOrdinaryLift_one (G F) rootH, ?_⟩
  intro e
  obtain ⟨lambda, equalOne, _, brauerTwist, weightTwist⟩ :=
    commonTrivialTwist_of_fixed (G F) indexTwo rootH productFormula
      (matrixField e) Phi.val v.val
      (soBrauer_positiveField_fixed (literalH := literalH) (hbH := hbH)
        gggr roots fieldScope green principalLift clifford principalRestriction e Phi)
      (soWeight_positiveField_fixed (literalH := literalH) (hbH := hbH)
        (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration) fyz e v)
  subst lambda
  exact ⟨brauerTwist, weightTwist⟩

variable
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

local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction

include gggr fyz in
/-- Specialize to the same previously constructed SO map, with no map input. -/
theorem principalSOEquiv_commonTrivialTwist_allField
    (productFormula : BrauerLinearTensorProductFormula rootH)
    (Phi : SOBrauer F rootH bH) :
    ∃ lambda : linearCharactersTrivialOn (k := k) (G F),
      lambda = 1 ∧ quotientLift rootH (G F) lambda = (1 : H F →* Kˣ) ∧
        ∀ e : FieldGroup f,
          IrreducibleBrauerCharacter.twist rootH Phi.val (matrixField e) =
            IrreducibleBrauerCharacter.linearTwist rootH productFormula Phi.val lambda.val ∧
          TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
              (radicalLift (G F) indexTwo rootH lambda) (soMap Phi).val =
            CharacterWeight.rightTwistConjugacyClass (matrixField e) (soMap Phi).val :=
  commonTrivialTwist_allField (literalH := literalH) (hbH := hbH)
    (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration)
    gggr roots fieldScope green principalLift clifford principalRestriction fyz
    productFormula Phi (soMap Phi)

end ModularRep.PaperProofs.TypeBRankThreePrincipalCommonTwistBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
