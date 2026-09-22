import ModularRep.PaperProofs.TypeBRankThreePrincipalCommonTwistBinding
import ModularRep.PaperProofs.TypeBPrincipalQuotientBrauerTwistBinding

/-!
# The actual quotient Brauer twist for the computed principal SO map

The quotient character is the irreducible Brauer character of the trivial
representation of the actual SO/Omega quotient, using the same modular
system. Its selected ordinary lift is the previously constructed quotient
lift. Both are fixed before every field actor.

The accepted GGGR/FYZ common-twist deduction supplies the two action
identities for the original upper character and precisely the computed SO
map. Calibrated inflation replaces its modular linear character by the
literal quotient Brauer character. No fixedness, map, raw representative or
block-triple witness is an additional input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerTwist

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldMatchingSplitting
open TypeBCliffordOrthogonalAmbientQuotient TypeBGreenPrincipalConstituentSource
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBModularLinearCharacterLift

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

include gggr fyz in
/-- One actual quotient IBr and its selected ordinary lift work before all
field actors, for the original Phi and the same computed principal SO map. -/
theorem principalSOEquiv_quotientBrauerTwist_allField
    (productFormula : BrauerLinearTensorProductFormula rootH)
    (Phi : SOBrauer F rootH bH) :
    ∃ mu : IBr (TypeBPrincipalQuotientBrauerTwistBinding.quotientRoot (G F) Msys),
      ∃ lambda : TypeCWeightTensorFieldAction.RadicalTensorCharacter
          (p := 2) (K := K) (G := H F),
        mu = TypeBPrincipalQuotientBrauerTwistBinding.quotientBrauer (G F) Msys ∧
        lambda.val = quotientLift rootH (G F)
          (TypeBPrincipalQuotientBrauerTwistBinding.quotientLambda (k := k) (G F)) ∧
        lambda = 1 ∧
        (∀ h : PrimeRegularElement (G := H F) 2,
          (lambda.val h.val : K) =
            mu.val (PrimeRegularElement.map (QuotientGroup.mk' (G F)) h)) ∧
        ∀ e : FieldGroup f,
          (IrreducibleBrauerCharacter.twist rootH Phi.val (matrixField e)).val =
            PrimeRegularClassFunction.pointwiseMul
              (PrimeRegularClassFunction.pullback (QuotientGroup.mk' (G F)) mu.val)
              Phi.val.val ∧
          TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
              lambda (soMap Phi).val =
            CharacterWeight.rightTwistConjugacyClass (matrixField e) (soMap Phi).val := by
  obtain ⟨oldLambda, _equalOne, _selectedLift, twists⟩ :=
    TypeBRankThreePrincipalCommonTwistBinding.principalSOEquiv_commonTrivialTwist_allField
      (literalH := literalH) (hbH := hbH) (indexTwo := indexTwo)
      (rootCalibration := rootCalibration) (rootHCalibration := rootHCalibration)
      gggr roots fieldScope green principalLift clifford principalRestriction fyz
      covering counts productFormula Phi
  have canonical := TypeBPrincipalQuotientBrauerTwistBinding.lambda_eq_quotientLambda
    (G F) indexTwo oldLambda
  rw [canonical] at twists
  refine ⟨TypeBPrincipalQuotientBrauerTwistBinding.quotientBrauer (G F) Msys,
    TypeBPrincipalCommonTrivialTwist.radicalLift (G F) indexTwo rootH
      (TypeBPrincipalQuotientBrauerTwistBinding.quotientLambda (k := k) (G F)),
    rfl, rfl, ?_, ?_, ?_⟩
  · exact TypeBPrincipalCommonTrivialTwist.radicalLift_eq_one
      (G F) indexTwo rootH
      (TypeBPrincipalQuotientBrauerTwistBinding.quotientLambda (k := k) (G F))
  · intro h
    have compatible :=
      TypeBPrincipalQuotientBrauerTwistBinding.selectedOrdinaryLift_regular_value
        (G F) Msys rootH rootHCalibration h
    exact compatible.trans (congrArg
      (fun c : PrimeRegularClassFunction K (H F) 2 => c h)
      (TypeBPrincipalQuotientBrauerTwistBinding.inflatedBrauer_val
        (G F) Msys rootH rootHCalibration))
  · intro e
    constructor
    · have product := TypeBPrincipalQuotientBrauerTwistBinding.brauer_twist_inflated
        (G F) Msys rootH rootHCalibration productFormula Phi.val
      exact ((congrArg Subtype.val (twists e).1).trans product).trans
        (congrArg
          (fun c : PrimeRegularClassFunction K (H F) 2 =>
            PrimeRegularClassFunction.pointwiseMul c Phi.val.val)
          (TypeBPrincipalQuotientBrauerTwistBinding.inflatedBrauer_val
            (G F) Msys rootH rootHCalibration))
    · exact (twists e).2

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerTwist


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
