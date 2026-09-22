import ManuscriptIBAW.Jordan.TypeCOdd
import ManuscriptIBAW.Jordan.SeriesBinding

/-!
# Jordan reduction for Type C over a field of odd order

The published Jordan theorem is applied to the chosen permissible groups and
their proved restricted representatives. The complete relative class, maps
and original Späth condition are fixed throughout.
-/

noncomputable section

namespace ManuscriptIBAW.Jordan.TypeCOddLocalized

open ModularRep
open ModularRep.PaperProofs
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family EvenFieldFLZFullHG
open OddTwoConformalProjectiveRealisation OddTwoProjectiveAutomorphismDiagonalJoin
open OddTwoUniversalPrimeToTwoSelfCover OddTwoFinalBlockOrbitCentralCoverDescentWindow
open OddTwoDefinition35GlobalAssembly OddTwoFengMalleForwardSourceJoin
open OddTwoActualLocalBlockSupport OddTwoFLZ57LiteralMapSource

variable {n : ℕ} {F : Type} [Field F] [Fintype F]
  {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
  (cover : OddSymplecticFullCoverSource n F)
  (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))
  (P : LiteralFengMalleProblem n F)

local instance fieldAutomorphismFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective

variable (support : OperationsBrauerSupport P.iota P.irreducibleBrauerInjective
    P.blockSource.operations)
  (reduction : ∀ (b : LiteralBlock P) (w : LiteralWeightFibre P.blockSource b),
    SelectedLocalReductionSource P.blockSource b w)
  {pDef : ℕ} [CharP F pDef]
  (scope : FLZFullHGUniverse pDef 2)
  (coverage : FullHGDefinition35Coverage scope)
  (blockSource : FullHGBlockSource coverage)
  (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
  {Label : Type}
  (context : GeometricContext (ell := 2) (k := P.k) (S := Label)
    ((regularAction S cover lifting).comp SemidirectProduct.inl)
    (spFieldAction (n := n) (F := F)))

/-- Transport the ambient strict label along the specified equality of complete
families. The primitive block is the same under this identification. -/
def ambientStrictLabel
    (binding : AmbientBinding P support reduction scope coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource) :
    (literalFamily P support reduction).Block →
      (interpretation.strictModel scope.ambientPair).Dual := fun b =>
  (interpretation.strictModel scope.ambientPair).label
    (cast (congrArg (fun family : Definition35Family.{0} 2 => family.Block)
      binding.family_eq.symm) b)

/-- The geometric series and the strict labels refer to the original symplectic family through its fixed ambient identification. -/
abbrev AmbientSeriesBinding
    (binding : AmbientBinding P support reduction scope coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource) :=
  SeriesBinding (literalFamily P support reduction) context
    (ambientStrictLabel P support reduction scope coverage blockSource strictSource
      binding interpretation)

/-- Apply the published Jordan consequence for block maps (E2) after
constructing its first hypothesis for every label. -/
structure FLZ57PerLabelMapSource : Prop where
  applyTheorem57 :
    ∀ (binding : AmbientBinding P support reduction scope coverage)
      (interpretation : FullHGInterpretation scope coverage blockSource strictSource),
    AmbientSeriesBinding S cover lifting P support reduction scope coverage
      blockSource strictSource context binding interpretation →
    InputSemantics P →
    RegularActionCoordinates S cover lifting →
    GeneralPerLabelHypothesis
      ((regularAction S cover lifting).comp SemidirectProduct.inl)
      (spFieldAction (n := n) (F := F)) P.iota context →
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource →
    Nonempty (BlockMapFamily (literalFamily P support reduction))

variable (binding : AmbientBinding P support reduction scope coverage)
  (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
  (input : InputSemantics P)
  (coordinates : RegularActionCoordinates S cover lifting)
  (assumptionSource : FLZRemark54Source S cover lifting P)
  (geometry : GeometricSelection
    ((regularAction S cover lifting).comp SemidirectProduct.inl)
    (spFieldAction (n := n) (F := F)) context)
  (theoremSource : FLZ57PerLabelMapSource S cover lifting P support reduction
    scope coverage blockSource strictSource context)
  (series : AmbientSeriesBinding S cover lifting P support reduction scope coverage
    blockSource strictSource context binding interpretation)

include binding interpretation input coordinates assumptionSource geometry theoremSource series in
def globalMap (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource) :
    LiteralGlobalMap P :=
  literalGlobalMap P support reduction
    (Classical.choice (theoremSource.applyTheorem57 binding interpretation series input coordinates
      (TypeCOdd.generalPerLabel S cover lifting P context geometry
        (assumptionSource.assumption53 coordinates)) strictBlocks))

omit [CharP F pDef] in
include binding interpretation input coordinates assumptionSource geometry theoremSource series in
theorem originalIBAW
    (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource)
    (O : LiteralDiagonalFieldRealisation n F) (target : TargetData P)
    (fm34 : FengMalleProposition34Source P O target)
    (cor46 : LiteralFengMalleCorollary46Certificate P O) :
    OddTwoLiteralSpathTarget.OriginalIBAW target.toProblem :=
  originalIBAW_of_literalGlobalMap P O target fm34 input
    (globalMap S cover lifting P support reduction scope coverage blockSource strictSource
      context binding interpretation input coordinates assumptionSource geometry theoremSource
      series strictBlocks) cor46

end ManuscriptIBAW.Jordan.TypeCOddLocalized

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
