import ManuscriptIBAW.TypeC.PrincipalApplicationFamilies
import ManuscriptIBAW.Jordan.TypeCOddLocalized

/-!
# Type C in odd characteristic at the prime two

The principal correspondence is constructed from the parameters and then
corrected to satisfy the modular character triple conditions. The complete
relative hypothesis for strict blocks is used in Jordan reduction after
restriction has been proved. The resulting global map gives the specified
original Späth condition, with the same coefficient fields, blocks
and roots along the quotient projection.

Published source interpretations remain explicit. The principal bijection,
the completed relative hypotheses and the global map are conclusions of the
construction.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
open ModularRep.PaperProofs.OddTwoDefinition35GlobalAssembly
open ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin
open ManuscriptIBAW.Jordan

variable {pDef : ℕ} {scope : FLZFullHGUniverse pDef 2}
variable {coverage : FullHGDefinition35Coverage scope}
variable {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
variable (routing : FullHGPrincipalRoutingSource coverage strictSource)
variable (blockSource : FullHGBlockSource coverage)
variable (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
variable (sources : PrincipalApplicationFamilySource routing blockSource interpretation)
variable (typeA : ∀ (pair : FullHG scope)
    (presentation : TypeAActualPresentation pDef (routing.pairSource pair).rank
      (coverage.presentation pair).family.H),
    TypeAApplicationData (coverage.presentation pair).family presentation
      (blockSource.automorphisms pair) (blockSource.source pair))

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [CharP F pDef]
variable {C : CenterIntersectionSource n F} (B : BroughGroupSource C)
variable (cover : OddSymplecticFullCoverSource n F)
variable (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))
variable (P : LiteralFengMalleProblem n F)

local instance applicationFieldAutomorphismFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective

variable (support : OperationsBrauerSupport P.iota P.irreducibleBrauerInjective
  P.blockSource.operations)
variable (reduction : ∀ (b : LiteralBlock P) (w : LiteralWeightFibre P.blockSource b),
  SelectedLocalReductionSource P.blockSource b w)
variable (binding : AmbientBinding P support reduction scope coverage)
variable (input : InputSemantics P)
variable (coordinates : RegularActionCoordinates B cover lifting)
variable (assumptionSource : FLZRemark54Source B cover lifting P)
variable {Label : Type}
variable (context : GeometricContext (ell := 2) (k := P.k) (S := Label)
  ((regularAction B cover lifting).comp SemidirectProduct.inl)
  (spFieldAction (n := n) (F := F)))
variable (geometry : GeometricSelection
  ((regularAction B cover lifting).comp SemidirectProduct.inl)
  (spFieldAction (n := n) (F := F)) context)
variable (theoremSource : TypeCOddLocalized.FLZ57PerLabelMapSource B cover lifting P
  support reduction scope coverage blockSource strictSource context)
variable (series : TypeCOddLocalized.AmbientSeriesBinding B cover lifting P
  support reduction scope coverage blockSource strictSource context binding interpretation)

/-- The global Sp map follows from the constructed principal and Type A
hypotheses and the proved restriction for each label. -/
def principalApplicationGlobalMap : LiteralGlobalMap P :=
  TypeCOddLocalized.globalMap B cover lifting P support reduction scope coverage
    blockSource strictSource context binding interpretation input coordinates
    assumptionSource geometry theoremSource series (sources.strictBlocks typeA)

omit [CharP F pDef] in
include routing blockSource interpretation sources typeA B cover lifting
  support reduction binding input coordinates assumptionSource context geometry theoremSource series in
/-- Proposition 3.3 under the stated assumptions, with the specified original
Späth condition on PSp and its identity prime-to-two cover. The final map
need not equal the initial counting bijection. -/
theorem prop33_originalIBAW
    (O : LiteralDiagonalFieldRealisation n F) (target : TargetData P)
    (fm34 : FengMalleProposition34Source P O target)
    (cor46 : LiteralFengMalleCorollary46Certificate P O) :
    ModularRep.PaperProofs.OddTwoLiteralSpathTarget.OriginalIBAW target.toProblem :=
  originalIBAW_of_literalGlobalMap P O target fm34 input
    (principalApplicationGlobalMap routing blockSource interpretation sources typeA
      B cover lifting P support reduction binding input coordinates assumptionSource
      context geometry theoremSource series) cor46

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
