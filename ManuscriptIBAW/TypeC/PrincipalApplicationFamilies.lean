import ManuscriptIBAW.TypeC.PrincipalApplicationInputs
import ManuscriptIBAW.TypeC.LiLiSource
import ModularRep.PaperProofs.OddTwoFullHGPrincipalApplication

/-!
# The principal correspondence on every relative family

The operations, primitive block interpretation and common root convention
belong to the fixed family. The source data determine the principal
correspondence on that family's intrinsic data. The correction argument
interprets the required tuples for every admissible choice, corrects the map
and transports the resulting bijection using the selected groups, characters
and roots.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCommonRoots
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCompletedSeed
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting
open ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource

universe u

section Family

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)
variable (input : TypeAInputSemantics family)
variable (standard : BlockTripleSourceSemantics 2 family.k family.K)

local instance applicationFamilySpFintype : Fintype (Sp rank F) := Fintype.ofFinite _

/-- Inputs for the fixed family, with the principal correspondence constructed
from its intrinsic data and primitive block interpretation. -/
structure PrincipalApplicationFamilyInputs where
  operations : LocalBlockInductionOperations
    (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block)
  dictionary : PrimitiveDictionary family.blockSource.operations operations
    (groupEquiv family block carrier)
  commonRoots : FamilyCommonRootConvention family block carrier
  published :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    PrincipalApplicationPublishedInputs
      (data family block carrier input operations dictionary) standard

namespace PrincipalApplicationFamilyInputs

variable {family block carrier input standard}
variable (I : PrincipalApplicationFamilyInputs family block carrier input standard)

/-- The family uses these same operations, root tables and characters. Its
principal correspondence is supplied by the parameter construction. -/
def toFamilyInputs : FamilyInputs family block carrier input standard where
  operations := I.operations
  dictionary := I.dictionary
  commonRoots := I.commonRoots
  published := by
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    exact I.published.toPublishedInputs

@[simp] theorem toFamilyInputs_operations : I.toFamilyInputs.operations = I.operations := rfl

@[simp] theorem toFamilyInputs_FM :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    I.toFamilyInputs.published.FM = I.published.correspondence := rfl

end PrincipalApplicationFamilyInputs

end Family

section FullFamily

variable {pDef : ℕ} {scope : FLZFullHGUniverse pDef 2}
variable {coverage : FullHGDefinition35Coverage scope}
variable {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
variable (routing : FullHGPrincipalRoutingSource coverage strictSource)
variable (blockSource : FullHGBlockSource coverage)
variable (interpretation : FullHGInterpretation scope coverage blockSource strictSource)

/-- Source assumptions for every original relative pair and principal block.
Rank two uses Li–Li and central lifting. Higher ranks use the character
selection, principal parameter construction and correction argument. -/
structure PrincipalApplicationFamilySource where
  rankTwo : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block)
      (coordinates : SymplecticCoordinates pDef (routing.pairSource pair).rank
        (coverage.presentation pair).family.H)
      (carrier : OddSymplecticPrincipalCarrier
        ((coverage.presentation pair).family.problem block)
        (routing.pairSource pair).rank coordinates.F),
    (routing.pairSource pair).rank = 2 →
    LiLiSource.ClosedRankTwoPrincipalInputs coordinates.F
      ((coverage.presentation pair).family.problem block)
      (blockSource.automorphisms pair block) (blockSource.source pair block)
  higherRank : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block)
      (coordinates : SymplecticCoordinates pDef (routing.pairSource pair).rank
        (coverage.presentation pair).family.H)
      (carrier : OddSymplecticPrincipalCarrier
        ((coverage.presentation pair).family.problem block)
        (routing.pairSource pair).rank coordinates.F),
    3 ≤ (routing.pairSource pair).rank →
    PrincipalApplicationFamilyInputs (coverage.presentation pair).family block carrier
      (interpretation.blockSemantics pair) (interpretation.standard pair)

/-- The resulting bijections use the original blocks, automorphism actions
and character triple interpretations. -/
structure PrincipalBlockBijections where
  atPrincipal : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block)
      (coordinates : SymplecticCoordinates pDef (routing.pairSource pair).rank
        (coverage.presentation pair).family.H)
      (carrier : OddSymplecticPrincipalCarrier
        ((coverage.presentation pair).family.problem block)
        (routing.pairSource pair).rank coordinates.F),
    Nonempty (Definition35IBAWBijection ((coverage.presentation pair).family.problem block)
      (blockSource.automorphisms pair block) (blockSource.source pair block))

namespace PrincipalApplicationFamilySource

variable {routing blockSource interpretation}
variable (sources : PrincipalApplicationFamilySource routing blockSource interpretation)

/-- Construct each principal bijection from the source appropriate to its
rank. The higher rank construction retains the interpretation for every
admissible choice of roots. -/
def completedPrincipalSeeds : PrincipalBlockBijections routing blockSource where
  atPrincipal pair block coordinates carrier := by
    by_cases rankTwo : (routing.pairSource pair).rank = 2
    · exact ⟨(sources.rankTwo pair block coordinates carrier rankTwo).seed⟩
    · have rankThree : 3 ≤ (routing.pairSource pair).rank := by
        have rankAtLeastTwo := carrier.rankAtLeastTwo
        omega
      let family := (coverage.presentation pair).family
      let input := interpretation.blockSemantics pair
      let I := (sources.higherRank pair block coordinates carrier rankThree).toFamilyInputs
      letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
      exact ⟨(completedAt family block carrier input (interpretation.standard pair) I
        (blockSource.automorphisms pair block) (blockSource.source pair block)
        (ModularRep.PaperProofs.OddTwoPrincipalFamilyAuthenticInterpretation.authenticInterpretation
          scope coverage blockSource strictSource interpretation pair block carrier
          I.operations I.dictionary I.published.standardTransport)).seed⟩

variable (typeA : ∀ (pair : FullHG scope)
    (presentation : TypeAActualPresentation pDef (routing.pairSource pair).rank
      (coverage.presentation pair).family.H),
    TypeAApplicationData (coverage.presentation pair).family presentation
      (blockSource.automorphisms pair) (blockSource.source pair))

include sources typeA in
/-- Classify each strictly quasi-isolated block, then use the Type A result
or the principal bijection on that same block. -/
theorem strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource where
  iBAWBijection pair block hstrict := by
    rcases routing.strictBlock_typeA_or_principal pair block hstrict with hA | hC
    · obtain ⟨presentation⟩ := hA
      exact (typeA pair presentation).blockWitness scope.definingPrime
        scope.distinctPrimes (routing.pairSource pair).rankPositive block
    · obtain ⟨coordinates, ⟨carrier⟩⟩ := hC
      exact sources.completedPrincipalSeeds.atPrincipal pair block coordinates carrier

end PrincipalApplicationFamilySource

end FullFamily

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
