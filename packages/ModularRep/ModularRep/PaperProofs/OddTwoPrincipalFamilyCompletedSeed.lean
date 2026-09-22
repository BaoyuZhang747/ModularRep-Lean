import ModularRep.PaperProofs.OddTwoPrincipalFamilySeedTransport
import ModularRep.PaperProofs.OddTwoPrincipalFamilyCommonRoots
import ModularRep.PaperProofs.OddTwoPrincipalPublishedInputs

/-!
# Constructing the completed principal packet on the fixed family

The source data below contain only the actual primitive dictionary, fixed
family root-table convention, and the existing published playlist on the
computed D. The completed packet, orbit correction and carrier transport
are outputs. The authentic meaning is a separate explicit K argument here;
the Full-HG consumer derives it from its fixed interpretation.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilyCompletedSeed

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
open ModularRep.PaperProofs.OddTwoPrincipalFamilySelectedReduction
open ModularRep.PaperProofs.OddTwoPrincipalFamilyFibreActions
open ModularRep.PaperProofs.OddTwoPrincipalFamilySeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCommonRoots
open ModularRep.PaperProofs.OddTwoPrincipalPublishedInputs
open ModularRep.PaperProofs.OddTwoPrincipalDefinition35Covariance
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)
variable (input : TypeAInputSemantics family)
variable (standard : BlockTripleSourceSemantics 2 family.k family.K)

local instance completedFamilySpFintype : Fintype (Sp rank F) := Fintype.ofFinite _

/-- The permitted existing inputs on the actual computed family data.
There is no completed supplier, intrinsic meaning, selected transport,
correction input, orbit witness, covariance or seed field. -/
structure FamilyInputs where
  operations : LocalBlockInductionOperations
    (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block)
  dictionary : PrimitiveDictionary family.blockSource.operations operations
    (groupEquiv family block carrier)
  commonRoots : FamilyCommonRootConvention family block carrier
  published :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    PublishedInputs (data family block carrier input operations dictionary) standard

variable (S : FamilyInputs family block carrier input standard)
variable (adapter : Definition35AutomorphismStabilizerAdapter (family.problem block))
variable (source : FLZSourceSemantics (family.problem block) adapter)

/-- K: all fields of CompletedPrincipalSeedAt are supplied by the exact
computed data, selected table, correction engine and inverse carrier map.
The same meaning argument is consumed by both engine relation lanes. -/
def completedAt
    (meaning :
      letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
      AuthenticDefinition35Interpretation
        (data family block carrier input S.operations S.dictionary)
        (selectedReduction family block carrier input S.operations S.dictionary)
        (intrinsicSource family block carrier input S.operations S.dictionary
          (selectedReduction family block carrier input S.operations S.dictionary) adapter source)
        standard) :
    CompletedPrincipalSeedAt family block adapter source rank F carrier := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  let D := data family block carrier input S.operations S.dictionary
  let reduction := selectedReduction family block carrier input S.operations S.dictionary
  let flz := intrinsicSource family block carrier input S.operations S.dictionary
    reduction adapter source
  let convention := S.published.commonRootConvention reduction
    (intrinsic_selected_root family block carrier input S.operations S.dictionary S.commonRoots)
  exact
    { SpBlock := family.Block
      blockAction := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
      data := D
      reduction := reduction
      FM := S.published.FM
      principalSource := flz
      correction := S.published.correctionInput reduction convention flz meaning
      transport := carrierTransport family block carrier input S.operations S.dictionary
        reduction adapter source
      group_coordinates := rfl
      coefficients_identity := rfl }

end ModularRep.PaperProofs.OddTwoPrincipalFamilyCompletedSeed


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
