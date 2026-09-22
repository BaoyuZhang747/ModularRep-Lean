import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCyclicBlockChoice
import ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport

/-!
# The base block relation from the literal operations

The lower operations-wide reduction/inflation law identifies the selected
local block. Together with the common block fibre, it derives the one base
induction relation used by the cyclic block choice. No induction relation is
an input to the constructor or the resulting intermediate-block theorem.
-/

noncomputable section

-- The concrete operations problem unfolds several dependent carrier records.
set_option maxHeartbeats 1200000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOperationsBlock

open Formalisation ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock
open ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCyclicBlockChoice

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

local instance blockStabilizerFinite {k X : Type u} [Field k] [Group X] [Finite X]
    (b : ActualBlock (k := k) (X := X)) : Finite (BlockStabilizer b) :=
  Finite.of_injective (fun a : BlockStabilizer b ↦ (a.1.unop : X → X))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (localReduction :
  ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
    SelectedLocalReductionSource R.1 b w)
variable (b : ActualBlock (k := k) (X := X))

variable (P : Definition35Problem.{u})
variable (hP : P = blockProblem iota hinj R localReduction b)

variable (hcenter : Subgroup.center P.H = ⊥)
variable {reference psi : Definition35Brauer P} {w : Definition35Weight P}
variable {weight : QuotientWeightBrauerSource P reference w}
variable {localInflation : QuotientLocalInflationSource P reference w weight}
variable {ambient : SpathAmbientGroup P reference psi
  (centerlessCentralQuotientBrauerSourceFromReference P hcenter reference psi)}

def baseBlockOfOperations
    (extensions : SpathCharacterExtensions P reference psi w
      (centerlessCentralQuotientBrauerSourceFromReference P hcenter reference psi)
      weight localInflation ambient)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source P.blockSource.operations)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime) :
    BaseBlockInducesFromSelectedWeight extensions := by
  let base := baseBlockCatalogueDataOfOperations hcenter extensions
  refine {
    GlobalBlock := base.GlobalBlock
    LocalBlock := base.LocalBlock
    fintypeGlobalBlock := base.fintypeGlobalBlock
    fintypeLocalBlock := base.fintypeLocalBlock
    globalBlockIdempotent := base.globalBlockIdempotent
    localBlockIdempotent := base.localBlockIdempotent
    globalBlocks := base.globalBlocks
    localBlocks := base.localBlocks
    globalBrauerInjective := base.globalBrauerInjective
    localBrauerInjective := base.localBrauerInjective
    globalCentralCharacters := base.globalCentralCharacters
    localCentralCharacters := base.localCentralCharacters
    globalCentralCharactersNavarro311 := { fieldSource := fieldSource }
    localCentralCharactersNavarro311 := { fieldSource := fieldSource }
    inductionEquality := ?_ }
  subst P
  exact baseBlockInducesTo_ofOperations_centerless_of_compatibility
    (iota := iota) (hinj := hinj) (blockSource := R.1) (block := b)
    (gamma := blockField b) (gammaBlock_fixed := blockField_fixed b)
    (brauerSupport := literalOperationsBrauerSupport iota hinj R)
    (localReduction := localReduction b) hcenter extensions compatibility

theorem exists_extensions_and_intermediate_blocks_of_operations
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K)
    (S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K)
    (fixedLocal : FixedLocalExtensionData localInflation ambient)
    (initialGlobal : ChosenGlobalExtensionData ambient)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source P.blockSource.operations)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (source : CyclicBlockSource fixedLocal initialGlobal
      (baseBlockOfOperations iota hinj R localReduction b P hP hcenter
        (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal) compatibility fieldSource)) :
    ∃ extensions : SpathCharacterExtensions P reference psi w
        (centerlessCentralQuotientBrauerSourceFromReference P hcenter reference psi)
        weight localInflation ambient,
      Nonempty (IntermediateBlockSource P reference psi w
        (centerlessCentralQuotientBrauerSourceFromReference P hcenter reference psi)
        weight localInflation ambient extensions) :=
  exists_extensions_and_intermediate_blocks S9295 S9495 S820 fixedLocal initialGlobal
    (baseBlockOfOperations iota hinj R localReduction b P hP hcenter
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal) compatibility fieldSource) source

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOperationsBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
