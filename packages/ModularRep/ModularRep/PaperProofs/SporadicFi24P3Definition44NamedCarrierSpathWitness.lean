import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOperationsBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathSource

/-!
# The literal matched-pair Späth packet from lower sources

The global and local extensions and every intermediate block equality are
constructed together on the canonical centreless quotient. The only problem
alignment is equality with the literal operations problem; its concrete
instances use reflexivity. No radical case is removed.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathWitness

open Formalisation ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.NavarroBrauerRestrictionCovering
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOperationsBlock
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathSource

universe u

local instance outerFinite {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

theorem spathMatchedBlockCondition_of_sources
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (localReduction :
      ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
        SelectedLocalReductionSource R.1 b w)
    (b : ActualBlock (k := k) (X := X))
    (P : Definition35Problem.{u})
    (hP : P = blockProblem iota hinj R localReduction b)
    (M : EquivariantMatch P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (hcenter : Subgroup.center P.H = ⊥) (reference : Definition35Brauer P)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K)
    (S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K (GTheta P M S))
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source P.blockSource.operations)
    (catalogues : BlockCatalogues P M S hcenter reference haut) :
    Nonempty (SpathMatchedBlockCondition P reference M.theta M.weight) := by
  obtain ⟨localInflation, fixedLocal, initialGlobal, mkSource⟩ :=
    exists_cyclic_inputs P M S hcenter reference haut principle seed fieldSource catalogues
  let base := baseBlockOfOperations iota hinj R localReduction b P hP hcenter
    (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal) compatibility fieldSource
  obtain ⟨source⟩ := mkSource base
  obtain ⟨extensions, ⟨allJ⟩⟩ := exists_extensions_and_intermediate_blocks_of_operations
    iota hinj R localReduction b P hP hcenter S9295 S9495 S820
    fixedLocal initialGlobal compatibility fieldSource source
  exact ⟨{
    quotient := SelectedCentralQuotient P hcenter reference M.theta
    tail := {
      weight := SelectedWeight P M hcenter reference
      localInflation := localInflation
      ambient := Ambient P M S hcenter reference haut
      extensions := extensions
      intermediateBlocks := allJ } }⟩

/-- Both concrete outputs are indexed by the same selected pair and Omega. -/
structure NamedMatchedPairWitness
    (P : Definition35Problem.{u}) (M : EquivariantMatch P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (hcenter : Subgroup.center P.H = ⊥) (reference : Definition35Brauer P)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S))) where
  clause3 : NamedClause3Witness P M S hcenter haut
  spath : SpathMatchedBlockCondition P reference M.theta M.weight

theorem namedMatchedPairWitness_of_sources
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (localReduction :
      ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
        SelectedLocalReductionSource R.1 b w)
    (b : ActualBlock (k := k) (X := X))
    (P : Definition35Problem.{u})
    (hP : P = blockProblem iota hinj R localReduction b)
    (M : EquivariantMatch P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (hcenter : Subgroup.center P.H = ⊥) (reference : Definition35Brauer P)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K)
    (S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K (GTheta P M S))
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source P.blockSource.operations)
    (catalogues : BlockCatalogues P M S hcenter reference haut) :
    Nonempty (NamedMatchedPairWitness P M S hcenter reference haut) := by
  obtain ⟨clause3⟩ := namedClause3Witness_of_equivariantMatch P M S hcenter haut principle
  obtain ⟨spath⟩ := spathMatchedBlockCondition_of_sources
    iota hinj R localReduction b P hP M S hcenter reference haut
    principle S9295 S9495 S820 seed fieldSource compatibility catalogues
  exact ⟨{ clause3 := clause3, spath := spath }⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
