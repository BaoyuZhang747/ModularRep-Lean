import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedPairs

/-! The same-Omega Q=1 and positive-radical branches with canonical
reductions. The existing literal target record is reused, but the general
branch uses only the fixed-root Späth constructor. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalNormalizedPairs

open Formalisation ModularRep
open ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.NavarroBrauerRestrictionCovering
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathSource
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedPairs

universe u
local instance outerFinite {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

theorem exists_normalized_named_pair_of_canonical_sources
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (b : ActualBlock (k := k) (X := X))
    (P : Definition35Problem.{u})
    (hP : P = blockProblem iota hinj R (canonicalSelectedReduction iota R C) b)
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
    (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
    (catalogues : BlockCatalogues P M S hcenter reference haut)
    (D : SporadicCompleteCollapseLemma52Actual.DefectZeroReductionSource P.iota)
    (T : SporadicCompleteCollapseLemma52Actual.TrivialWeightSource (p := P.p) (X := P.H))
    (hOmegaOne : ∀ d : SporadicCompleteCollapseLemma52Actual.GlobalDefectZeroCharacter
        (p := P.p) (K := P.K) (X := P.H),
      M.Omega (D.reduce (iota := P.iota) d) = T.atOne d) :
    Nonempty (NormalizedNamedPairWitness P M S hcenter reference haut) := by
  classical
  have hgeneral : Nonempty (NamedMatchedPairWitness P M S hcenter reference haut) := by
    obtain ⟨pair⟩ := namedMatchedPairWitness_of_canonical_sources
      iota hinj R C b P hP M S hcenter reference haut
      principle S9295 S9495 S820 seed fieldSource compatibility catalogues
    exact ⟨{ clause3 := pair.clause3, spath := pair.spath }⟩
  have hOne := fun hQ => exists_qOne_named_pair P M S hcenter reference haut
    principle seed fieldSource catalogues D T hOmegaOne hQ
  let pair : NamedMatchedPairWitness P M S hcenter reference haut :=
    if hQ : selectedRadical P M.weight = ⊥ then Classical.choose (hOne hQ)
    else Classical.choice hgeneral
  refine ⟨{ pair := pair, qOne := ?_ }⟩
  intro hQ
  dsimp only [pair]
  rw [dif_pos hQ]
  exact Classical.choose_spec (hOne hQ)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalNormalizedPairs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
