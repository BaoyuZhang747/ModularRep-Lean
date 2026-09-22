import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCharacters
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneGlobal
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathWitness

/-!
# The actual Q=1 packet with equal chosen ambient extensions

The normalized correspondence supplies the base-character identity.
Choose one global extension, use it for both sides, and derive all
intermediate block equalities on that same packet.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneWitness

open ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathSource
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathWitness
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCharacters
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneExtensions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneGlobal

universe u

local instance outerFinite {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

def GlobalLocalExtensionsAgree
    {P : Definition35Problem.{u}} {reference psi : Definition35Brauer P}
    {w : Definition35Weight P} (packet : SpathMatchedBlockCondition P reference psi w) : Prop :=
  PrimeRegularClassFunction.pullback
    (AmbientLocalGroup P reference psi w packet.quotient packet.ambient).subtype
      packet.extensions.globalExtension.1.1 = packet.extensions.localExtension.1.1

theorem exists_qOne_named_pair
    (P : Definition35Problem.{u}) (M : EquivariantMatch P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (hcenter : Subgroup.center P.H = ⊥) (reference : Definition35Brauer P)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K (GTheta P M S))
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (catalogues : BlockCatalogues P M S hcenter reference haut)
    (D : DefectZeroReductionSource P.iota)
    (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOmegaOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      M.Omega (D.reduce (iota := P.iota) d) = T.atOne d)
    (hQ : selectedRadical P M.weight = ⊥) :
    ∃ witness : NamedMatchedPairWitness P M S hcenter reference haut,
      GlobalLocalExtensionsAgree witness.spath := by
  obtain ⟨localInflation, _fixedLocal, globalChoice, _source⟩ :=
    exists_cyclic_inputs P M S hcenter reference haut principle seed fieldSource catalogues
  let localData := qOneLocalDataOfNormalizedMatch P M hcenter reference D T hOmegaOne hQ
    localInflation (Ambient P M S hcenter reference haut)
  let extensions := characterExtensionsOfGlobal globalChoice localData
  let allJ := intermediateBlocksOfSelectedAmbient P M S hcenter reference haut
    globalChoice localData catalogues.ambientBlocks catalogues.ambientCharacters fieldSource
  let packet : SpathMatchedBlockCondition P reference M.theta M.weight := {
    quotient := SelectedCentralQuotient P hcenter reference M.theta
    tail := {
      weight := SelectedWeight P M hcenter reference
      localInflation := localInflation
      ambient := Ambient P M S hcenter reference haut
      extensions := extensions
      intermediateBlocks := allJ } }
  obtain ⟨clause3⟩ := namedClause3Witness_of_equivariantMatch P M S hcenter haut principle
  refine ⟨{ clause3 := clause3, spath := packet }, ?_⟩
  exact global_restriction_eq_local globalChoice localData

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
