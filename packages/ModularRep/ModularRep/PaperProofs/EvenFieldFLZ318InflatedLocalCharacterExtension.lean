import ModularRep.PaperProofs.EvenFieldFLZ318CharacterExtensions

/-!
# Inflating the local Brauer-character extension to the pair stabiliser

The quotient-level result in `EvenFieldFLZ318CharacterExtensions` constructs
an irreducible Brauer character on the quotient pair stabiliser.  The
representation-level construction in `EvenFieldFLZ318SelfCover` pulls its
chosen extension back to the full pair stabiliser.  This module joins those
two constructions at character level.

The conclusion contains an actual irreducible Brauer character on the
embedded local subgroup, equal as a class function to the inflation of the
prescribed local Brauer character, and an actual irreducible Brauer character
of the full pair stabiliser restricting to it.  The three compatibility
premises supply sufficient root-lift coherence at the quotient restriction,
the quotient inflation, and the local inflation.

This is a theorem about the project's literal pair-stabiliser model.  It does
not identify that model and its selected character with every source-level
object in Feng--Li--Zhang, Theorem 3.18(iv)(b), and it does not assert the
remaining source hypotheses or the theorem's final conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZ318InflatedLocalCharacterExtension

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge

universe u

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (field : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks field block)
variable (quotientInput : RawNormalizerQuotientInput
  (p := p) (K := K) (H := H))
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)

/-- The quotient local extension and the representation-level inflation give
an actual irreducible Brauer character of the full pair stabiliser.  Its
restriction to the embedded `H`-local subgroup is the actual irreducible
Brauer character whose underlying class function is the inflation of the
prescribed quotient-local Brauer character.

The returned quotient witness is included to expose the precise character
being inflated.  The final equality says that the ambient character is its
literal pullback along the quotient map. -/
theorem localBrauerCharacterExtension_inflate_of_cyclicEndgame
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      quotientInput localReduction)
    (psi : BrauerFibre iota hinj blocks block) :
    let w := endgame.omega.toEquiv psi
    letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        quotientInput w
    ∀ (iotaQuotient : PrimeRegularRootEmbedding p k K
        (PairStabilizer field blockSource block w ⧸
          EmbeddedRadical field blockSource block quotientInput w))
      (iotaPair : PrimeRegularRootEmbedding p k K
        (PairStabilizer field blockSource block w))
      (iotaEmbeddedLocal : PrimeRegularRootEmbedding p k K
        (EmbeddedPairHStabilizer field blockSource block w)),
      (∀ (W : FDRep k (LocalBase field blockSource block quotientInput w))
        (extension : Representation.Extension
          (LocalBase field blockSource block quotientInput w) W.ρ),
        Representation.BrauerRootLiftCompatibleAlong
          extension.representation iotaQuotient
          (transportedLocalRootEmbedding
            field blockSource block quotientInput w (localReduction w))
          (LocalBase field blockSource block quotientInput w).subtype) →
      (∀ (W : FDRep k (LocalBase field blockSource block quotientInput w))
        (extension : Representation.Extension
          (LocalBase field blockSource block quotientInput w) W.ρ),
        Representation.BrauerRootLiftCompatibleAlong
          extension.representation iotaQuotient iotaPair
          (QuotientGroup.mk'
            (EmbeddedRadical field blockSource block quotientInput w))) →
      (∀ W : FDRep k (LocalBase field blockSource block quotientInput w),
        Representation.BrauerRootLiftCompatibleAlong W.ρ
          (transportedLocalRootEmbedding
            field blockSource block quotientInput w (localReduction w))
          iotaEmbeddedLocal
          (subgroupToQuotientImage
            (EmbeddedRadical field blockSource block quotientInput w)
            (EmbeddedPairHStabilizer field blockSource block w))) →
      ∃ quotientWitness :
          Representation.Extension.BrauerCharacterExtensionWitness
            iotaQuotient
            (transportedLocalRootEmbedding
              field blockSource block quotientInput w (localReduction w))
            (transportedLocalBrauer
              field blockSource block quotientInput w (localReduction w)),
        ∃ inflatedLocal : IBr iotaEmbeddedLocal,
          inflatedLocal.1 =
              PrimeRegularClassFunction.pullback
                (subgroupToQuotientImage
                  (EmbeddedRadical field blockSource block quotientInput w)
                  (EmbeddedPairHStabilizer field blockSource block w))
                (transportedLocalBrauer
                  field blockSource block quotientInput w
                    (localReduction w)).1 ∧
          ∃ pairWitness :
              Representation.Extension.BrauerCharacterExtensionWitness
                iotaPair iotaEmbeddedLocal inflatedLocal,
            pairWitness.1.1 =
              PrimeRegularClassFunction.pullback
                (QuotientGroup.mk'
                  (EmbeddedRadical field blockSource block quotientInput w))
                quotientWitness.1.1 := by
  dsimp only
  let w := endgame.omega.toEquiv psi
  letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := field) (blockSource := blockSource) (block := block)
      quotientInput w
  intro iotaQuotient iotaPair iotaEmbeddedLocal
    quotientCompatible pairInflationCompatible localInflationCompatible
  rcases endgame.local_extension psi with
    ⟨W, hW, hcharacter, _hreduction, ⟨extension⟩⟩
  let localIota := transportedLocalRootEmbedding
    field blockSource block quotientInput w (localReduction w)
  let localBrauer := transportedLocalBrauer
    field blockSource block quotientInput w (localReduction w)
  let Q := EmbeddedRadical field blockSource block quotientInput w
  let N := EmbeddedPairHStabilizer field blockSource block w
  let f := subgroupToQuotientImage Q N
  let q := QuotientGroup.mk' Q
  let quotientWitness :
      Representation.Extension.BrauerCharacterExtensionWitness
        iotaQuotient localIota localBrauer :=
    Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
      extension hW iotaQuotient localIota localBrauer hcharacter.symm
        (quotientCompatible W extension)
  have hf : Function.Surjective f := by
    intro y
    rcases y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let inflatedLocal : IBr iotaEmbeddedLocal := by
    refine ⟨PrimeRegularClassFunction.pullback f localBrauer.1, ?_⟩
    refine ⟨FDRep.of (Representation.pullback W.ρ f),
      hW.pullback f hf, ?_⟩
    rw [FDRep.of_ρ']
    calc
      PrimeRegularClassFunction.pullback f localBrauer.1 =
          PrimeRegularClassFunction.pullback f
            (Representation.brauerCharacterOfRootEmbedding W.ρ localIota) :=
        congrArg (PrimeRegularClassFunction.pullback f) hcharacter
      _ = (Representation.pullback W.ρ f).brauerCharacterOfRootEmbedding
          iotaEmbeddedLocal :=
        (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
          W.ρ localIota iotaEmbeddedLocal f
            (localInflationCompatible W)).symm
  let inflatedExtension := inflateQuotientExtension Q N W.ρ extension
  let pairBrauer : IBr iotaPair := by
    refine ⟨PrimeRegularClassFunction.pullback q quotientWitness.1.1, ?_⟩
    refine ⟨FDRep.of inflatedExtension.representation,
      inflateQuotientExtension_isIrreducible Q N W.ρ extension hW, ?_⟩
    rw [FDRep.of_ρ']
    change PrimeRegularClassFunction.pullback q quotientWitness.1.1 =
      Representation.brauerCharacterOfRootEmbedding
        (Representation.pullback extension.representation q) iotaPair
    calc
      PrimeRegularClassFunction.pullback q quotientWitness.1.1 =
          PrimeRegularClassFunction.pullback q
            (Representation.brauerCharacterOfRootEmbedding
              extension.representation iotaQuotient) := rfl
      _ = Representation.brauerCharacterOfRootEmbedding
          (Representation.pullback extension.representation q) iotaPair :=
        (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
          extension.representation iotaQuotient iotaPair q
            (pairInflationCompatible W extension)).symm
  have hpullback :
      PrimeRegularClassFunction.pullback N.subtype pairBrauer.1 =
        inflatedLocal.1 := by
    change PrimeRegularClassFunction.pullback N.subtype
        (PrimeRegularClassFunction.pullback q quotientWitness.1.1) =
      PrimeRegularClassFunction.pullback f localBrauer.1
    calc
      PrimeRegularClassFunction.pullback N.subtype
          (PrimeRegularClassFunction.pullback q quotientWitness.1.1) =
        PrimeRegularClassFunction.pullback f
          (PrimeRegularClassFunction.pullback
            (LocalBase field blockSource block quotientInput w).subtype
            quotientWitness.1.1) := by
          apply PrimeRegularClassFunction.ext
          intro n
          rfl
      _ = PrimeRegularClassFunction.pullback f localBrauer.1 :=
        congrArg (PrimeRegularClassFunction.pullback f) quotientWitness.2
  let pairWitness :
      Representation.Extension.BrauerCharacterExtensionWitness
        iotaPair iotaEmbeddedLocal inflatedLocal := ⟨pairBrauer, hpullback⟩
  exact ⟨quotientWitness, inflatedLocal, rfl, pairWitness, rfl⟩

end ModularRep.PaperProofs.EvenFieldFLZ318InflatedLocalCharacterExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
