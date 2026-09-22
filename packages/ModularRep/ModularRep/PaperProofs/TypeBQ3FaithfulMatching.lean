import ModularRep.PaperProofs.TypeBExceptionalQ3CanonicalInnerRangeActual

/-! Equivariant correspondences for the four faithful block labels, using
the canonical routing and the same literal Brauer and weight output maps. -/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3FaithfulMatching

open Formalisation.ComputationArithmetic
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative
open ModularRep.PaperProofs.TypeBExceptionalQ3CanonicalInnerRangeActual

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharZero K] [Group X] [Fintype X]
variable [CharP k 2] [IsAlgClosed k]
variable {blockIdempotent : Q3Block → k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

/-- The B6/B7 matching is retained from canonical routing. The actual B8/B9
weight counts construct the other two matchings, whose equivariance follows
from fixation by the literal inner range. -/
theorem exists_faithful_actualFibreEquivs
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : ModularRep.FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (outerSource : CanonicalInnerRangeOuterInput blocks)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (brauerMap : LiteralBrauerOutputMap iota)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible :
      BrauerBlockFibreCompatible iota hinj blocks brauerMap)
    (weightMap : LiteralWeightOutputMap (K := K) (X := X))
    (weightMap_injective : Function.Injective weightMap.classOfLabel)
    (weightMap_surjective : Function.Surjective weightMap.classOfLabel)
    (sector_compatible :
      canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap
        blocks R weightMap)
    (B8_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B8)) = 2)
    (B9_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B9)) = 2) :
    ∀ block : Q3Block,
      (block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9) →
      ∃ equivalence : ActualBrauerFibre iota hinj blocks block ≃
          R.Fibre (primitiveBlockOfLabel blocks block),
        ∀ alpha : actualBlockStabilizer blocks block, ∀ phi,
          equivalence
              (brauerFibreAction iota hinj blocks
                (canonical_brauerBlock_transport blocks iota hinj)
                block alpha phi) =
            alpha • equivalence phi := by
  classical
  have large :=
    canonical_faithful_actualFibreEquivs_upToFaithfulSwap_of_innerRange
      blocks iota hinj outerSource R brauerMap brauerMap_injective
      brauerMap_surjective brauerBlock_compatible weightMap
      weightMap_injective weightMap_surjective sector_compatible
      B8_weight_fibre_card B9_weight_fibre_card
  have small : ∀ block : Q3Block,
      (block = .B8 ∨ block = .B9) →
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks block)) = 2 →
      ∃ equivalence : ActualBrauerFibre iota hinj blocks block ≃
          R.Fibre (primitiveBlockOfLabel blocks block),
        ∀ alpha : actualBlockStabilizer blocks block, ∀ phi,
          equivalence
              (brauerFibreAction iota hinj blocks
                (canonical_brauerBlock_transport blocks iota hinj)
                block alpha phi) =
            alpha • equivalence phi := by
    intro block hsmall weight_card
    let routing : WeightBlockRouting :=
      canonicalWeightBlockRouting blocks R weightMap
    have routing_compatible :
        WeightBlockFibreCompatible blocks R weightMap routing :=
      canonicalWeightBlockRouting_compatible blocks R weightMap
    have output_natCard : Nat.card (WeightOutputFibre routing block) = 2 := by
      calc
        Nat.card (WeightOutputFibre routing block) =
            Nat.card (R.Fibre (primitiveBlockOfLabel blocks block)) :=
          Nat.card_congr (weightBlockFibreEquiv blocks R weightMap routing
            weightMap_injective weightMap_surjective routing_compatible block)
        _ = 2 := weight_card
    have output_card : Fintype.card (WeightOutputFibre routing block) = 2 := by
      simpa only [← Nat.card_eq_fintype_card] using output_natCard
    have brauer_card : Fintype.card (BrauerOutputFibre block) = 2 := by
      rw [brauerOutputFibre_card]
      rcases hsmall with rfl | rfl <;> rfl
    let labelEquiv : BrauerOutputFibre block ≃ WeightOutputFibre routing block :=
      Fintype.equivOfCardEq (brauer_card.trans output_card.symm)
    let equivalence : ActualBrauerFibre iota hinj blocks block ≃
        R.Fibre (primitiveBlockOfLabel blocks block) :=
      (brauerBlockFibreEquiv iota hinj blocks brauerMap
        brauerMap_injective brauerMap_surjective brauerBlock_compatible block).symm.trans
          (labelEquiv.trans
            (weightBlockFibreEquiv blocks R weightMap routing
              weightMap_injective weightMap_surjective routing_compatible block))
    have hfaithful :
        block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9 := by
      rcases hsmall with h8 | h9
      · exact Or.inr (Or.inr (Or.inl h8))
      · exact Or.inr (Or.inr (Or.inr h9))
    refine ⟨equivalence, ?_⟩
    exact arbitrary_actualFibre_equiv_is_stabilizer_equivariant
      iota hinj blocks
      (CanonicalInnerRangeOuterInput.toC2OuterQuotientInput blocks outerSource)
      (by
        intro alpha halpha block
        change alpha ∈
          (RepresentationWeight.innerInverseOpHom (G := X)).range at halpha
        exact innerInverseOpRange_fixes_blocks alpha halpha block)
      outerSource.outer outerSource.outer_nontrivial
      outerSource.computed_outer_block_action
      (canonical_brauerBlock_transport blocks iota hinj)
      (by
        intro alpha halpha phi
        change alpha ∈
          (RepresentationWeight.innerInverseOpHom (G := X)).range at halpha
        exact innerInverseOpRange_fixes_brauer iota alpha halpha phi)
      (by
        intro alpha halpha weight
        change alpha ∈
          (RepresentationWeight.innerInverseOpHom (G := X)).range at halpha
        exact innerInverseOpRange_fixes_weight alpha halpha weight)
      R block hfaithful equivalence
  intro block hblock
  rcases hblock with rfl | rfl | rfl | rfl
  · exact large.1
  · exact large.2
  · exact small .B8 (Or.inl rfl) B8_weight_fibre_card
  · exact small .B9 (Or.inr rfl) B9_weight_fibre_card

end ModularRep.PaperProofs.TypeBQ3FaithfulMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
