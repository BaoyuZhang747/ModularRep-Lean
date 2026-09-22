import ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding
import ModularRep.PaperProofs.TypeBWeightCoveringSplittingSource

/-!
# Principal weight counting on the literal dimension-seven groups over ZMod 3

The published covering data is indexed by the actual principal SO and Omega
weight fibres. Its covering relation uses the intermediate quotients, local
ordinary characters and calibrated selectors of one splitting modular system.
The SO actor is the existing conjugation permutation. The existing index-two
covering arithmetic derives its cardinality and fixed-point count.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3PrincipalWeightBinding

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelPrincipalStability
open TypeBRankThreePrincipalCountBinding
open TypeBExceptionalQ3Proposition416Relative

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable [HasEnoughRootsOfUnity K (Nat.card (H (ZMod 3)))]

/-- The q=3 specialization of the published principal covering rule.
The specified idempotents, principal guards and noninner SO coset remain
explicit indices. The ten SO classes use the independent principal weight
classification in Feng--Yu--Zhang, Lemma 5.7, and the odd-dimensional
I-to-SO nonsplitting step; the covering and splitting parameters use the proof of Proposition
5.11. Movement in a split fibre uses its actual SO-orbit assertion.

The literal quadratic form has the opposite discriminant normalization to
that proof. Scalar normalization, any resulting permutation of the parameter
labels, and the source-to-specified principal-class identification remain
explicit E2/U obligations of this exact literal-carrier certificate. No
inhabitant is supplied by the numerical transcript. The exact calibrated
local covering relation prevents an independent relabelling of its fibres.
The source-to-specified identification includes the original S and SH local
block and inflation selectors; the ambient idempotent equalities alone do
not establish their interpretation. -/
structure PublishedWeightCovering
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
    (delta : H (ZMod 3)) (indexTwo : (G (ZMod 3)).index = 2)
    (outside : delta ∉ G (ZMod 3))
    (SH : SOWeightSource (k := k) (K := K) (ZMod 3))
    (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
    (bH : LiteralPrimitiveBlock k (H (ZMod 3))) (hbH : IsPrincipal bH)
    [Fintype (OmegaWeight (ZMod 3) S b)]
    [DecidableEq (OmegaWeight (ZMod 3) S b)]
    [Fintype (SOWeight (ZMod 3) SH bH)]
    [DecidableEq (SOWeight (ZMod 3) SH bH)]
    (Msys : ModularSystem 2 K O k)
    (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G (ZMod 3)) Msys) where
  splits : SOWeight (ZMod 3) SH bH → Prop
  splitsDecidable : DecidablePred splits
  splittingParametrisation :
    {w : SOWeight (ZMod 3) SH bH // splits w} ≃ SplittingParameterIndex
  cover : OmegaWeight (ZMod 3) S b → SOWeight (ZMod 3) SH bH
  covers_iff : ∀ (h : SOWeight (ZMod 3) SH bH) (w : OmegaWeight (ZMod 3) S b),
    TypeBWeightCoveringSplittingSource.CoversClass (G (ZMod 3)) dgn h.val w.val ↔
      cover w = h
  cover_surjective : Function.Surjective cover
  cover_action : ∀ w,
    cover (weightPermutation (ZMod 3) S literal b hb delta indexTwo w) = cover w
  fibre_card : ∀ w,
    Fintype.card {v : OmegaWeight (ZMod 3) S b // cover v = w} =
      if splits w then 2 else 1
  split_weights_are_moved : ∀ w,
    splits (cover w) →
      weightPermutation (ZMod 3) S literal b hb delta indexTwo w ≠ w
  soWeight_card : Fintype.card (SOWeight (ZMod 3) SH bH) = 10

variable
  (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
  (delta : H (ZMod 3)) (indexTwo : (G (ZMod 3)).index = 2)
  (outside : delta ∉ G (ZMod 3))
  (SH : SOWeightSource (k := k) (K := K) (ZMod 3))
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (bH : LiteralPrimitiveBlock k (H (ZMod 3))) (hbH : IsPrincipal bH)
  [Fintype (OmegaWeight (ZMod 3) S b)]
  [DecidableEq (OmegaWeight (ZMod 3) S b)]
  [Fintype (SOWeight (ZMod 3) SH bH)]
  [DecidableEq (SOWeight (ZMod 3) SH bH)]
  (Msys : ModularSystem 2 K O k)
  (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G (ZMod 3)) Msys)
  (covering : PublishedWeightCovering S literal b hb delta indexTwo outside
    SH literalH bH hbH Msys dgn)

/-- Bind the existing covering arithmetic to the same actual SO action.
Its involutivity follows from the index-two inclusion and inner fixation. -/
def coveringInput : PrincipalWeightCoveringInput
    (SOWeight (ZMod 3) SH bH) (OmegaWeight (ZMod 3) S b) where
  splits := covering.splits
  splitsDecidable := covering.splitsDecidable
  splittingParametrisation := covering.splittingParametrisation
  cover := covering.cover
  cover_surjective := covering.cover_surjective
  weightAction := weightPermutation (ZMod 3) S literal b hb delta indexTwo
  weightAction_involutive := weightStep_involutive (ZMod 3) S literal b hb delta indexTwo
  cover_action := covering.cover_action
  fibre_card := covering.fibre_card
  split_weights_are_moved := covering.split_weights_are_moved
  hWeight_card := covering.soWeight_card

@[simp]
theorem coveringInput_weightAction :
    (coveringInput S literal b hb delta indexTwo outside SH literalH bH hbH
      Msys dgn covering).weightAction =
      weightPermutation (ZMod 3) S literal b hb delta indexTwo := rfl

include covering in
/-- Twelve actual principal Omega weight classes, with eight fixed by the
same noninner SO coset, follow from the calibrated published covering rule. -/
theorem principalWeight_action_signature :
    (Fintype.card (OmegaWeight (ZMod 3) S b),
      Fintype.card (Function.fixedPoints
        (weightPermutation (ZMod 3) S literal b hb delta indexTwo))) = (12, 8) :=
  (coveringInput S literal b hb delta indexTwo outside SH literalH bH hbH
    Msys dgn covering).principalWeight_action_signature

end ModularRep.PaperProofs.TypeBQ3PrincipalWeightBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
