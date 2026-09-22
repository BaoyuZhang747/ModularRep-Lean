import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction
import ModularRep.PaperProofs.CyclicOuterLocalRepresentationInflation
import ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier

/-!
# The selected Fischer local representation extension

This module applies the cyclic extension theorem to a selected Fischer raw
weight and inflates the resulting quotient representation to the literal pair
stabiliser. The conclusion remains at representation level. It does not assert
the root compatibility needed for a Brauer-character extension witness and it
contains no block equality, BAW, or iBAW conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalRepresentationExtension

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

noncomputable local instance selectedOuterFiniteForLocalExtension
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _a _b h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

/-- The selected quotient-local extension, inflated to an actual
representation extension from the embedded pair base to the raw-pair
stabiliser. Fixedness and cyclicity are derived internally. -/
theorem selectedPairLocalRepresentationExtension
    (P : Definition35Problem.{u})
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (w : Definition35Weight P) :
    InflatedLocalRepresentationExtensionConclusion
      (phi := selectedOuterField S)
      (blockSource := P.blockSource)
      (block := P.block)
      (quotientInput := canonicalRawNormalizerQuotientInput
        (p := P.p) (K := P.K) (H := P.H))
      w (P.localReduction w) := by
  exact inflate_localExtensionConclusion
    (phi := selectedOuterField S)
    (blockSource := P.blockSource)
    (block := P.block)
    (quotientInput := canonicalRawNormalizerQuotientInput
      (p := P.p) (K := P.K) (H := P.H))
    w (P.localReduction w)
    (selectedLiteralLocalExtension
      (phi := selectedOuterField S)
      (blockSource := P.blockSource)
      (block := P.block)
      (canonicalRawNormalizerQuotientInput
        (p := P.p) (K := P.K) (H := P.H))
      principle w (P.localReduction w))

end ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalRepresentationExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
