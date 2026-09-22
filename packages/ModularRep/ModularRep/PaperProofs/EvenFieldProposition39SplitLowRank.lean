import ModularRep.PaperProofs.EvenFieldConcreteTypeC
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.EvenFieldFLZFullHG
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource

/-!
# The split low rank branches in even characteristic

This module isolates the cited whole-family input for the split groups of
type `C_2` and `C_3` over fields of size at least four in Proposition 3.9.
The finite group and its complete block family are the literal presentation
of one certified member of `FullHG`.

The project has no algebraic-group carrier capable of deriving that a given
certified pair is the split group of the displayed rank over `F_(2^a)` or
that the presented group is the full universal cover used in the cited proof.
These facts remain explicit E1/U data.  The field `fixedPointModel` identifies
the certified fixed point group with the literal finite symplectic fixed point
carrier, `cover` fixes the exact universal prime-to-`ell` cover, and
`fullUniversalCover` certifies that `cover.quotient` is a full universal
central extension.

The source result is split into two E2/U inputs.  Schaeffer Fry, Theorem 5.5,
supplies a complete Definition 4.1 packet whose BAW-good relation uses the
cited character triple formulation.  The separate
`FLZBAWGoodToDefinition35FamilySource` supplies the implication from its
BAW-good relation to the fixed Definition 3.5 relation.  The classifier
parameter supplies the low rank branch, the field exponent, and the proof that
the exponent is at least two.  Lean preserves that exact parameter, applies its
bound together with `scope.distinctPrimes`, reuses the equivalence and
equivariance through the generic converter, and projects a selected block.
The stored bound excludes the separately treated `Sp6(2)` branches.  It is not
the full range of Schaeffer Fry's theorem.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank

open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldProposition39Relative

universe u

/-- The E2/U source operation supplied by Schaeffer Fry, Theorem 5.5, with
the BAW-good relation expressed through the cited character triple
formulation.  It returns one complete Definition 4.1 packet rather than only
its BAW-good component.  The concrete group model, universal prime-to-`ell`
cover, full universal cover certificate, actions, and relation semantics are
indices and cannot change when the theorem is used. -/
structure SchaefferFrySplitLowRankDefinition41Source {ell : Nat}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (parameter : SplitLowRankParameter)
    (hcase : classification.structuralCase coverage pair =
      .typeC (.splitLowRank parameter))
    (fixedPointModel : pair.1.algebraicPair.FixedPointGroup ≃*
      FiniteSymplecticFixed parameter.branch.rank parameter.fieldExponent)
    (cover : EllPrimeCoverSource ell (coverage.presentation pair).family.H)
    (fullUniversalCover :
      IsUniversalCentralExtension cover.quotient)
    (automorphisms : forall block : (coverage.presentation pair).family.Block,
      Definition35AutomorphismStabilizerAdapter
        ((coverage.presentation pair).family.problem block))
    (semantics : FLZBAWGoodFamilySemantics
      (coverage.presentation pair).family cover
      automorphisms)
    (globalSemantics : SpathDefinition41GlobalSemantics
      (coverage.presentation pair).family cover automorphisms semantics) : Prop where
  applyTheorem55Definition41 :
    2 <= parameter.fieldExponent ->
      ell ≠ 2 ->
        Nonempty (SpathDefinition41FamilyWitness globalSemantics)

/-- The complete source packet for one split low rank branch.  It separates
the E1/U concrete model, universal prime-to-`ell` cover, and full universal
cover certificate from the E2/U Definition 4.1 source and the E2/U
implication to the fixed Definition 3.5 relation. -/
structure SchaefferFrySplitLowRankFamilySource {ell : Nat}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (parameter : SplitLowRankParameter)
    (hcase : classification.structuralCase coverage pair =
      .typeC (.splitLowRank parameter))
    (automorphisms : forall block : (coverage.presentation pair).family.Block,
      Definition35AutomorphismStabilizerAdapter
        ((coverage.presentation pair).family.problem block))
    (source : forall block : (coverage.presentation pair).family.Block,
      FLZSourceSemantics ((coverage.presentation pair).family.problem block)
        (automorphisms block)) : Type (u + 1) where
  fixedPointModel : pair.1.algebraicPair.FixedPointGroup ≃*
    FiniteSymplecticFixed parameter.branch.rank parameter.fieldExponent
  cover : EllPrimeCoverSource ell (coverage.presentation pair).family.H
  fullUniversalCover :
    IsUniversalCentralExtension cover.quotient
  semantics : FLZBAWGoodFamilySemantics (coverage.presentation pair).family cover
    automorphisms
  globalSemantics : SpathDefinition41GlobalSemantics
    (coverage.presentation pair).family cover automorphisms semantics
  definition41Source : SchaefferFrySplitLowRankDefinition41Source
    classification pair parameter hcase fixedPointModel cover
      fullUniversalCover automorphisms semantics globalSemantics
  passage : FLZBAWGoodToDefinition35FamilySource semantics source

namespace SchaefferFrySplitLowRankFamilySource

variable {ell : Nat} {scope : FLZFullHGUniverse 2 ell}
variable {coverage : FullHGDefinition35Coverage scope}
variable {classification : FullHGTypeCClassificationSource scope}
variable {pair : FullHG scope}
variable {parameter : SplitLowRankParameter}
variable {hcase : classification.structuralCase coverage pair =
  .typeC (.splitLowRank parameter)}
variable {automorphisms : forall block : (coverage.presentation pair).family.Block,
  Definition35AutomorphismStabilizerAdapter
    ((coverage.presentation pair).family.problem block)}
variable {source : forall block : (coverage.presentation pair).family.Block,
  FLZSourceSemantics ((coverage.presentation pair).family.problem block)
    (automorphisms block)}
variable (S : SchaefferFrySplitLowRankFamilySource classification pair parameter
  hcase automorphisms source)

/-- Compose the presentation equivalence with the E1/U concrete model. -/
def familyToConcrete : (coverage.presentation pair).family.H ≃*
    FiniteSymplecticFixed parameter.branch.rank parameter.fieldExponent :=
  (coverage.presentation pair).fixedPointEquiv.trans S.fixedPointModel

include S in
/-- Apply the full Definition 4.1 source to the low rank bound stored in the
classifier parameter and the distinct-prime premise supplied by the ambient
universe. -/
theorem hasDefinition41FamilyWitness :
    Nonempty (SpathDefinition41FamilyWitness S.globalSemantics) :=
  S.definition41Source.applyTheorem55Definition41
    parameter.fieldExponentAtLeastTwo scope.distinctPrimes

include S in
/-- Convert the BAW-good component of the complete Definition 4.1 packet
through the separately supplied fixed relation implication. -/
theorem hasDefinition35IBAWFamilyWitness :
    Nonempty (Definition35IBAWFamilyWitness (coverage.presentation pair).family
      automorphisms source) := by
  exact Nonempty.map
    (fun definition41 =>
      S.passage.toDefinition35Family definition41.good)
    S.hasDefinition41FamilyWitness

include S in
/-- Project one block witness from the whole-family cited result. -/
theorem blockWitness (block : (coverage.presentation pair).family.Block) :
    Nonempty (Definition35IBAWBijection
      ((coverage.presentation pair).family.problem block) (automorphisms block)
      (source block)) := by
  obtain ⟨familyWitness⟩ := hasDefinition35IBAWFamilyWitness S
  exact ⟨familyWitness.blockWitness block⟩

end SchaefferFrySplitLowRankFamilySource

end ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
