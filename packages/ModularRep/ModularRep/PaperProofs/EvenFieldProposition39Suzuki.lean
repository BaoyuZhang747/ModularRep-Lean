import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.EvenFieldFLZFullHG
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource

/-!
# The Suzuki branch in even characteristic

This module gives a staged trust boundary for the Suzuki branch of
Proposition 3.9.  The finite group and its complete block family are the
literal presentation of one certified member of `FullHG`.

The project cannot yet derive from algebraic group data that the certified
pair is `^2B_2(2^(2m+1))`.  The E1/U classifier therefore returns a Suzuki
case carrying the positive parameter `m`.  Every source below is indexed by
that exact classifier equality.  Spath, Corollary 6.3, is the first E2/U
source and supplies one complete Definition 4.1 packet on the covering
family.  Both its parameter and odd-prime hypotheses are passed explicitly.
Malle, Theorem 5.1, is only a secondary summary of this Suzuki result.

The indexed application of Spath, Proposition 4.6 and Theorem 4.4, is a
second E2/U source.  A third source supplies the one-way implication from the
resulting character triple relation to the fixed Definition 3.5 relation.
Lean constructs the compatible cover map and performs the final relation
conversion.  It does not prove the Suzuki identification, the cited theorems,
or their applicability.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39Suzuki

open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldProposition39Relative

/-- The E1/U covering data for the exact Suzuki branch selected by the
structural classifier.  The branch equality ties the positive parameter to
the represented pair and its fixed target family.  The exceptional multiplier
at `^2B_2(8)` is part of the supplied cover match.  No concrete Suzuki carrier
is reconstructed in this project. -/
structure SuzukiCoverModel {ell : Nat}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (parameter : SuzukiParameter)
    (hSuzuki : classification.structuralCase coverage pair =
      .typeC (.simpleSuzuki parameter)) : Type 1 where
  coverFamily : Definition35Family ell
  coverMatch : EllPrimeCoverCentralExtensionFamilyMatch coverFamily
    (coverage.presentation pair).family
  fullUniversalCover :
    IsUniversalCentralExtension coverMatch.cover.quotient
  targetCenterless :
    Subgroup.center (coverage.presentation pair).family.H = ⊥

/-- The E2/U application of Spath, Corollary 6.3, to the exact classified
Suzuki pair, its positive parameter, its covering family, and the coefficient
prime.  The output is a complete Definition 4.1 packet on the cover, not a
final target family witness. -/
structure SpathSuzukiDefinition41Source {ell : Nat}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {classification : FullHGTypeCClassificationSource scope}
    {pair : FullHG scope}
    {parameter : SuzukiParameter}
    {hSuzuki : classification.structuralCase coverage pair =
      .typeC (.simpleSuzuki parameter)}
    (model : SuzukiCoverModel classification pair parameter hSuzuki)
    (coverAutomorphisms : ∀ block : model.coverFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (model.coverFamily.problem block))
    (coverSemantics : FLZBAWGoodFamilySemantics model.coverFamily
      model.coverMatch.cover coverAutomorphisms)
    (coverGlobalSemantics : SpathDefinition41GlobalSemantics model.coverFamily
      model.coverMatch.cover coverAutomorphisms coverSemantics) : Prop where
  applyCorollary63 : 0 < parameter.twistParameter → 2 < ell →
    Nonempty (SpathDefinition41FamilyWitness coverGlobalSemantics)

namespace SpathSuzukiDefinition41Source

/-- Select the Definition 4.1 packet supplied by Spath, Corollary 6.3. -/
noncomputable def corollary63Definition41 {ell : Nat}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {classification : FullHGTypeCClassificationSource scope}
    {pair : FullHG scope}
    {parameter : SuzukiParameter}
    {hSuzuki : classification.structuralCase coverage pair =
      .typeC (.simpleSuzuki parameter)}
    {model : SuzukiCoverModel classification pair parameter hSuzuki}
    {coverAutomorphisms : ∀ block : model.coverFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (model.coverFamily.problem block)}
    {coverSemantics : FLZBAWGoodFamilySemantics model.coverFamily
      model.coverMatch.cover coverAutomorphisms}
    {coverGlobalSemantics : SpathDefinition41GlobalSemantics model.coverFamily
      model.coverMatch.cover coverAutomorphisms coverSemantics}
    (S : SpathSuzukiDefinition41Source model coverAutomorphisms
      coverSemantics coverGlobalSemantics)
    (hparameter : 0 < parameter.twistParameter)
    (hell : 2 < ell) :
    SpathDefinition41FamilyWitness coverGlobalSemantics :=
  Classical.choice (S.applyCorollary63 hparameter hell)

end SpathSuzukiDefinition41Source

/-- The complete staged source packet for the exact classified Suzuki
branch.  Spath, Corollary 6.3, is the direct source.  Malle, Theorem 5.1, is
only a secondary summary. -/
structure SpathSuzukiFamilySource {ell : Nat}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (parameter : SuzukiParameter)
    (hSuzuki : classification.structuralCase coverage pair =
      .typeC (.simpleSuzuki parameter))
    (automorphisms : ∀ block : (coverage.presentation pair).family.Block,
      Definition35AutomorphismStabilizerAdapter
        ((coverage.presentation pair).family.problem block))
    (source : ∀ block : (coverage.presentation pair).family.Block,
      FLZSourceSemantics ((coverage.presentation pair).family.problem block)
        (automorphisms block)) : Type 1 where
  model : SuzukiCoverModel classification pair parameter hSuzuki
  coverAutomorphisms : ∀ block : model.coverFamily.Block,
    Definition35AutomorphismStabilizerAdapter
      (model.coverFamily.problem block)
  coverSemantics : FLZBAWGoodFamilySemantics model.coverFamily
    model.coverMatch.cover coverAutomorphisms
  coverGlobalSemantics : SpathDefinition41GlobalSemantics model.coverFamily
    model.coverMatch.cover coverAutomorphisms coverSemantics
  spathCorollary63 : SpathSuzukiDefinition41Source model coverAutomorphisms
    coverSemantics coverGlobalSemantics
  targetSemantics : SpathProposition46Theorem44FamilySemantics
    model.coverMatch model.fullUniversalCover model.targetCenterless
      automorphisms
  spath : ∀ (hparameter : 0 < parameter.twistParameter) (hell : 2 < ell),
    SpathProposition46Theorem44Source model.coverMatch
      model.fullUniversalCover model.targetCenterless coverAutomorphisms
      coverSemantics coverGlobalSemantics
      (spathCorollary63.corollary63Definition41 hparameter hell) automorphisms
      targetSemantics
  passage : SpathProposition46Theorem44ToDefinition35FamilySource
    targetSemantics source

namespace SpathSuzukiFamilySource

variable {ell : Nat} {scope : FLZFullHGUniverse 2 ell}
variable {coverage : FullHGDefinition35Coverage scope}
variable {classification : FullHGTypeCClassificationSource scope}
variable {pair : FullHG scope} {parameter : SuzukiParameter}
variable {hSuzuki : classification.structuralCase coverage pair =
  .typeC (.simpleSuzuki parameter)}
variable {automorphisms : forall block : (coverage.presentation pair).family.Block,
  Definition35AutomorphismStabilizerAdapter
    ((coverage.presentation pair).family.problem block)}
variable {source : forall block : (coverage.presentation pair).family.Block,
  FLZSourceSemantics ((coverage.presentation pair).family.problem block)
    (automorphisms block)}
variable (S : SpathSuzukiFamilySource classification pair parameter hSuzuki
  automorphisms source)

include S in
/-- Apply the indexed Spath passage to the compatible cover map constructed by
Lean.  Both hypotheses of Corollary 6.3 are passed explicitly. -/
theorem hasSpathProposition46Theorem44FamilyWitness (ell_ne_two : ell ≠ 2) :
    Nonempty (SpathProposition46Theorem44FamilyWitness
      S.targetSemantics) := by
  have hell : 2 < ell :=
    lt_of_le_of_ne (coverage.presentation pair).family.ellPrime.two_le
      (Ne.symm ell_ne_two)
  obtain ⟨coverToTarget, hsurj, hcomm⟩ :=
    S.model.coverMatch.exists_coverToTarget
  let spathSource := S.spath parameter.positiveTwistParameter hell
  exact spathSource.applyFullDefinition41AndProposition46Theorem44
    coverToTarget hsurj hcomm

include S in
/-- Convert the target family obtained from Spath's passage to the fixed
Definition 3.5 relations. -/
theorem hasDefinition35IBAWFamilyWitness (ell_ne_two : ell ≠ 2) :
    Nonempty (Definition35IBAWFamilyWitness
      (coverage.presentation pair).family automorphisms source) :=
  Nonempty.map (fun witness ↦ S.passage.toDefinition35Family witness)
    (S.hasSpathProposition46Theorem44FamilyWitness ell_ne_two)

include S in
/-- Project one selected block from the staged whole family result. -/
theorem blockWitness (ell_ne_two : ell ≠ 2)
    (block : (coverage.presentation pair).family.Block) :
    Nonempty (Definition35IBAWBijection
      ((coverage.presentation pair).family.problem block)
      (automorphisms block) (source block)) := by
  obtain ⟨familyWitness⟩ :=
    S.hasDefinition35IBAWFamilyWitness ell_ne_two
  exact ⟨familyWitness.blockWitness block⟩

end SpathSuzukiFamilySource

end ModularRep.PaperProofs.EvenFieldProposition39Suzuki


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
