import ModularRep.PaperProofs.EvenFieldConcreteTypeC
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource

/-!
# The exceptional `Sp6(2)` branch at three

This module gives a staged trust boundary for the coefficient prime three
branch of even field Proposition 3.9.  The target is identified with the
literal fixed point group `FiniteSymplecticFixed 3 1`.  A separate family is
identified as its universal prime to three cover and is supplied with a full
universal central extension certificate.

Schaeffer Fry, Theorem 5.5, supplies one complete instance of Spath's
Definition 4.1 on the covering family.  Spath, Proposition 4.6 and Theorem
4.4, then pass that exact instance through the central extension.  A
separately supplied relation implication converts the resulting modular
character triple relation to the fixed Definition 3.5 relation used by this
project.

The supplementary GAP calculation is not load bearing here.  Its blockwise
counts corroborate the numerical part of the cited proof, but do not construct
the equivariant bijections, extensions, or block relations represented by the
external theorem sources below.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39Sp6Three

open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- The E1/U identification of the target family and its full covering
family in the exceptional `Sp6(2)` branch. -/
structure Sp6TwoThreeModel {ell : Nat}
    (targetFamily : Definition35Family.{u} ell) : Type (u + 1) where
  coverFamily : Definition35Family.{u} ell
  targetModel : targetFamily.H ≃* FiniteSymplecticFixed 3 1
  coverMatch : EllPrimeCoverCentralExtensionFamilyMatch
    coverFamily targetFamily
  fullUniversalCover :
    IsUniversalCentralExtension coverMatch.cover.quotient
  targetCenterless : Subgroup.center targetFamily.H = ⊥

/-- The E2/U application of Schaeffer Fry, Theorem 5.5, to the exact
exceptional group and coefficient prime.  Its output is one complete
Definition 4.1 packet on the covering family, not a final witness on the
target family. -/
structure SchaefferFrySp6TwoThreeDefinition41Source {ell : Nat}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    (targetModel : targetFamily.H ≃* FiniteSymplecticFixed 3 1)
    (coverMatch : EllPrimeCoverCentralExtensionFamilyMatch
      coverFamily targetFamily)
    (fullUniversalCover :
      IsUniversalCentralExtension coverMatch.cover.quotient)
    (targetCenterless : Subgroup.center targetFamily.H = ⊥)
    (coverAutomorphisms : ∀ block : coverFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (coverFamily.problem block))
    (coverSemantics : FLZBAWGoodFamilySemantics coverFamily
      coverMatch.cover coverAutomorphisms)
    (coverGlobalSemantics : SpathDefinition41GlobalSemantics coverFamily
      coverMatch.cover coverAutomorphisms coverSemantics) : Prop where
  applyTheorem55 : ell = 3 →
    Nonempty (SpathDefinition41FamilyWitness coverGlobalSemantics)

namespace SchaefferFrySp6TwoThreeDefinition41Source

/-- Select the single Definition 4.1 packet supplied by the cited theorem. -/
noncomputable def theorem55Definition41 {ell : Nat}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    {targetModel : targetFamily.H ≃* FiniteSymplecticFixed 3 1}
    {coverMatch : EllPrimeCoverCentralExtensionFamilyMatch
      coverFamily targetFamily}
    {fullUniversalCover :
      IsUniversalCentralExtension coverMatch.cover.quotient}
    {targetCenterless : Subgroup.center targetFamily.H = ⊥}
    {coverAutomorphisms : ∀ block : coverFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (coverFamily.problem block)}
    {coverSemantics : FLZBAWGoodFamilySemantics coverFamily
      coverMatch.cover coverAutomorphisms}
    {coverGlobalSemantics : SpathDefinition41GlobalSemantics coverFamily
      coverMatch.cover coverAutomorphisms coverSemantics}
    (S : SchaefferFrySp6TwoThreeDefinition41Source targetModel coverMatch
      fullUniversalCover targetCenterless coverAutomorphisms coverSemantics
      coverGlobalSemantics)
    (ell_eq : ell = 3) :
    SpathDefinition41FamilyWitness coverGlobalSemantics :=
  Classical.choice (S.applyTheorem55 ell_eq)

end SchaefferFrySp6TwoThreeDefinition41Source

/-- The complete staged source packet for the exceptional `Sp6(2)` branch.
The public parameters are unchanged: one literal target family, its
automorphism adapters, and its fixed Definition 3.5 relations. -/
structure Sp6TwoThreeSource {ell : Nat}
    (family : Definition35Family.{u} ell)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) :
    Type (u + 1) where
  ell_eq : ell = 3
  model : Sp6TwoThreeModel family
  coverAutomorphisms : ∀ block : model.coverFamily.Block,
    Definition35AutomorphismStabilizerAdapter
      (model.coverFamily.problem block)
  coverSemantics : FLZBAWGoodFamilySemantics model.coverFamily
    model.coverMatch.cover coverAutomorphisms
  coverGlobalSemantics : SpathDefinition41GlobalSemantics model.coverFamily
    model.coverMatch.cover coverAutomorphisms coverSemantics
  schaefferFry : SchaefferFrySp6TwoThreeDefinition41Source
    model.targetModel model.coverMatch model.fullUniversalCover
      model.targetCenterless coverAutomorphisms coverSemantics
      coverGlobalSemantics
  targetSemantics : SpathProposition46Theorem44FamilySemantics
    model.coverMatch model.fullUniversalCover model.targetCenterless
      automorphisms
  spath : SpathProposition46Theorem44Source model.coverMatch
    model.fullUniversalCover model.targetCenterless coverAutomorphisms
      coverSemantics coverGlobalSemantics
      (schaefferFry.theorem55Definition41 ell_eq) automorphisms
      targetSemantics
  passage : SpathProposition46Theorem44ToDefinition35FamilySource
    targetSemantics source

namespace Sp6TwoThreeSource

variable {ell : Nat}
variable {family : Definition35Family.{u} ell}
variable {automorphisms : ∀ block : family.Block,
  Definition35AutomorphismStabilizerAdapter (family.problem block)}
variable {source : ∀ block : family.Block,
  FLZSourceSemantics (family.problem block) (automorphisms block)}
variable (S : Sp6TwoThreeSource family automorphisms source)

include S in
/-- Apply the indexed Spath passage to the homomorphism produced by the
universal prime to `ell` cover. -/
theorem hasSpathProposition46Theorem44FamilyWitness :
    Nonempty (SpathProposition46Theorem44FamilyWitness
      S.targetSemantics) := by
  obtain ⟨coverToTarget, hsurj, hcomm⟩ :=
    S.model.coverMatch.exists_coverToTarget
  exact S.spath.applyFullDefinition41AndProposition46Theorem44
    coverToTarget hsurj hcomm

include S in
/-- Convert the target family obtained from Spath's passage to the fixed
Definition 3.5 relations. -/
theorem hasDefinition35IBAWFamilyWitness :
    Nonempty (Definition35IBAWFamilyWitness family automorphisms source) :=
  Nonempty.map (fun witness ↦ S.passage.toDefinition35Family witness)
    S.hasSpathProposition46Theorem44FamilyWitness

include S in
/-- Project one selected block from the whole family result. -/
theorem blockWitness (block : family.Block) :
    Nonempty (Definition35IBAWBijection (family.problem block)
      (automorphisms block) (source block)) := by
  obtain ⟨familyWitness⟩ := S.hasDefinition35IBAWFamilyWitness
  exact ⟨familyWitness.blockWitness block⟩

end Sp6TwoThreeSource

end ModularRep.PaperProofs.EvenFieldProposition39Sp6Three


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
