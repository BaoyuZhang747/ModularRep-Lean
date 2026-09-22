import ManuscriptIBAW.TypeC.EvenApplicationSourceCoordinates
import ModularRep.PaperProofs.EvenFieldConcreteTypeC
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource

/-!
The split application in ranks two and three, with the specified cover
descent. The finite fixed point family may be a central quotient of its full
cover when such a presentation is chosen. Schaeffer Fry, Theorem 5.5, is
applied to the covering family. Späth (2013), Proposition 4.6 with r = 1,
together with Späth (2017), Theorem 4.4, then gives descent to the fixed
point blocks.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC.EvenApplicationLowRank

open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- The E1/U identification of the target family and its full covering family in
the split small rank branch. -/
structure SplitLowRankModel (r a : Nat) {ell : Nat}
    (targetFamily : Definition35Family.{u} ell) : Type (u + 1) where
  coverFamily : Definition35Family.{u} ell
  commonRoots : ManuscriptIBAW.TypeC.CommonFamilyRoots coverFamily targetFamily
  targetModel : targetFamily.H ≃* FiniteSymplecticFixed r a
  coverMatch : EllPrimeCoverCentralExtensionFamilyMatch
    coverFamily targetFamily
  fullUniversalCover :
    IsUniversalCentralExtension coverMatch.cover.quotient
  targetCenterless : Subgroup.center targetFamily.H = ⊥

/-- The application of Schaeffer Fry, Theorem 5.5 (E2/U), to the specified
finite fixed point group and odd prime. Its output is a complete collection
of data satisfying Definition 4.1 on the covering family. Descent to the
target family is a separate step. -/
structure SchaefferFrySplitDefinition41Source {r a ell : Nat}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    (targetModel : targetFamily.H ≃* FiniteSymplecticFixed r a)
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
  applyTheorem55 : (r = 2 ∨ r = 3) → 2 ≤ a → 2 < ell →
    Nonempty (SpathDefinition41FamilyWitness coverGlobalSemantics)

namespace SchaefferFrySplitDefinition41Source

/-- Choose data satisfying Definition 4.1 supplied by the cited theorem. -/
noncomputable def theorem55Definition41 {r a ell : Nat}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    {targetModel : targetFamily.H ≃* FiniteSymplecticFixed r a}
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
    (S : SchaefferFrySplitDefinition41Source targetModel coverMatch
      fullUniversalCover targetCenterless coverAutomorphisms coverSemantics
      coverGlobalSemantics)
    (rankLow : r = 2 ∨ r = 3) (fieldLarge : 2 ≤ a) (ell_odd : 2 < ell) :
    SpathDefinition41FamilyWitness coverGlobalSemantics :=
  Classical.choice (S.applyTheorem55 rankLow fieldLarge ell_odd)

end SchaefferFrySplitDefinition41Source

/-- The source data for the split small rank case. The target family,
automorphism actions and relations in Definition 3.5 are fixed throughout. -/
structure SplitLowRankSource (r a : Nat) {ell : Nat}
    (family : Definition35Family.{u} ell)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) :
    Type (u + 1) where
  rankLow : r = 2 ∨ r = 3
  fieldLarge : 2 ≤ a
  ell_odd : 2 < ell
  model : SplitLowRankModel r a family
  coverAutomorphisms : ∀ block : model.coverFamily.Block,
    Definition35AutomorphismStabilizerAdapter
      (model.coverFamily.problem block)
  coverSemantics : FLZBAWGoodFamilySemantics model.coverFamily
    model.coverMatch.cover coverAutomorphisms
  coverGlobalSemantics : SpathDefinition41GlobalSemantics model.coverFamily
    model.coverMatch.cover coverAutomorphisms coverSemantics
  schaefferFry : SchaefferFrySplitDefinition41Source
    model.targetModel model.coverMatch model.fullUniversalCover
      model.targetCenterless coverAutomorphisms coverSemantics
      coverGlobalSemantics
  targetSemantics : SpathProposition46Theorem44FamilySemantics
    model.coverMatch model.fullUniversalCover model.targetCenterless
      automorphisms
  spath : SpathProposition46Theorem44Source model.coverMatch
    model.fullUniversalCover model.targetCenterless coverAutomorphisms
      coverSemantics coverGlobalSemantics
      (schaefferFry.theorem55Definition41 rankLow fieldLarge ell_odd) automorphisms
      targetSemantics
  passage : SpathProposition46Theorem44ToDefinition35FamilySource
    targetSemantics source

namespace SplitLowRankSource

variable {r a ell : Nat}
variable {family : Definition35Family.{u} ell}
variable {automorphisms : ∀ block : family.Block,
  Definition35AutomorphismStabilizerAdapter (family.problem block)}
variable {source : ∀ block : family.Block,
  FLZSourceSemantics (family.problem block) (automorphisms block)}
variable (S : SplitLowRankSource r a family automorphisms source)

include S in
/-- Apply Späth's descent theorem to the homomorphism from the universal prime
to `ell` cover. -/
theorem hasSpathProposition46Theorem44FamilyWitness :
    Nonempty (SpathProposition46Theorem44FamilyWitness
      S.targetSemantics) := by
  obtain ⟨coverToTarget, hsurj, hcomm⟩ :=
    S.model.coverMatch.exists_coverToTarget
  exact S.spath.applyFullDefinition41AndProposition46Theorem44
    coverToTarget hsurj hcomm

include S in
/-- Express the family obtained by Späth's descent theorem in the specified
relations of Definition 3.5. -/
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

end SplitLowRankSource

end ManuscriptIBAW.TypeC.EvenApplicationLowRank



/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
