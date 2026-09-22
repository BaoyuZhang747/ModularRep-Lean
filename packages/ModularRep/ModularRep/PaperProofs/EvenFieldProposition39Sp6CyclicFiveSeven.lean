import ModularRep.Sp6DoubleCoverOrder
import ModularRep.PaperProofs.EvenFieldConcreteTypeC
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource

/-!
# The cyclic defect branches for `Sp6(2)` at five and seven

This module isolates the elementary part of the two exceptional branches in
the even field case of Proposition 3.9.  A closed index prevents confusion
between the branches for the primes five and seven.  From the exact coefficient
prime and the order of the exact universal cover, Lean proves the stronger
group property that every subgroup of the cover at the coefficient prime is
cyclic.

The target is identified with `FiniteSymplecticFixed 3 1`.  A separate
covering family is supplied with an exact universal cover prime to `ell`, a
full universal central extension certificate, and the exact order of its
group.  The elementary cyclicity calculation therefore takes place on the
same carrier on which the cited blockwise theorem is applied.

The first external source absorbs the unformalised standard passage from
cyclic `ell`-subgroups to cyclic block defect groups.  Koshitani--Spath,
Theorem 1.1 and Lemma 3.3, together with Spath's Remark 5.18, then supply one
Definition 4.1 packet on the covering family.  This is kept separate from the
indexed source in which Spath's Proposition 4.6 performs the descent to the
target and the 2017 Theorem 4.4 reformulates the extension and block
conditions.  A third source supplies the implication to the fixed Definition
3.5 relation.  The kernel constructs the compatible cover map and performs
only the fixed relation conversion and family projections.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven

open ModularRep.ManuscriptVerification.Sp6DoubleCoverOrder
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- The two coefficient primes for which the fixed point group order
forces every prime subgroup to be cyclic.  Keeping this index closed rules
out a raw prime selected by the caller. -/
inductive Sp6TwoCyclicPrime where
  | five
  | seven
  deriving DecidableEq, Repr

namespace Sp6TwoCyclicPrime

/-- The natural-number coefficient prime represented by the closed branch
index. -/
@[simp]
def value : Sp6TwoCyclicPrime -> Nat
  | .five => 5
  | .seven => 7

end Sp6TwoCyclicPrime

/-- The E1/U model for the exceptional prime five and prime seven branches.
The covering and target families are separate dependent indices. -/
structure Sp6TwoCyclicFiveSevenModel {ell : Nat}
    (prime : Sp6TwoCyclicPrime)
    (targetFamily : Definition35Family.{u} ell) : Type (u + 1) where
  ell_eq : ell = prime.value
  coverFamily : Definition35Family.{u} ell
  targetModel : targetFamily.H ≃* FiniteSymplecticFixed 3 1
  coverMatch : EllPrimeCoverCentralExtensionFamilyMatch
    coverFamily targetFamily
  fullUniversalCover :
    IsUniversalCentralExtension coverMatch.cover.quotient
  targetCenterless : Subgroup.center targetFamily.H = ⊥
  coverOrder : Nat.card coverFamily.H = sp6DoubleCoverOrder

namespace Sp6TwoCyclicFiveSevenModel

variable {ell : Nat} {prime : Sp6TwoCyclicPrime}
variable {targetFamily : Definition35Family.{u} ell}
variable (M : Sp6TwoCyclicFiveSevenModel prime targetFamily)

include M in
/-- Every subgroup of the fixed covering group at the coefficient prime is
cyclic. -/
theorem everyEllSubgroupCyclic :
    ∀ D : Subgroup M.coverFamily.H, IsPGroup ell D → IsCyclic D := by
  intro D hD
  cases prime with
  | five =>
      have hell : ell = 5 := by
        simpa using M.ell_eq
      exact isCyclic_five_subgroup M.coverOrder D (by
        simpa [hell] using hD)
  | seven =>
      have hell : ell = 7 := by
        simpa using M.ell_eq
      exact isCyclic_seven_subgroup M.coverOrder D (by
        simpa [hell] using hD)

end Sp6TwoCyclicFiveSevenModel

/-- The first E2/U boundary.  It absorbs the unformalised passage from cyclic
`ell`-subgroups to cyclic block defect groups, then applies Koshitani--Spath,
Theorem 1.1 and Lemma 3.3, together with Spath's Remark 5.18.  It returns only
a Definition 4.1 packet on the covering family. -/
structure KoshitaniSpathSp6TwoCyclicDefinition41Source {ell : Nat}
    (prime : Sp6TwoCyclicPrime)
    {targetFamily : Definition35Family.{u} ell}
    (model : Sp6TwoCyclicFiveSevenModel prime targetFamily)
    (coverAutomorphisms : ∀ block : model.coverFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (model.coverFamily.problem block))
    (coverSemantics : FLZBAWGoodFamilySemantics model.coverFamily
      model.coverMatch.cover coverAutomorphisms)
    (coverGlobalSemantics : SpathDefinition41GlobalSemantics model.coverFamily
      model.coverMatch.cover coverAutomorphisms coverSemantics) : Prop where
  applyTheorem11Lemma33Remark518 :
    (∀ D : Subgroup model.coverFamily.H,
      IsPGroup ell D → IsCyclic D) →
      Nonempty (SpathDefinition41FamilyWitness coverGlobalSemantics)

namespace KoshitaniSpathSp6TwoCyclicDefinition41Source

/-- Select the exact Definition 4.1 packet supplied by the cited source after
the kernel cyclicity deduction. -/
noncomputable def theorem11Lemma33Remark518Definition41
    {ell : Nat} {prime : Sp6TwoCyclicPrime}
    {targetFamily : Definition35Family.{u} ell}
    {model : Sp6TwoCyclicFiveSevenModel prime targetFamily}
    {coverAutomorphisms : ∀ block : model.coverFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (model.coverFamily.problem block)}
    {coverSemantics : FLZBAWGoodFamilySemantics model.coverFamily
      model.coverMatch.cover coverAutomorphisms}
    {coverGlobalSemantics : SpathDefinition41GlobalSemantics model.coverFamily
      model.coverMatch.cover coverAutomorphisms coverSemantics}
    (S : KoshitaniSpathSp6TwoCyclicDefinition41Source prime model
      coverAutomorphisms coverSemantics coverGlobalSemantics) :
    SpathDefinition41FamilyWitness coverGlobalSemantics :=
  Classical.choice
    (S.applyTheorem11Lemma33Remark518 model.everyEllSubgroupCyclic)

end KoshitaniSpathSp6TwoCyclicDefinition41Source

/-- The staged source for the whole family at coefficient prime five or
seven.  The outer parameters remain the target family, its automorphism
adapters, and its fixed Definition 3.5 relations. -/
structure Sp6TwoCyclicFiveSevenSource {ell : Nat}
    (prime : Sp6TwoCyclicPrime)
    (family : Definition35Family.{u} ell)
    (automorphisms : forall block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : forall block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) where
  model : Sp6TwoCyclicFiveSevenModel prime family
  coverAutomorphisms : ∀ block : model.coverFamily.Block,
    Definition35AutomorphismStabilizerAdapter
      (model.coverFamily.problem block)
  coverSemantics : FLZBAWGoodFamilySemantics model.coverFamily
    model.coverMatch.cover coverAutomorphisms
  coverGlobalSemantics : SpathDefinition41GlobalSemantics model.coverFamily
    model.coverMatch.cover coverAutomorphisms coverSemantics
  koshitaniSpath : KoshitaniSpathSp6TwoCyclicDefinition41Source prime model
    coverAutomorphisms coverSemantics coverGlobalSemantics
  targetSemantics : SpathProposition46Theorem44FamilySemantics
    model.coverMatch model.fullUniversalCover model.targetCenterless
      automorphisms
  spath : SpathProposition46Theorem44Source model.coverMatch
    model.fullUniversalCover model.targetCenterless coverAutomorphisms
      coverSemantics coverGlobalSemantics
      (koshitaniSpath.theorem11Lemma33Remark518Definition41) automorphisms
      targetSemantics
  passage : SpathProposition46Theorem44ToDefinition35FamilySource
    targetSemantics source

namespace Sp6TwoCyclicFiveSevenSource

variable {ell : Nat} {prime : Sp6TwoCyclicPrime}
variable {family : Definition35Family.{u} ell}
variable {automorphisms : forall block : family.Block,
  Definition35AutomorphismStabilizerAdapter (family.problem block)}
variable {source : forall block : family.Block,
  FLZSourceSemantics (family.problem block) (automorphisms block)}
variable (S : Sp6TwoCyclicFiveSevenSource prime family automorphisms source)

include S in
/-- Every subgroup of the fixed covering group at the coefficient prime is
cyclic. -/
theorem everyEllSubgroupCyclic :
    ∀ D : Subgroup S.model.coverFamily.H,
      IsPGroup ell D → IsCyclic D :=
  S.model.everyEllSubgroupCyclic

include S in
/-- Apply the indexed Spath passage to the compatible cover map constructed
from the exact central extension data. -/
theorem hasSpathProposition46Theorem44FamilyWitness :
    Nonempty (SpathProposition46Theorem44FamilyWitness
      S.targetSemantics) := by
  obtain ⟨coverToTarget, hsurj, hcomm⟩ :=
    S.model.coverMatch.exists_coverToTarget
  exact S.spath.applyFullDefinition41AndProposition46Theorem44
    coverToTarget hsurj hcomm

include S in
/-- Convert the target witnesses obtained from the Spath passage to the fixed
Definition 3.5 relations. -/
theorem hasDefinition35IBAWFamilyWitness :
    Nonempty (Definition35IBAWFamilyWitness family automorphisms source) :=
  Nonempty.map (fun witness ↦ S.passage.toDefinition35Family witness)
    S.hasSpathProposition46Theorem44FamilyWitness

include S in
/-- Project one selected block from the cited result for the whole family. -/
theorem blockWitness (block : family.Block) :
    Nonempty (Definition35IBAWBijection (family.problem block)
      (automorphisms block) (source block)) := by
  obtain ⟨familyWitness⟩ := S.hasDefinition35IBAWFamilyWitness
  exact ⟨familyWitness.blockWitness block⟩

end Sp6TwoCyclicFiveSevenSource

end ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
