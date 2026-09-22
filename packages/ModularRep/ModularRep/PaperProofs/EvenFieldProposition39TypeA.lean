import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.TypeAQuasisimpleSource

/-!
# The type A branch of Proposition 3.9

The current type A input is `CoverFreeTypeAApplication`. It supplies the
scoped independent type A consequence on the actual SL/SU finite group,
with its original coefficients, blocks, actions and Definition 3.5 relation.
It uses the actual matrix presentations and finite-splitting source contract
in `TypeAQuasisimpleSource`. The source chain includes the universal and
exceptional cases; the finite group is never replaced by its central quotient.
In particular its centre may have order divisible by the coefficient prime.

The retained `FLZ2023TypeACompositeSource` is indexed by one already fixed
`Definition35Family`, all of its block stabiliser actions, and all of its
Definition 3.5 source relations.  The source separates the cited BAW-good
family from the passage to these Definition 3.5 relations.  The exact match
of the indexed family and cover with the universal type A source, including
the interpretation of `ell ≠ 2` as `ell ∤ q` when `q = 2^a`, remains E1/U.
The E2/U material consists of:

* Feng--Li--Zhang 2023, Theorem 5.2, which reduces all type A blocks to
  isolated blocks;
* the proof of their Theorem 1, which discharges that premise in nondefining
  characteristic using Bonnafe, Proposition 5.2, and Feng--C. Li--Zhang,
  Theorem 2; and
* the separate implication from the fixed BAW-good relation to the fixed
  Definition 3.5 relation, as in Feng--Li--Zhang 2022, Section 3.5.

Lean gives the cited theorem and relation implication no K credit.  The
kernel reuses the exact BAW-good equivalence and equivariance, changes only
the relation proof through the supplied implication, and projects a selected
block from the resulting witness for the whole family.

The old composite is valid only on its stronger prime-to-ell-cover domain.
`toCoverFree` converts it to the current supplier when actual type A
coordinates and coefficient/source identifications are also supplied. The
old declarations and theorems are retained without weakening their cover.
Neither route supplies a `SpathDefinition41FamilyWitness`; the endpoint is
a family of Definition 3.5 iBAW-bijections.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39TypeA

open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- Current even-characteristic type A supplier, on the same actual finite
fixed-point group. This imposes no centre-prime-to or cover hypothesis. -/
abbrev CoverFreeTypeAApplication {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) :=
  TypeAQuasisimpleSource.ApplicationData 2 family automorphisms source

/-- The cited assertion that the fixed type A family is BAW-good.  The theorem
operation is E2/U.  Matching the indexed family and cover to the source and
interpreting `ell ≠ 2` as `ell ∤ q` are separate E1/U obligations.  Theorem
5.2 is used together with the discharge in the proof of Theorem 1. -/
structure FLZ2023TypeABAWGoodSource {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (semantics : FLZBAWGoodFamilySemantics
      family cover automorphisms) : Prop where
  applyTheorem52ProofTheorem1ToBAWGood :
    ell ≠ 2 →
      Nonempty (FLZBAWGoodFamilyWitness
        family cover automorphisms semantics)

/-- The fixed type A family, its BAW-good source, and the separate passage to
the Definition 3.5 relations.  The data fields prevent the cover, actions, or
relations from changing during composition. -/
structure FLZ2023TypeACompositeSource {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block)
        (automorphisms block)) : Type (u + 1) where
  cover : EllPrimeCoverSource ell family.H
  semantics : FLZBAWGoodFamilySemantics family cover automorphisms
  bawGoodSource :
    FLZ2023TypeABAWGoodSource family cover automorphisms semantics
  passage :
    FLZBAWGoodToDefinition35FamilySource semantics source

namespace FLZ2023TypeACompositeSource

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {automorphisms : ∀ block : family.Block,
  Definition35AutomorphismStabilizerAdapter (family.problem block)}
variable {source : ∀ block : family.Block,
  FLZSourceSemantics (family.problem block) (automorphisms block)}
variable (S : FLZ2023TypeACompositeSource family automorphisms source)

include S in
/-- Convert the cited BAW-good family to the fixed Definition 3.5 family. -/
theorem hasDefinition35IBAWFamilyWitness
    (hell : ell ≠ 2) :
    Nonempty (Definition35IBAWFamilyWitness
      family automorphisms source) :=
  Nonempty.map
    (fun good ↦ S.passage.toDefinition35Family good)
    (S.bawGoodSource.applyTheorem52ProofTheorem1ToBAWGood hell)

include S in
/-- Project the Definition 3.5 witness for one literal block from the result
for the whole family. -/
theorem blockWitness (hell : ell ≠ 2) (block : family.Block) :
    Nonempty (Definition35IBAWBijection (family.problem block)
      (automorphisms block) (source block)) :=
  Nonempty.map
    (fun familyWitness ↦ familyWitness.blockWitness block)
    (S.hasDefinition35IBAWFamilyWitness hell)

/-- Preserve the accepted stronger constructor on its valid domain. The
new applicability and coefficient data identify the same family with an
actual even-characteristic SL/SU group. The theorem operation reuses the
old composite's witness; it does not assume a new matching or strengthen
the old theorem to arbitrary defining characteristics. -/
def toCoverFree (rank : ℕ) (rankPositive : 0 < rank)
    (presentation : TypeAQuasisimpleSource.ActualPresentation 2 rank family.H)
    (groupScope : TypeAQuasisimpleSource.QuasisimpleScope family.H)
    (inputSemantics : TypeAQuasisimpleSource.InputSemantics family) :
    CoverFreeTypeAApplication family automorphisms source where
  rank := rank
  rankPositive := rankPositive
  presentation := presentation
  groupScope := groupScope
  inputSemantics := inputSemantics
  published :=
    { typeA_iBAWBijection := by
        intro _definingPrime _coefficientPrime distinctPrimes
          _rankPositive _groupScope _inputSemantics
        exact S.hasDefinition35IBAWFamilyWitness distinctPrimes }

end FLZ2023TypeACompositeSource

end ModularRep.PaperProofs.EvenFieldProposition39TypeA


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
