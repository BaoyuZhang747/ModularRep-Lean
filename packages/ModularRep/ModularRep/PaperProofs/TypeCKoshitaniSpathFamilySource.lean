import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# The published blockwise-to-global family passage

Koshitani--Spath (2016), Definition 3.2 and Lemma 3.3, pp. 782--783,
pass from a block-condition transversal on the actual universal prime-to-p
cover to Spath (2013), Definition 5.17. Taking all blocks and all p-groups
gives the complete condition by Remark 5.18, including BOTH Q=1 clauses.

The general E2 source below consumes independently established COMPLETE
block witnesses. It does not produce these block hypotheses, and a bare
relative witness cannot be substituted. The fixed family, actual cover
projection, specified operations, coefficient fields and selected reduction
tables precede the implication. Their standard E1 dictionaries retain the
actual primitive equations and finite-domain root agreement.

The conclusion is existential. It may choose new compatible block maps,
references, ambient extensions and intermediate packets. In particular no
equality to arbitrary old block witnesses or their global map is asserted.
This is the published normalization passage, not an assumption that those
old packets already satisfy its conclusion. No source instance is supplied.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCKoshitaniSpathFamilySource

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition

universe u

/-- Exact universal E2 passage, with the standard fixed-system E1
interpretation explicit. The chosen output need not retain old packets. -/
structure Source : Prop where
  allBlocks : ∀ {ell : ℕ} (family : Definition35Family.{u} ell)
      (cover : EllPrimeCoverSource ell family.H)
      (splitting : IsAlgClosed family.K)
      (coefficient : SpathCoefficientField ell family.k family.ellPrime)
      (ambient_idempotent : ∀ b,
        family.blockSource.operations.ambientBlockData.blockIdempotent b =
          family.blockIdempotent b)
      (localPhysical : GuardedBlockCompatibility family.iota
        family.blockSource.operations)
      (selectedRoots : ∀ b w,
        QuotientRootAgreement family.iota
          (SelectedRadical family.blockSource b w)
          (family.localReduction b w).iota),
    (∀ b, Nonempty (BlockWitness family cover b)) →
      Nonempty (FamilyWitness family cover)

variable {ell : ℕ} (family : Definition35Family.{u} ell)
variable (cover : EllPrimeCoverSource ell family.H)
variable (splitting : IsAlgClosed family.K)
variable (coefficient : SpathCoefficientField ell family.k family.ellPrime)
variable (ambient_idempotent : ∀ b,
  family.blockSource.operations.ambientBlockData.blockIdempotent b =
    family.blockIdempotent b)
variable (localPhysical : GuardedBlockCompatibility family.iota
  family.blockSource.operations)
variable (selectedRoots : ∀ b w,
  QuotientRootAgreement family.iota
    (SelectedRadical family.blockSource b w) (family.localReduction b w).iota)

/-- Apply the named source after constructing every complete block. The
same family and cover remain fixed; its normalized packets are fresh choices. -/
def familyWitness (source : Source.{u})
    (blocks : ∀ b, Nonempty (BlockWitness family cover b)) :
    FamilyWitness family cover :=
  Classical.choice (source.allBlocks family cover splitting coefficient
    ambient_idempotent localPhysical selectedRoots blocks)

end ModularRep.PaperProofs.TypeCKoshitaniSpathFamilySource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
