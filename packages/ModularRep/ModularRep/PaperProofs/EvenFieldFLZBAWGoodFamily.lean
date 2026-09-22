import ModularRep.BrauerCharacterHomPullback
import ModularRep.BlockInduction
import ModularRep.NormalCoreTransport
import ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource
import ModularRep.SpathNavarroSourceAdapter

/-!
# A fixed carrier for the Brough--Spath block condition

Brough--Spath, Definition 4.3, describes the inductive BAW condition for a
block by an equivariant bijection and, for every matched Brauer character and
weight, a central character quotient, a finite ambient group, global and local
extensions, and equalities of blocks in every intermediate group.  The
paragraph after that definition gives the corresponding formulation on the
universal prime-to-`ell` cover.  Feng--Li--Zhang, Section 3.5, uses this
formulation and gives equation (3.17) as a sufficient criterion.

This module separates a blockwise BAW-good carrier from a full source packet
for Spath's Definition 4.1.  `FLZBAWGoodFamilyWitness` fixes one opaque source
interpretation of the published matched-pair relation and one witness for each
block.  It does not contain cross-block naturality or the remaining global
clauses.  `SpathDefinition41FamilyWitness` adds a source-supplied proof of the
literal cross-block naturality proposition and a source-supplied proof of
`globalSemantics.globallyCoherent`.  The latter predicate is the indexed U
interpretation of the remaining clauses of Definition 4.1.  The definitions
and dependent indices are K, whereas a mathematical witness returned by a
cited source is E2/U.

The neutral central-extension layer fixes an exact universal prime-to-`ell`
cover and a perfect central prime-to-`ell` extension of the same simple
quotient.  A full universal central extension certificate and target
centrelessness are separate indices of the Spath passage.  Lean derives only
the compatible surjective homomorphism.  It does not transport blocks,
characters, weights, or actions.  A separate proposition-valued passage can
convert a BAW-good family to the fixed Definition 3.5 family, but only after an
external source supplies the implication between the two block relations.  The
module does not prove that implication or identify BAW-goodness with equation
(3.17), and it does not use `Formalisation.IBAW.BlockWitness`.

In the concrete layer, one reference Brauer character fixes the central
kernel, quotient group, and selected quotient block for the whole block.  Every
other character is descended to that same quotient.  The image of the radical
subgroup and the canonical map between the two normaliser quotients are
constructed in the kernel.  In particular, the central prime-to-`ell` kernel
is not incorrectly assumed to lie in the radical `ell`-subgroup.

Two source interfaces remain.  `IntermediateBlockSource` is indexed by the
actual ambient group, extensions, intermediate subgroups, complete families
of primitive central idempotents, and their block central characters.  It
isolates the definedness and equality of the induced central function at
every intermediate subgroup.  This is the literal block induction relation:
no function selecting an ambient block is supplied.  The one-way
`Equation317ToRelativeBlockConditionSource` isolates the cited implication
from equation (3.17) to the concrete Brough--Spath data.  Because the present
library does not prove the required definedness and central character
equality from the representation theoretic hypotheses, the final carrier is
explicitly named relative to the supplied block induction relations.  It
must not be read as a kernel proof of BAW-goodness.  There is a second
explicit boundary: the descended characters are proved only to lie in one
fixed quotient block.  The converse
identification of the entire quotient-block Brauer fibre with the original
block fibre is not yet constructed.  Thus the carrier does not turn one-way
quotient-block membership into equality of block fibres.  Neither interface
contains an arbitrary block-result proposition.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-! ## Source-level BAW-goodness on one fixed cover -/

/-- The source interpretation of the matched-pair relation occurring in
BAW-goodness.  The automorphism adapter and exact universal prime-to-`p`
cover are indices, so they cannot be changed after the relation is fixed. -/
structure FLZBAWGoodRelation
    (P : Definition35Problem.{u})
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (cover : EllPrimeCoverSource P.p P.H) where
  bawGoodBlockIsomorphic :
    Definition35Brauer P → Definition35Weight P → Prop

/-- One fixed source interpretation of BAW-goodness for an entire literal
block family.  The family, its automorphism adapters, and its exact universal
prime-to-`ell` cover are indices of the interpretation.  The remaining field is
the explicitly graded U/E2 meaning of the published matched-pair relation for
each block. -/
structure FLZBAWGoodFamilySemantics {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)) where
  relation : ∀ block : family.Block,
    FLZBAWGoodRelation (family.problem block)
      (automorphisms block) cover

/-- One BAW-good block witness for one fixed relation and cover. -/
structure FLZBAWGoodBlockWitness
    (P : Definition35Problem.{u})
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (cover : EllPrimeCoverSource P.p P.H)
    (relation : FLZBAWGoodRelation P automorphisms cover) where
  omega : Definition35Brauer P ≃ Definition35Weight P
  equivariant : Definition35Equivariant P omega
  blockIsomorphism : ∀ psi : Definition35Brauer P,
    relation.bawGoodBlockIsomorphic psi (omega psi)

/-- BAW-good witnesses for every literal block of one family, all indexed by
the same exact cover. -/
structure FLZBAWGoodFamilyWitness {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (semantics : FLZBAWGoodFamilySemantics family cover automorphisms) where
  blockWitness : ∀ block : family.Block,
    FLZBAWGoodBlockWitness (family.problem block)
      (automorphisms block) cover (semantics.relation block)

/-- Compatibility of one chosen family of BAW-good bijections with transport
between different blocks.  The equality is the part of the global
automorphism coherence that can be stated using the present literal block
family carrier. -/
structure FLZBAWGoodFamilyNaturality {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {semantics : FLZBAWGoodFamilySemantics
      family cover automorphisms}
    (good : FLZBAWGoodFamilyWitness
      family cover automorphisms semantics) : Prop where
  omega_transport :
    ∀ (alpha : (MulAut family.H)ᵐᵒᵖ)
      (block : family.Block)
      (psi : Definition35Brauer (family.problem block)),
      (good.blockWitness (alpha • block)).omega
          (family.transportBrauer alpha psi) =
        family.transportWeight alpha
          ((good.blockWitness block).omega psi)

/-- An indexed U interpretation of the clauses in Spath's Definition 4.1
that are not represented literally by `Definition35Family`.  Its intended
meaning includes the radical partition, central character lifting, coherence
beyond `FLZBAWGoodFamilyNaturality`, normalization at the trivial radical
subgroup, and the remaining extension and intermediate block conditions.
This structure only fixes that interpretation; it supplies no proof of it. -/
structure SpathDefinition41GlobalSemantics {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (bawSemantics : FLZBAWGoodFamilySemantics
      family cover automorphisms) : Type u where
  globallyCoherent : FLZBAWGoodFamilyWitness family cover
    automorphisms bawSemantics → Prop

/-- One exact BAW-good family together with a source-supplied proof of the
literal cross-block naturality proposition and a source-supplied proof of the
externally interpreted remaining clauses of Spath's Definition 4.1. -/
structure SpathDefinition41FamilyWitness {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {bawSemantics : FLZBAWGoodFamilySemantics
      family cover automorphisms}
    (globalSemantics : SpathDefinition41GlobalSemantics family cover
      automorphisms bawSemantics) : Type u where
  good : FLZBAWGoodFamilyWitness family cover automorphisms bawSemantics
  naturality : FLZBAWGoodFamilyNaturality good
  globalCoherence : globalSemantics.globallyCoherent good

/-- The external relation implication needed to turn BAW-good witnesses on
one fixed cover into witnesses for the fixed Definition 3.5 relations.  Both
relations are indices, so the passage cannot change the family, its actions,
or the chosen cover. -/
structure FLZBAWGoodToDefinition35FamilySource {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    (semantics : FLZBAWGoodFamilySemantics family cover automorphisms)
    (definition35Source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block)
        (automorphisms block)) : Prop where
  relation_implication : ∀ (block : family.Block)
      (psi : Definition35Brauer (family.problem block))
      (weight : Definition35Weight (family.problem block)),
    (semantics.relation block).bawGoodBlockIsomorphic psi weight →
      (definition35Source block).definition35BlockIsomorphic psi weight

/-- Reuse the exact BAW-good equivalence and its equivariance, changing only
the relation proof through the supplied implication. -/
def FLZBAWGoodToDefinition35FamilySource.toDefinition35Family
    {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {semantics : FLZBAWGoodFamilySemantics family cover automorphisms}
    {definition35Source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block)
        (automorphisms block)}
    (passage : FLZBAWGoodToDefinition35FamilySource
      semantics definition35Source)
    (good : FLZBAWGoodFamilyWitness
      family cover automorphisms semantics) :
    Definition35IBAWFamilyWitness
      family automorphisms definition35Source where
  blockWitness block :=
    { omega := (good.blockWitness block).omega
      equivariant := (good.blockWitness block).equivariant
      blockIsomorphism := fun psi ↦
        passage.relation_implication block psi
          ((good.blockWitness block).omega psi)
          ((good.blockWitness block).blockIsomorphism psi) }

/-! ## Universal prime-to-`ell` cover and central extension comparison -/

/-- Exact E1/U data identifying `targetFamily.H` as a finite perfect central
prime-to-`ell` extension of the same nonabelian simple group as
`coverFamily.H`.  This structure contains no fixed point assertion and no
block, character, weight, or iBAW transport. -/
structure EllPrimeCoverCentralExtensionFamilyMatch {ell : ℕ}
    (coverFamily targetFamily : Definition35Family.{u} ell) : Type (u + 1) where
  cover : EllPrimeCoverSource ell coverFamily.H
  simpleQuotientEquiv :
    cover.S ≃* targetFamily.H ⧸ Subgroup.center targetFamily.H
  targetPerfect : commutator targetFamily.H = ⊤
  targetCenterPrimeTo :
    ¬ ell ∣ Nat.card (Subgroup.center targetFamily.H)

/-- The central quotient of the target, identified with the simple quotient
of the universal prime-to-`ell` cover. -/
def EllPrimeCoverCentralExtensionFamilyMatch.targetQuotient {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    (coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily) :
    targetFamily.H →* coverMatch.cover.S :=
  coverMatch.simpleQuotientEquiv.symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center targetFamily.H))

theorem EllPrimeCoverCentralExtensionFamilyMatch.targetQuotient_surjective
    {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    (coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily) :
    Function.Surjective coverMatch.targetQuotient := by
  change Function.Surjective
    (fun x : targetFamily.H ↦
      coverMatch.simpleQuotientEquiv.symm
        (QuotientGroup.mk' (Subgroup.center targetFamily.H) x))
  exact coverMatch.simpleQuotientEquiv.symm.surjective.comp
    (QuotientGroup.mk'_surjective (Subgroup.center targetFamily.H))

@[simp]
theorem EllPrimeCoverCentralExtensionFamilyMatch.targetQuotient_ker
    {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    (coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily) :
    coverMatch.targetQuotient.ker =
      Subgroup.center targetFamily.H := by
  change
    (coverMatch.simpleQuotientEquiv.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center targetFamily.H))).ker =
        Subgroup.center targetFamily.H
  calc
    _ = (QuotientGroup.mk' (Subgroup.center targetFamily.H)).ker :=
      MonoidHom.ker_comp_of_injective
        (QuotientGroup.mk' (Subgroup.center targetFamily.H))
        coverMatch.simpleQuotientEquiv.symm.toMonoidHom
        coverMatch.simpleQuotientEquiv.symm.injective
    _ = Subgroup.center targetFamily.H :=
      QuotientGroup.ker_mk' (Subgroup.center targetFamily.H)

/-- Maximality of the universal prime-to-`ell` cover gives a surjective
homomorphism to the matched perfect central extension.  This is only a
group-theoretic comparison: it does not transport blocks, characters,
weights, or iBAW data. -/
theorem EllPrimeCoverCentralExtensionFamilyMatch.exists_coverToTarget
    {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    (coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily) :
    ∃ coverToTarget : coverFamily.H →* targetFamily.H,
      Function.Surjective coverToTarget ∧
        coverMatch.targetQuotient.comp coverToTarget =
          coverMatch.cover.quotient := by
  exact coverMatch.cover.maximal targetFamily.H
    coverMatch.targetQuotient
    coverMatch.targetQuotient_surjective
    (le_of_eq coverMatch.targetQuotient_ker)
    coverMatch.targetPerfect
    (by
      rw [coverMatch.targetQuotient_ker]
      exact coverMatch.targetCenterPrimeTo)

/-! ## Spath Proposition 4.6 and Theorem 4.4 family passage -/

/-- One fixed interpretation of the modular character triple relation
obtained for every block of the target family after applying Spath,
Proposition 4.6 and Theorem 4.4.  The cover match, full universal cover,
centreless target, and exact automorphism adapters are indices.  The meaning
of `relation` remains U/E2. -/
structure SpathProposition46Theorem44FamilySemantics {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    (coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily)
    (fullUniversalCover :
      IsUniversalCentralExtension coverMatch.cover.quotient)
    (targetCenterless : Subgroup.center targetFamily.H = ⊥)
    (targetAutomorphisms : ∀ block : targetFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (targetFamily.problem block)) : Type u where
  relation : ∀ block : targetFamily.Block,
    Definition35Brauer (targetFamily.problem block) →
      Definition35Weight (targetFamily.problem block) → Prop

/-- One target block witness for the relation produced by the cited Spath
passage. -/
structure SpathProposition46Theorem44BlockWitness {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    {coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily}
    {fullUniversalCover :
      IsUniversalCentralExtension coverMatch.cover.quotient}
    {targetCenterless : Subgroup.center targetFamily.H = ⊥}
    {targetAutomorphisms : ∀ block : targetFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (targetFamily.problem block)}
    (semantics : SpathProposition46Theorem44FamilySemantics coverMatch
      fullUniversalCover targetCenterless targetAutomorphisms)
    (block : targetFamily.Block) : Type u where
  omega : Definition35Brauer (targetFamily.problem block) ≃
    Definition35Weight (targetFamily.problem block)
  equivariant : Definition35Equivariant
    (targetFamily.problem block) omega
  blockIsomorphism : ∀ psi : Definition35Brauer
      (targetFamily.problem block),
    semantics.relation block psi (omega psi)

/-- The target block witnesses constructed for the complete literal block
family. -/
structure SpathProposition46Theorem44FamilyWitness {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    {coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily}
    {fullUniversalCover :
      IsUniversalCentralExtension coverMatch.cover.quotient}
    {targetCenterless : Subgroup.center targetFamily.H = ⊥}
    {targetAutomorphisms : ∀ block : targetFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (targetFamily.problem block)}
    (semantics : SpathProposition46Theorem44FamilySemantics coverMatch
      fullUniversalCover targetCenterless targetAutomorphisms) : Type u where
  blockWitness : ∀ block : targetFamily.Block,
    SpathProposition46Theorem44BlockWitness semantics block

/-- A source-specific E2/U forward composite of Spath's Definition 4.1 and
Proposition 4.6, specialised to `r = 1`, and Spath's 2017 Theorem 4.4.  The
exact `SpathDefinition41FamilyWitness` is an index, so the source cannot be
applied to a different family witness.  Source carriers, the ambient action,
radical and defect-zero data, block identifications, and central-kernel
identifications remain external. -/
structure SpathProposition46Theorem44Source {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    (coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily)
    (fullUniversalCover :
      IsUniversalCentralExtension coverMatch.cover.quotient)
    (targetCenterless : Subgroup.center targetFamily.H = ⊥)
    (coverAutomorphisms : ∀ block : coverFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (coverFamily.problem block))
    (coverSemantics : FLZBAWGoodFamilySemantics coverFamily
      coverMatch.cover coverAutomorphisms)
    (coverGlobalSemantics : SpathDefinition41GlobalSemantics coverFamily
      coverMatch.cover coverAutomorphisms coverSemantics)
    (definition41 : SpathDefinition41FamilyWitness coverGlobalSemantics)
    (targetAutomorphisms : ∀ block : targetFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (targetFamily.problem block))
    (targetSemantics : SpathProposition46Theorem44FamilySemantics coverMatch
      fullUniversalCover targetCenterless targetAutomorphisms) : Prop where
  applyFullDefinition41AndProposition46Theorem44 :
    ∀ (coverToTarget : coverFamily.H →* targetFamily.H),
      Function.Surjective coverToTarget →
      coverMatch.targetQuotient.comp coverToTarget =
        coverMatch.cover.quotient →
      Nonempty (SpathProposition46Theorem44FamilyWitness
        targetSemantics)

/-- The separate pointwise implication from the modular character triple
relation produced by the Spath passage to the fixed Definition 3.5 relation. -/
structure SpathProposition46Theorem44ToDefinition35FamilySource
    {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    {coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily}
    {fullUniversalCover :
      IsUniversalCentralExtension coverMatch.cover.quotient}
    {targetCenterless : Subgroup.center targetFamily.H = ⊥}
    {targetAutomorphisms : ∀ block : targetFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (targetFamily.problem block)}
    (targetSemantics : SpathProposition46Theorem44FamilySemantics coverMatch
      fullUniversalCover targetCenterless targetAutomorphisms)
    (definition35Source : ∀ block : targetFamily.Block,
      FLZSourceSemantics (targetFamily.problem block)
        (targetAutomorphisms block)) : Prop where
  relation_implication : ∀ (block : targetFamily.Block)
      (psi : Definition35Brauer (targetFamily.problem block))
      (weight : Definition35Weight (targetFamily.problem block)),
    targetSemantics.relation block psi weight →
      (definition35Source block).definition35BlockIsomorphic psi weight

/-- Reuse the exact equivalences and equivariance constructed by the Spath
passage, changing only the relation proof through the supplied implication. -/
def SpathProposition46Theorem44ToDefinition35FamilySource.toDefinition35Family
    {ell : ℕ}
    {coverFamily targetFamily : Definition35Family.{u} ell}
    {coverMatch :
      EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily}
    {fullUniversalCover :
      IsUniversalCentralExtension coverMatch.cover.quotient}
    {targetCenterless : Subgroup.center targetFamily.H = ⊥}
    {targetAutomorphisms : ∀ block : targetFamily.Block,
      Definition35AutomorphismStabilizerAdapter
        (targetFamily.problem block)}
    {targetSemantics : SpathProposition46Theorem44FamilySemantics coverMatch
      fullUniversalCover targetCenterless targetAutomorphisms}
    {definition35Source : ∀ block : targetFamily.Block,
      FLZSourceSemantics (targetFamily.problem block)
        (targetAutomorphisms block)}
    (passage : SpathProposition46Theorem44ToDefinition35FamilySource
      targetSemantics definition35Source)
    (spath : SpathProposition46Theorem44FamilyWitness targetSemantics) :
    Definition35IBAWFamilyWitness targetFamily targetAutomorphisms
      definition35Source where
  blockWitness block :=
    { omega := (spath.blockWitness block).omega
      equivariant := (spath.blockWitness block).equivariant
      blockIsomorphism := fun psi ↦
        passage.relation_implication block psi
          ((spath.blockWitness block).omega psi)
          ((spath.blockWitness block).blockIsomorphism psi) }

local instance subgroupFintype {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- A chosen irreducible representation affording an arbitrary function-valued
Brauer character.  It is selected from the witness already contained in
`IBr`; it is not an additional source assumption. -/
def chosenIBrRepresentation
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) (psi : IBr iota) :
    FDRep k G :=
  Classical.choose psi.2

/-- The selected representation affords the supplied Brauer character. -/
theorem chosenIBrRepresentation_character
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) (psi : IBr iota) :
    psi.1 = Representation.brauerCharacterOfRootEmbedding
      (chosenIBrRepresentation iota psi).ρ iota :=
  (Classical.choose_spec psi.2).2

/-! ## The quotient by the central character kernel -/

/-- A chosen irreducible representation affording a Brauer character in a
literal block fibre.  It is selected from the witness already contained in
`IBr`; it is not an additional source assumption. -/
def chosenBrauerRepresentation (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) : FDRep P.k P.H :=
  chosenIBrRepresentation P.iota psi.1

/-- The selected representation is irreducible. -/
theorem chosenBrauerRepresentation_irreducible (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) :
    Representation.IsIrreducible (chosenBrauerRepresentation P psi).ρ :=
  (Classical.choose_spec psi.1.2).1

/-- The selected representation affords the given Brauer character. -/
theorem chosenBrauerRepresentation_character (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) :
    psi.1.1 = Representation.brauerCharacterOfRootEmbedding
      (chosenBrauerRepresentation P psi).ρ P.iota :=
  chosenIBrRepresentation_character P.iota psi.1

/-- The literal subgroup `Z(H) cap ker(psi)`, represented as the intersection
of the centre with the kernel of a chosen representation affording `psi`. -/
def centralCharacterKernel (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) : Subgroup P.H :=
  Subgroup.center P.H ⊓ (chosenBrauerRepresentation P psi).ρ.ker

instance centralCharacterKernel_normal (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) : (centralCharacterKernel P psi).Normal := by
  let _ : (chosenBrauerRepresentation P psi).ρ.ker.Normal :=
    MonoidHom.normal_ker (chosenBrauerRepresentation P psi).ρ
  exact Subgroup.normal_inf_normal _ _

/-- The fixed quotient by the central character kernel. -/
abbrev CentralCharacterQuotient (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) :=
  P.H ⧸ centralCharacterKernel P psi

/-- The canonical quotient homomorphism. -/
abbrev centralCharacterQuotientMap (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) :
    P.H →* CentralCharacterQuotient P psi :=
  QuotientGroup.mk' (centralCharacterKernel P psi)

/-- Exact E1/U source data for the irreducible Brauer character on the
central quotient whose inflation is `psi`.  The equality is between actual
prime regular class functions. -/
structure CentralQuotientBrauerSource (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P) where
  iota : PrimeRegularRootEmbedding P.p P.k P.K
    (CentralCharacterQuotient P reference)
  brauer : IBr iota
  irreducibleBrauerInjective :
    IrreducibleBrauerCharacterInjectivity iota
  centralFaithful :
    Subgroup.center (CentralCharacterQuotient P reference) ⊓
        (chosenIBrRepresentation iota brauer).ρ.ker = ⊥
  inflation :
    PrimeRegularClassFunction.pullback
        (centralCharacterQuotientMap P reference) brauer.1 = psi.1.1

/-! ## The quotient weight and its local Brauer character -/

/-- The selected radical subgroup of a literal weight. -/
abbrev selectedRadical (P : Definition35Problem.{u})
    (w : Definition35Weight P) : Subgroup P.H :=
  SelectedRadical P.blockSource P.block w

/-- The image of the selected radical subgroup in the central quotient. -/
def quotientRadical (P : Definition35Problem.{u})
    (reference : Definition35Brauer P) (w : Definition35Weight P) :
    Subgroup (CentralCharacterQuotient P reference) :=
  (selectedRadical P w).map (centralCharacterQuotientMap P reference)

/-- The canonical homomorphism from `N_H(Q)/Q` to
`N_Hbar(Qbar)/Qbar`.  The central kernel has prime-to-`p` order and is not a
subgroup of the `p`-group `Q` in general, so this map must not be replaced by
the normal-core equivalence that assumes `ker(f) <= Q`. -/
def quotientNormalizerMap (P : Definition35Problem.{u})
    (reference : Definition35Brauer P) (w : Definition35Weight P) :
    NormalizerQuotient (selectedRadical P w) →*
      NormalizerQuotient (quotientRadical P reference w) := by
  let Q := selectedRadical P w
  let f := centralCharacterQuotientMap P reference
  let NG := Subgroup.normalizer (Q : Set P.H)
  let NH := Subgroup.normalizer ((Q.map f :
    Subgroup (CentralCharacterQuotient P reference)) :
      Set (CentralCharacterQuotient P reference))
  let R : Subgroup NG := Q.subgroupOf NG
  let S : Subgroup NH := (Q.map f).subgroupOf NH
  let fN : NG →* NH := normalizerMap f Q
  exact QuotientGroup.map R S fN (by
    intro q hq
    change f q.1 ∈ Q.map f
    exact ⟨q.1, hq, rfl⟩)

/-- Exact E1/U source data for the weight after passage to the
central character quotient.  `Qbar` is the fixed image of the selected
radical.  The ordinary character and its defect-zero property make this an
actual weight rather than merely a local Brauer character.  The two descent
equalities tie the quotient character data to the selected original weight
through the canonical normaliser-quotient homomorphism above. -/
structure QuotientWeightBrauerSource (P : Definition35Problem.{u})
    (reference : Definition35Brauer P) (w : Definition35Weight P) where
  radical : IsRadicalSubgroup P.p (quotientRadical P reference w)
  ordinary : OrdinaryIrreducibleCharacter.Irr P.K
    (NormalizerQuotient (quotientRadical P reference w))
  defectZero : IsDefectZeroOrdinaryCharacter P.p ordinary
  ordinaryDescends : ∀ x : NormalizerQuotient (selectedRadical P w),
    ordinary (quotientNormalizerMap P reference w x) =
      (selectedCharacterWeight P.blockSource P.block w).localCharacter x
  iota : PrimeRegularRootEmbedding P.p P.k P.K
    (NormalizerQuotient (quotientRadical P reference w))
  brauer : IBr iota
  reduction :
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      iota ordinary brauer
  brauerDescends :
    PrimeRegularClassFunction.pullback
        (quotientNormalizerMap P reference w) brauer.1 =
      (P.localReduction w).brauer.1

/-- Exact E1/U source data inflating the quotient local character from
`N_Hbar(Qbar)/Qbar` to `N_Hbar(Qbar)`.  The local library does not yet prove
irreducibility of this inflation, so the irreducible character and the
function equality are exposed explicitly. -/
structure QuotientLocalInflationSource (P : Definition35Problem.{u})
    (reference : Definition35Brauer P) (w : Definition35Weight P)
    (weight : QuotientWeightBrauerSource P reference w) where
  iota : PrimeRegularRootEmbedding P.p P.k P.K
    (Subgroup.normalizer (quotientRadical P reference w :
      Set (CentralCharacterQuotient P reference)))
  brauer : IBr iota
  inflation :
    PrimeRegularClassFunction.pullback
        (QuotientGroup.mk'
          ((quotientRadical P reference w).subgroupOf
            (Subgroup.normalizer (quotientRadical P reference w :
              Set (CentralCharacterQuotient P reference)))))
        weight.brauer.1 = brauer.1

/-! ## The concrete ambient extension group -/

/-- The right-action presentation of `Aut(Hbar)_psibar`. -/
abbrev QuotientBrauerAutomorphismStabilizer
    (P : Definition35Problem.{u}) (reference psi : Definition35Brauer P)
    (quotient : CentralQuotientBrauerSource P reference psi) :=
  MulAction.stabilizer
    (MulAut (CentralCharacterQuotient P reference))ᵐᵒᵖ quotient.brauer

/-- The group-theoretic part of Brough--Spath, Definition 4.3(ii)(1),
for the quotient by the central character kernel.  `base` is the literal
normal copy of the quotient group inside `A`. -/
structure SpathAmbientGroup (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P)
    (quotient : CentralQuotientBrauerSource P reference psi) where
  A : Type u
  [groupA : Group A]
  [fintypeA : Fintype A]
  base : Subgroup A
  [baseNormal : base.Normal]
  baseEquiv : CentralCharacterQuotient P reference ≃* base
  baseCentralizer_eq_center :
    Subgroup.centralizer (base : Set A) = Subgroup.center A
  centerPrimeTo : ¬ P.p ∣ Nat.card (Subgroup.center A)
  conjugation : A →* MulAut (CentralCharacterQuotient P reference)
  conjugation_on_base : ∀ (a : A)
      (h : CentralCharacterQuotient P reference),
    (baseEquiv (conjugation a h) : A) =
      a * (baseEquiv h : A) * a⁻¹
  automorphismQuotientEquiv :
    A ⧸ Subgroup.center A ≃*
      QuotientBrauerAutomorphismStabilizer P reference psi quotient
  automorphismQuotientEquiv_natural : ∀ a : A,
    ((automorphismQuotientEquiv
        (QuotientGroup.mk' (Subgroup.center A) a) :
          QuotientBrauerAutomorphismStabilizer P reference psi quotient) :
        (MulAut (CentralCharacterQuotient P reference))ᵐᵒᵖ) =
      inverseOpHom conjugation a

attribute [instance]
  SpathAmbientGroup.groupA SpathAmbientGroup.fintypeA
  SpathAmbientGroup.baseNormal

/-- The literal embedding of the central quotient as the normal subgroup
`base` of the ambient group. -/
def quotientToAmbient (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P)
    (quotient : CentralQuotientBrauerSource P reference psi)
    (ambient : SpathAmbientGroup P reference psi quotient) :
    CentralCharacterQuotient P reference →* ambient.A :=
  ambient.base.subtype.comp ambient.baseEquiv.toMonoidHom

/-- The image of the quotient radical in the ambient group. -/
def ambientRadical (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P) (w : Definition35Weight P)
    (quotient : CentralQuotientBrauerSource P reference psi)
    (ambient : SpathAmbientGroup P reference psi quotient) : Subgroup ambient.A :=
  (quotientRadical P reference w).map
    (quotientToAmbient P reference psi quotient ambient)

/-- The actual local ambient group `N_A(Qbar)`. -/
abbrev AmbientLocalGroup (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P) (w : Definition35Weight P)
    (quotient : CentralQuotientBrauerSource P reference psi)
    (ambient : SpathAmbientGroup P reference psi quotient) :=
  Subgroup.normalizer
    (ambientRadical P reference psi w quotient ambient : Set ambient.A)

/-- The subgroup `N_A(Qbar) cap Hbar`, represented inside the local ambient
group. -/
def AmbientLocalBase (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P) (w : Definition35Weight P)
    (quotient : CentralQuotientBrauerSource P reference psi)
    (ambient : SpathAmbientGroup P reference psi quotient) :
    Subgroup (AmbientLocalGroup P reference psi w quotient ambient) :=
  ambient.base.comap
    (AmbientLocalGroup P reference psi w quotient ambient).subtype

/-- The global and local character extensions required in Definition
4.3(ii)(2)--(3).  The local equivalence identifies the normaliser in the
quotient group with the intersection `N_A(Qbar) cap Hbar`. -/
structure SpathCharacterExtensions (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P) (w : Definition35Weight P)
    (quotient : CentralQuotientBrauerSource P reference psi)
    (weight : QuotientWeightBrauerSource P reference w)
    (localInflation :
      QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient) where
  ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A
  globalExtension :
    Representation.Extension.BrauerCharacterExtensionWitness
      ambientRoot
      (quotient.iota.alongMulEquiv ambient.baseEquiv)
      (IrreducibleBrauerCharacter.alongMulEquiv
        quotient.iota ambient.baseEquiv quotient.brauer)
  localBaseEquiv :
    Subgroup.normalizer (quotientRadical P reference w :
      Set (CentralCharacterQuotient P reference)) ≃*
      AmbientLocalBase P reference psi w quotient ambient
  localBaseEquiv_natural : ∀ n :
      Subgroup.normalizer (quotientRadical P reference w :
        Set (CentralCharacterQuotient P reference)),
    (localBaseEquiv n).1.1 =
      quotientToAmbient P reference psi quotient ambient n.1
  localAmbientRoot : PrimeRegularRootEmbedding P.p P.k P.K
    (AmbientLocalGroup P reference psi w quotient ambient)
  localExtension :
    Representation.Extension.BrauerCharacterExtensionWitness
      localAmbientRoot
      (localInflation.iota.alongMulEquiv localBaseEquiv)
      (IrreducibleBrauerCharacter.alongMulEquiv
        localInflation.iota localBaseEquiv localInflation.brauer)

/-- The actual subgroup `N_J(Qbar)` for an intermediate subgroup `J` of
the ambient group, expressed as `J cap N_A(Qbar)`. -/
def IntermediateLocalNormalizer {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P} {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (J : Subgroup ambient.A) : Subgroup J :=
  (AmbientLocalGroup P reference psi w quotient ambient).comap J.subtype

/-- The canonical inclusion `N_J(Qbar) -> N_A(Qbar)`. -/
def intermediateLocalToAmbientLocal {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P} {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (J : Subgroup ambient.A) :
    IntermediateLocalNormalizer (w := w) ambient J →*
      AmbientLocalGroup P reference psi w quotient ambient where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Literal block equality at one intermediate subgroup.

The two Brauer characters are actual restrictions of the supplied global and
local extensions.  Their block labels are computed in complete families of
primitive central idempotents, and catalogues supply the corresponding block
central characters.  The last field states the literal `BlockInducesTo`
relation between the selected local and global blocks.  Thus no function from
local blocks to global blocks is supplied.  The structure remains graded E2/U
because definedness of the induced central function and its equality with the
selected global block central character are not yet derived from the published
representation theoretic hypotheses. -/
structure IntermediateBlockEqualityAt (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P) (w : Definition35Weight P)
    (quotient : CentralQuotientBrauerSource P reference psi)
    (weight : QuotientWeightBrauerSource P reference w)
    (localInflation :
      QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient)
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient)
    (J : Subgroup ambient.A) where
  globalRoot : PrimeRegularRootEmbedding P.p P.k P.K J
  globalBrauer : IBr globalRoot
  globalRestriction :
    PrimeRegularClassFunction.pullback J.subtype
        extensions.globalExtension.1.1 = globalBrauer.1
  localRoot : PrimeRegularRootEmbedding P.p P.k P.K
    (IntermediateLocalNormalizer (w := w) ambient J)
  localBrauer : IBr localRoot
  localRestriction :
    PrimeRegularClassFunction.pullback
        (intermediateLocalToAmbientLocal (w := w) ambient J)
        extensions.localExtension.1.1 = localBrauer.1
  GlobalBlock : Type u
  LocalBlock : Type u
  [fintypeGlobalBlock : Fintype GlobalBlock]
  [fintypeLocalBlock : Fintype LocalBlock]
  globalBlockIdempotent : GlobalBlock → P.k[J]
  localBlockIdempotent : LocalBlock →
    P.k[IntermediateLocalNormalizer (w := w) ambient J]
  globalBlocks : BlockIdempotentDecomposition globalBlockIdempotent
  localBlocks : BlockIdempotentDecomposition localBlockIdempotent
  globalBrauerInjective : IrreducibleBrauerCharacterInjectivity globalRoot
  localBrauerInjective : IrreducibleBrauerCharacterInjectivity localRoot
  globalCentralCharacters : BlockCentralCharacterCatalogue globalBlocks
  localCentralCharacters : BlockCentralCharacterCatalogue localBlocks
  globalCentralCharactersNavarro311 :
    ModularRep.Navarro311CatalogueProvenance P.p P.iota.prime
      globalBlocks globalCentralCharacters
  localCentralCharactersNavarro311 :
    ModularRep.Navarro311CatalogueProvenance P.p P.iota.prime
      localBlocks localCentralCharacters
  inductionEquality :
    ModularRep.BlockInducesTo
      (IntermediateLocalNormalizer (w := w) ambient J)
      localCentralCharacters globalCentralCharacters
      (irreducibleBrauerCharacterBlock localRoot localBrauerInjective
        localBlocks localBrauer)
      (irreducibleBrauerCharacterBlock globalRoot globalBrauerInjective
        globalBlocks globalBrauer)

attribute [instance]
  IntermediateBlockEqualityAt.fintypeGlobalBlock
  IntermediateBlockEqualityAt.fintypeLocalBlock

/-- Narrow E2/U interface for all actual intermediate subgroups in
Brough--Spath, Definition 4.3(ii)(4). -/
structure IntermediateBlockSource (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P) (w : Definition35Weight P)
    (quotient : CentralQuotientBrauerSource P reference psi)
    (weight : QuotientWeightBrauerSource P reference w)
    (localInflation :
      QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient)
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) where
  equalityAt : ∀ (J : Subgroup ambient.A), ambient.base ≤ J →
    IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient extensions J

/-- The quotient-dependent tail of the concrete data required for one
matched Brauer character and weight.

Separating this tail from the quotient source lets specialised constructors
fix the quotient canonically before supplying the weight, ambient-group,
extension, and intermediate-block data.  The intermediate-block boundary is
unchanged. -/
structure SpathMatchedBlockConditionTail (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (quotient : CentralQuotientBrauerSource P reference psi) where
  weight : QuotientWeightBrauerSource P reference w
  localInflation : QuotientLocalInflationSource P reference w weight
  ambient : SpathAmbientGroup P reference psi quotient
  extensions : SpathCharacterExtensions P reference psi w quotient weight
    localInflation ambient
  intermediateBlocks : IntermediateBlockSource P reference psi w
    quotient weight localInflation ambient extensions

/-- All concrete data required for one matched Brauer character and weight
after quotienting by the central character kernel.

The quotient is stored separately from its dependent tail.  This preserves
the general carrier while allowing centreless conversions to use the
canonical quotient source rather than accept an arbitrary one. -/
structure SpathMatchedBlockCondition (P : Definition35Problem.{u})
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P) where
  quotient : CentralQuotientBrauerSource P reference psi
  tail : SpathMatchedBlockConditionTail P reference psi w quotient

namespace SpathMatchedBlockCondition

variable {P : Definition35Problem.{u}}
variable {reference psi : Definition35Brauer P}
variable {w : Definition35Weight P}

/-- Backwards-compatible access to the quotient-weight datum in the
dependent tail. -/
abbrev weight (condition : SpathMatchedBlockCondition P reference psi w) :=
  condition.tail.weight

/-- Backwards-compatible access to local inflation in the dependent tail. -/
abbrev localInflation
    (condition : SpathMatchedBlockCondition P reference psi w) :=
  condition.tail.localInflation

/-- Backwards-compatible access to the ambient group in the dependent
tail. -/
abbrev ambient
    (condition : SpathMatchedBlockCondition P reference psi w) :=
  condition.tail.ambient

/-- Backwards-compatible access to the character extensions in the
dependent tail. -/
abbrev extensions
    (condition : SpathMatchedBlockCondition P reference psi w) :=
  condition.tail.extensions

/-- Backwards-compatible access to the intermediate block source. -/
abbrev intermediateBlocks
    (condition : SpathMatchedBlockCondition P reference psi w) :=
  condition.tail.intermediateBlocks

end SpathMatchedBlockCondition

/-! ## Fixed block and family carriers -/

/-- Exact E1/U source data for the fixed central quotient in the paragraph
following Brough--Spath, Remark 4.4.  This quotient need not itself be the
maximal cover.  The commutative formula ties its map to the already fixed
maximal covering map, so this is not an unrelated abstract presentation of
the simple quotient. -/
structure CentralQuotientCoverSource {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H) (block : family.Block)
    (reference : Definition35Brauer (family.problem block)) where
  quotientToSimple :
    CentralCharacterQuotient (family.problem block) reference →* cover.S
  quotientToSimple_comp :
    quotientToSimple.comp
        (centralCharacterQuotientMap (family.problem block) reference) =
      cover.quotient
  quotientToSimple_surjective : Function.Surjective quotientToSimple
  quotient_kernel : quotientToSimple.ker =
    Subgroup.center
      (CentralCharacterQuotient (family.problem block) reference)
  perfect : commutator
      (CentralCharacterQuotient (family.problem block) reference) = ⊤
  centerPrimeTo : ¬ ell ∣ Nat.card
    (Subgroup.center
      (CentralCharacterQuotient (family.problem block) reference))

/-- A fixed block-condition witness relative to the exact block induction
relations at intermediate subgroups.

One reference character fixes a single central kernel, quotient group, and
quotient block for the whole original block.  Every other character is
descended to that same quotient and its matched datum includes the central
faithfulness required before applying Brough--Spath, Definition 4.3.  The
acting group is identified with the actual block stabiliser.  This carrier is
not named BAW-good because `IntermediateBlockEqualityAt.inductionEquality`
remains E2/U evidence for the definedness and central character equality in
the block induction relation. -/
structure RelativeBlockConditionWitness {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (block : family.Block) where
  automorphismStabilizer :
    Definition35AutomorphismStabilizerAdapter (family.problem block)
  omega : Definition35Brauer (family.problem block) ≃
    Definition35Weight (family.problem block)
  equivariant : Definition35Equivariant (family.problem block) omega
  reference : Definition35Brauer (family.problem block)
  /-- E1/U bridge asserting that the representation theoretic kernel is
  constant on the literal block fibre.  The block library proves equality of
  central characters for canonical simple-module representatives.  It does
  not yet transport block support and kernels from the arbitrary affording
  representation stored in `IBr` to that canonical representative. -/
  commonCentralKernel : ∀ psi : Definition35Brauer (family.problem block),
    centralCharacterKernel (family.problem block) psi =
      centralCharacterKernel (family.problem block) reference
  quotientCover :
    CentralQuotientCoverSource family cover block reference
  QuotientBlock : Type u
  [fintypeQuotientBlock : Fintype QuotientBlock]
  quotientBlockIdempotent : QuotientBlock →
    family.k[CentralCharacterQuotient
      (family.problem block) reference]
  quotientBlocks :
    BlockIdempotentDecomposition quotientBlockIdempotent
  quotientBlock : QuotientBlock
  matched : ∀ psi : Definition35Brauer (family.problem block),
    SpathMatchedBlockCondition
      (family.problem block) reference psi (omega psi)
  /-- One-way E1/U quotient-block membership.  This does not assert that
  every irreducible Brauer character of the quotient block is the descent of
  a character in the original block, and is therefore insufficient on its
  own for BAW-goodness. -/
  descendedBrauer_liesInQuotientBlock :
    ∀ psi : Definition35Brauer (family.problem block),
      irreducibleBrauerCharacterBlock
          (matched psi).quotient.iota
          (matched psi).quotient.irreducibleBrauerInjective
          quotientBlocks (matched psi).quotient.brauer =
        quotientBlock

attribute [instance] RelativeBlockConditionWitness.fintypeQuotientBlock

/-- A relative block-condition witness for every literal block in one
`Definition35Family`.  This is still relative to the E2/U block induction
relations inside each block witness. -/
structure RelativeBlockConditionFamilyWitness {ell : ℕ}
    (family : Definition35Family.{u} ell) where
  cover : EllPrimeCoverSource ell family.H
  blockWitness : ∀ block : family.Block,
    RelativeBlockConditionWitness family cover block

/-! ## One-way centreless equation (3.17) bridge -/

/-- Exact E2 source interface for the centreless specialisation of the
sufficient criterion in Feng--Li--Zhang, Section 3.5.  The imported
`Equation317Witness` assumes that the centre of the original group is
trivial, so the central character quotient here has trivial kernel.  This is
not a generic quotient-and-lift form of equation (3.17).  The implication is
indexed by the fixed relation and cannot be replaced by a caller-selected
result predicate. -/
structure Equation317ToRelativeBlockConditionSource {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (block : family.Block)
    (automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block))
    (source : Equation317SourceSemantics (family.problem block) automorphisms
      cover) where
  reference : Definition35Brauer (family.problem block)
  /-- The same E1/U arbitrary-affording-representation bridge as in
  `RelativeBlockConditionWitness.commonCentralKernel`. -/
  commonCentralKernel : ∀ psi : Definition35Brauer (family.problem block),
    centralCharacterKernel (family.problem block) psi =
      centralCharacterKernel (family.problem block) reference
  quotientCover :
    CentralQuotientCoverSource family cover block reference
  QuotientBlock : Type u
  [fintypeQuotientBlock : Fintype QuotientBlock]
  quotientBlockIdempotent : QuotientBlock →
    family.k[CentralCharacterQuotient
      (family.problem block) reference]
  quotientBlocks :
    BlockIdempotentDecomposition quotientBlockIdempotent
  quotientBlock : QuotientBlock
  matched : ∀ (psi : Definition35Brauer (family.problem block))
      (w : Definition35Weight (family.problem block)),
    source.equation317BlockIsomorphic psi w →
      SpathMatchedBlockCondition
        (family.problem block) reference psi w
  descendedBrauer_liesInQuotientBlock :
    ∀ (psi : Definition35Brauer (family.problem block))
      (w : Definition35Weight (family.problem block))
      (hrelation : source.equation317BlockIsomorphic psi w),
      irreducibleBrauerCharacterBlock
          (matched psi w hrelation).quotient.iota
          (matched psi w hrelation).quotient.irreducibleBrauerInjective
          quotientBlocks (matched psi w hrelation).quotient.brauer =
        quotientBlock

attribute [instance]
  Equation317ToRelativeBlockConditionSource.fintypeQuotientBlock

/-- The cited one-way conversion from a centreless equation-(3.17) witness
to the relative Brough--Spath block-condition carrier.  No converse or
noncentreless version is asserted. -/
def Equation317Witness.toRelativeBlockCondition
    {ell : ℕ} {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {block : family.Block}
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    {source : Equation317SourceSemantics
      (family.problem block) automorphisms cover}
    (conversion : Equation317ToRelativeBlockConditionSource
      family cover block automorphisms source)
    (witness : Equation317Witness
      (family.problem block) automorphisms cover source) :
    RelativeBlockConditionWitness family cover block where
  automorphismStabilizer := automorphisms
  omega := witness.omega
  equivariant := witness.equivariant
  reference := conversion.reference
  commonCentralKernel := conversion.commonCentralKernel
  quotientCover := conversion.quotientCover
  QuotientBlock := conversion.QuotientBlock
  fintypeQuotientBlock := conversion.fintypeQuotientBlock
  quotientBlockIdempotent := conversion.quotientBlockIdempotent
  quotientBlocks := conversion.quotientBlocks
  quotientBlock := conversion.quotientBlock
  matched := fun psi ↦ conversion.matched psi (witness.omega psi)
    (witness.blockIsomorphism psi)
  descendedBrauer_liesInQuotientBlock := fun psi ↦
    conversion.descendedBrauer_liesInQuotientBlock psi (witness.omega psi)
      (witness.blockIsomorphism psi)

/-- Separately graded equation-(3.17)-to-Brough--Spath conversion data for
every block in one covered family.

Both the semantic relation and every blockwise conversion are indexed by the
single concrete `cover` parameter.  This carrier contains no application of
Feng--Li--Zhang, Theorem 5.7 and no intermediate iBAW conclusion. -/
structure Equation317ToRelativeBlockConditionFamilySource {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      Equation317SourceSemantics (family.problem block) (automorphisms block)
        cover) where
  conversion : ∀ block : family.Block,
    Equation317ToRelativeBlockConditionSource family cover block
      (automorphisms block) (source block)

/-- Combine the relative Brough--Spath carrier from a strong
equation-(3.17) family and the separately supplied blockwise conversions.
The output stores exactly the same concrete cover used by the semantic
relations and witnesses. -/
def Equation317FamilyWitness.toRelativeBlockConditionFamily
    {ell : ℕ} {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {source : ∀ block : family.Block,
      Equation317SourceSemantics (family.problem block) (automorphisms block)
        cover}
    (conversion : Equation317ToRelativeBlockConditionFamilySource
      family cover automorphisms source)
    (witness : Equation317FamilyWitness family cover automorphisms source) :
    RelativeBlockConditionFamilyWitness family where
  cover := cover
  blockWitness := fun block ↦
    Equation317Witness.toRelativeBlockCondition
      (conversion.conversion block) (witness.blockWitness block)

end ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
