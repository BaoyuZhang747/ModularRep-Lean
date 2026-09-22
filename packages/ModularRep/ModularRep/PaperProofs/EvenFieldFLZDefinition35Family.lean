import ModularRep.PaperProofs.EvenFieldFLZSourceConditions

/-!
# A common family of Feng--Li--Zhang Definition 3.5 problems

Feng--Li--Zhang, Hypothesis 5.5, uses one coefficient prime and the blocks of
one finite fixed-point group at a time.  This module packages that common
data before any model of the source class `H_G` is introduced.

`Definition35Family` fixes the coefficient prime, modular system, finite
group, complete set of blocks and decomposition, local block-induction
source, and transport of Brauer blocks.  For each literal block, the acting
stabiliser group and its homomorphism to automorphisms may be different, as
may the chosen Brauer reduction of a local defect-zero character.

The canonical constructor `Definition35Family.problem` returns the existing
`Definition35Problem`.  Its coefficient prime, finite group, block type,
block decomposition, and local block source are definitionally the common
family data.  `Definition35IBAWFamilyWitness` packages the fixed
Definition 3.5 iBAW-bijection content, while
`Equation317FamilyWitness` packages the strictly stronger equation (3.17)
route.  Only the latter fixes one concrete universal prime-to-`ell` cover for
the whole family.  This file applies no source theorem and contains no
arbitrary target predicate or caller-selectable conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZDefinition35Family

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- Block-dependent stabiliser data for a common literal finite group and
set of blocks.  `Gamma` is allowed to depend on the selected block.  Its
action is the canonical right action induced by `gamma`; no character or
weight bijection is stored here. -/
structure Definition35BlockAutomorphisms
    (H Block : Type u) [Group H]
    [MulAction (MulAut H)ᵐᵒᵖ Block] (block : Block) where
  Gamma : Type u
  [groupGamma : Group Gamma]
  [finiteGamma : Finite Gamma]
  gamma : Gamma →* MulAut H
  gammaBlock_fixed : ∀ a : Gamma,
    inverseOpHom gamma a • block = block

attribute [instance]
  Definition35BlockAutomorphisms.groupGamma
  Definition35BlockAutomorphisms.finiteGamma

/-- Common literal data for all Definition 3.5 block problems belonging to
one finite group at one coefficient prime.

Only the stabiliser presentation and selected local reduction vary with the
block.  In particular, `BlockIdempotentDecomposition` certifies the single
complete set of blocks used by every problem in the family. -/
structure Definition35Family (ell : ℕ) where
  ellPrime : Nat.Prime ell
  k : Type u
  K : Type u
  H : Type u
  Block : Type u
  [fieldk : Field k]
  [fieldK : Field K]
  [charPk : CharP k ell]
  [algClosedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  [groupH : Group H]
  [fintypeH : Fintype H]
  [fintypeBlock : Fintype Block]
  [blockAction : MulAction (MulAut H)ᵐᵒᵖ Block]
  blockIdempotent : Block → k[H]
  iota : PrimeRegularRootEmbedding ell k K H
  irreducibleBrauerInjective : IrreducibleBrauerCharacterInjectivity iota
  blocks : BlockIdempotentDecomposition blockIdempotent
  blockSource : LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := H) (Block := Block)
  brauerBlock_transport : ∀
      (alpha : (MulAut H)ᵐᵒᵖ) (psi : IBr iota),
    irreducibleBrauerCharacterBlock iota irreducibleBrauerInjective blocks
        (alpha • psi) =
      alpha • irreducibleBrauerCharacterBlock iota
        irreducibleBrauerInjective blocks psi
  automorphisms : ∀ block : Block,
    Definition35BlockAutomorphisms H Block block
  localReduction : ∀ (block : Block)
      (w : LiteralWeightFibre blockSource block),
    SelectedLocalReductionSource blockSource block w

attribute [instance]
  Definition35Family.fieldk Definition35Family.fieldK
  Definition35Family.charPk Definition35Family.algClosedk
  Definition35Family.charZeroK Definition35Family.groupH
  Definition35Family.fintypeH Definition35Family.fintypeBlock
  Definition35Family.blockAction

/-- The canonical Definition 3.5 problem attached to a literal block in the
family.  The common prime, group, set of blocks, decomposition, and local
block-induction source are reused without transport or equality casts. -/
def Definition35Family.problem
    {ell : ℕ} (family : Definition35Family ell)
    (block : family.Block) : Definition35Problem where
  p := ell
  k := family.k
  K := family.K
  H := family.H
  Gamma := (family.automorphisms block).Gamma
  Block := family.Block
  fieldk := family.fieldk
  fieldK := family.fieldK
  charPk := family.charPk
  algClosedk := family.algClosedk
  charZeroK := family.charZeroK
  groupH := family.groupH
  fintypeH := family.fintypeH
  groupGamma := (family.automorphisms block).groupGamma
  finiteGamma := (family.automorphisms block).finiteGamma
  fintypeBlock := family.fintypeBlock
  blockAction := family.blockAction
  blockIdempotent := family.blockIdempotent
  iota := family.iota
  irreducibleBrauerInjective := family.irreducibleBrauerInjective
  blocks := family.blocks
  blockSource := family.blockSource
  block := block
  gamma := (family.automorphisms block).gamma
  gammaBlock_fixed := (family.automorphisms block).gammaBlock_fixed
  brauerBlock_transport := family.brauerBlock_transport
  localReduction := family.localReduction block

@[simp]
theorem Definition35Family.problem_p
    {ell : ℕ} (family : Definition35Family ell)
    (block : family.Block) :
    (family.problem block).p = ell := rfl

@[simp]
theorem Definition35Family.problem_H
    {ell : ℕ} (family : Definition35Family ell)
    (block : family.Block) :
    (family.problem block).H = family.H := rfl

@[simp]
theorem Definition35Family.problem_Block
    {ell : ℕ} (family : Definition35Family ell)
    (block : family.Block) :
    (family.problem block).Block = family.Block := rfl

@[simp]
theorem Definition35Family.problem_block
    {ell : ℕ} (family : Definition35Family ell)
    (block : family.Block) :
    (family.problem block).block = block := rfl

/-- Transport a Brauer character in one block fibre to the transported block
fibre under the canonical right action of a group automorphism. -/
def Definition35Family.transportBrauer
    {ell : ℕ} (family : Definition35Family.{u} ell)
    (alpha : (MulAut family.H)ᵐᵒᵖ)
    {block : family.Block}
    (psi : Definition35Brauer (family.problem block)) :
    Definition35Brauer (family.problem (alpha • block)) := by
  change BrauerFibre family.iota family.irreducibleBrauerInjective
    family.blocks block at psi
  change BrauerFibre family.iota family.irreducibleBrauerInjective
    family.blocks (alpha • block)
  refine ⟨alpha • psi.1, ?_⟩
  exact
    (family.brauerBlock_transport alpha psi.1).trans
      (congrArg (fun b : family.Block ↦ alpha • b) psi.2)

/-- Transport a weight in one block fibre to the transported block fibre
under the canonical right action of a group automorphism. -/
def Definition35Family.transportWeight
    {ell : ℕ} (family : Definition35Family.{u} ell)
    (alpha : (MulAut family.H)ᵐᵒᵖ)
    {block : family.Block}
    (weight : Definition35Weight (family.problem block)) :
    Definition35Weight (family.problem (alpha • block)) := by
  change WeightFibre family.blockSource block at weight
  change WeightFibre family.blockSource (alpha • block)
  refine ⟨alpha • weight.1, ?_⟩
  change
    family.blockSource.weightBlock (alpha • weight.1) =
      alpha • block
  exact
    (family.blockSource.weightBlock_transport alpha weight.1).trans
      (congrArg (fun b : family.Block ↦ alpha • b) weight.2)

/-! ## Definition 3.5 iBAW-bijections on one family -/

/-- A fixed Definition 3.5 iBAW-bijection for every block in one family.

The automorphism-stabiliser adapters and Definition 3.5 source semantics are
fixed for the whole family before a block is selected.  Hypothesis 5.5(b)
uses this cover-free carrier on arbitrary fixed-point groups.  No
equation-(3.17) relation and no BAW-goodness predicate is required or
produced. -/
structure Definition35IBAWFamilyWitness {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) where
  blockWitness : ∀ block : family.Block,
    Definition35IBAWBijection (family.problem block) (automorphisms block)
      (source block)

/-! ## Equation (3.17) on one fixed covered family -/

/-- A strong equation-(3.17) witness for every literal block in one family.

The concrete universal prime-to-`ell` cover is a parameter of the whole
carrier.  Each block relation is therefore interpreted using literally the
same cover object, rather than a cover proposition or a blockwise choice. -/
structure Equation317FamilyWitness {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      Equation317SourceSemantics (family.problem block) (automorphisms block)
        cover) where
  blockWitness : ∀ block : family.Block,
    Equation317Witness (family.problem block) (automorphisms block) cover
      (source block)

end ModularRep.PaperProofs.EvenFieldFLZDefinition35Family


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
