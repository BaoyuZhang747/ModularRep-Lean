import ModularRep.CharacterWeightBlockAssignment
import ModularRep.IBrBlock
import ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

/-!
# Proposition 4.11 on sets of blocks and weights

This file isolates the remaining object-level adapter for the exceptional
group `3.Omega_7(3)` in manuscript Proposition 4.11.  It does not assume an
iBAW/BAW conclusion, `BlockGood`, or a Brauer--weight equivalence.

The nine computed block labels are realised by a complete family of literal
primitive central idempotents of the modular group algebra.  Lean proves that
this family identifies the nine labels bijectively with *all* primitive
blocks; injectivity, surjectivity, cardinality, the outer-generator formula,
and the faithful-block stabiliser consequence are separate declarations.

The radical transcript is represented losslessly by a dependent label
`(radical row, central sector, occurrence in the printed local-character
list)`.  Thus repeated local table positions in different quotient tables
cannot be conflated.  A literal weight map supplies a raw
`CharacterWeight`; Lean then takes both honest quotients to obtain
`CharacterWeight.ConjugacyClass`.  Injectivity, surjectivity, outer-action
compatibility, and compatibility with the block obtained by local block
induction are deliberately separate hypotheses.  From those narrow
properties Lean constructs the global and block-fibre equivalences, transports
counts and fixed points, and proves stabiliser equivariance on faithful
literal block fibres.

The archived GAP/CTblLib outputs do not currently provide the object-level
witnesses required to instantiate this file.  A strengthened certificate
must export:

* nine actual elements of `k[3.Omega_7(3)]`, together with completeness,
  orthogonality and primitivity proofs, and the action of one chosen outer
  representative on those elements;
* for every one of the 33 Brauer positions, the corresponding
  function-valued irreducible Brauer character, with injectivity,
  surjectivity, block membership, and outer-action witnesses;
* for every radical-output occurrence, an embedded radical subgroup and a
  function-valued defect-zero local character (hence a raw
  `CharacterWeight`), together with fusion witnesses proving injectivity,
  completeness witnesses proving surjectivity, its induced ambient block,
  and, if the computed outer action is to be used, the full permutation of
  these occurrences.

Table positions, subgroup orders, character degrees, and final cardinalities
alone cannot instantiate these maps.  The cover, outer quotient, inner
fixation, and routine group identifications remain E1/E2 source inputs; they
are not reproved here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual

open Formalisation.ComputationArithmetic
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative

universe u

/-! ## Exact carriers for the existing E3 transcript -/

/-- An index into the twelve retained `G_RADICAL` rows. -/
abbrev RadicalOutputRow := Fin radicalClassContributions.length

private instance q3SectorFintype : Fintype Q3Sector :=
  derive_fintype% Q3Sector

/-- One local defect-zero-character occurrence in `o7radical.out`.

The printed character position is only local to the quotient table in its
radical row.  Retaining the row and the occurrence index prevents accidental
identification of equal natural-number positions from different tables. -/
abbrev WeightOutputLabel :=
  Sigma fun row : RadicalOutputRow =>
    Sigma fun sector : Q3Sector =>
      Fin ((radicalClassContributions.get row).labels sector).length

deriving instance DecidableEq for WeightOutputLabel

namespace WeightOutputLabel

/-- The central-sector label printed for an output occurrence. -/
def sector (label : WeightOutputLabel) : Q3Sector := label.2.1

/-- The printed local character-table position of an output occurrence. -/
def localCharacterPosition (label : WeightOutputLabel) : Nat :=
  ((radicalClassContributions.get label.1).labels label.2.1).get label.2.2

/-- The exact dependent output carrier has 33 occurrences. -/
theorem card : Fintype.card WeightOutputLabel = 33 := by
  decide

/-- The sector fibres of the exact output carrier have the printed totals
`(17,8,8)`. -/
theorem sector_fibre_card (s : Q3Sector) :
    Fintype.card {label : WeightOutputLabel // label.sector = s} =
      radicalSectorTotal s := by
  cases s <;> decide

theorem sector_fibre_card_exact :
    Fintype.card {label : WeightOutputLabel // label.sector = .trivial} = 17 ∧
      Fintype.card
        {label : WeightOutputLabel // label.sector = .faithfulOne} = 8 ∧
      Fintype.card
        {label : WeightOutputLabel // label.sector = .faithfulTwo} = 8 := by
  decide

end WeightOutputLabel

/-- The exact Brauer-label fibre over one computed block label. -/
abbrev BrauerOutputFibre (block : Q3Block) :=
  {label : BrauerLabel // blockOfBrauerLabel label = block}

/-- The transcript itself determines every Brauer block-fibre cardinality. -/
theorem brauerOutputFibre_card (block : Q3Block) :
    Fintype.card (BrauerOutputFibre block) = q3BrauerCount block := by
  cases block <;> decide

/-! ## The literal set of primitive central idempotents -/

/-- Literal blocks of the modular group algebra. -/
abbrev PrimitiveBlock (k X : Type u) [Field k] [Group X] :=
  {b : k[X] // IsPrimitiveCentralIdempotent b}

variable {k K X : Type u}
variable [Field k] [Field K] [CharZero K] [Group X] [Fintype X]

/-- The literal primitive block attached to a computed block label by a
complete block-idempotent decomposition. -/
def primitiveBlockOfLabel
    {blockIdempotent : Q3Block -> k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : Q3Block) : PrimitiveBlock k X :=
  ⟨blockIdempotent block, blocks.primitive block⟩

/-- Orthogonality and nonzeroness make the literal block map injective. -/
theorem primitiveBlockOfLabel_injective
    {blockIdempotent : Q3Block -> k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent) :
    Function.Injective (primitiveBlockOfLabel blocks) := by
  intro left right heq
  by_contra hne
  have hvalues : blockIdempotent left = blockIdempotent right :=
    congrArg Subtype.val heq
  apply (blocks.primitive left).ne_zero
  calc
    blockIdempotent left = blockIdempotent left * blockIdempotent left :=
      (blocks.primitive left).idempotent.eq.symm
    _ = blockIdempotent left * blockIdempotent right := by rw [hvalues]
    _ = 0 := blocks.complete.ortho hne

/-- Completeness and primitivity make the literal block map surjective onto
all primitive central idempotents, not merely onto a preselected block type. -/
theorem primitiveBlockOfLabel_surjective
    {blockIdempotent : Q3Block -> k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent) :
    Function.Surjective (primitiveBlockOfLabel blocks) := by
  intro actual
  let index : Q3Block := actual.2.support blocks.complete
  refine ⟨index, Subtype.ext ?_⟩
  have hsupport : actual.1 * blockIdempotent index = actual.1 := by
    exact actual.2.mul_support blocks.complete
  have hzeroOrEqual :=
    (blocks.primitive index).eq_zero_or_eq_self actual.1
      actual.2.idempotent actual.2.central hsupport
  exact (hzeroOrEqual.resolve_left actual.2.ne_zero).symm

/-- The actual equivalence from computed block labels to all primitive
blocks.  Its two bijectivity components are proved separately above. -/
def primitiveBlockEquiv
    {blockIdempotent : Q3Block -> k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent) :
    Q3Block ≃ PrimitiveBlock k X :=
  Equiv.ofBijective (primitiveBlockOfLabel blocks)
    ⟨primitiveBlockOfLabel_injective blocks,
      primitiveBlockOfLabel_surjective blocks⟩

/-- Finiteness of the literal set of primitive central idempotents is a consequence of
the source map, rather than a carrier assumption. -/
@[instance_reducible] def primitiveBlockFintype
    {blockIdempotent : Q3Block -> k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent) :
    Fintype (PrimitiveBlock k X) :=
  Fintype.ofEquiv Q3Block (primitiveBlockEquiv blocks)

/-- There are exactly nine literal primitive blocks in the supplied complete
family. -/
theorem primitiveBlock_card
    {blockIdempotent : Q3Block -> k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent) :
    let _ := primitiveBlockFintype blocks
    Fintype.card (PrimitiveBlock k X) = 9 := by
  let _ := primitiveBlockFintype blocks
  calc
    Fintype.card (PrimitiveBlock k X) = Fintype.card Q3Block :=
      (Fintype.card_congr (primitiveBlockEquiv blocks)).symm
    _ = 9 := by decide

/-! ## Literal maps for the Brauer and weight output labels -/

variable [CharP k 2] [IsAlgClosed k]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)

/-- Object-level realisation of the 33 CTblLib Brauer positions.  The record
contains only the map; bijectivity, block membership, and action compatibility
remain separate certificate properties below. -/
structure LiteralBrauerOutputMap where
  character : BrauerLabel -> IBr iota

namespace LiteralBrauerOutputMap

variable (M : LiteralBrauerOutputMap iota)

/-- A bijection is constructed only after injectivity and completeness have
been supplied separately. -/
def equiv (map_injective : Function.Injective M.character)
    (map_surjective : Function.Surjective M.character) :
    BrauerLabel ≃ IBr iota :=
  Equiv.ofBijective M.character ⟨map_injective, map_surjective⟩

end LiteralBrauerOutputMap

/-- A raw literal-weight witness for every occurrence in the radical output.
Taking isomorphism classes and then ambient conjugacy classes is performed by
Lean in `classOfLabel`. -/
structure LiteralWeightOutputMap where
  rawWeight : WeightOutputLabel -> CharacterWeight 2 K X

namespace LiteralWeightOutputMap

variable (M : LiteralWeightOutputMap (K := K) (X := X))

/-- The actual conjugacy class represented by an output occurrence. -/
def classOfLabel (label : WeightOutputLabel) :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := X) :=
  Quotient.mk'' (Quotient.mk'' (M.rawWeight label))

/-- The global output-to-weight equivalence, constructed from separately
supplied nonduplication and completeness witnesses. -/
def equiv (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel) :
    WeightOutputLabel ≃
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := X) :=
  Equiv.ofBijective M.classOfLabel ⟨map_injective, map_surjective⟩

/-- Finiteness of the literal set of weights follows from the object map. -/
@[instance_reducible] def actualWeightFintype
    (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel) :
    Fintype (CharacterWeight.ConjugacyClass
      (p := 2) (K := K) (G := X)) :=
  Fintype.ofEquiv WeightOutputLabel (M.equiv map_injective map_surjective)

/-- The literal character-weight conjugacy class carrier has 33 elements. -/
theorem actualWeight_card
    (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel) :
    let _ := M.actualWeightFintype map_injective map_surjective
    Fintype.card (CharacterWeight.ConjugacyClass
      (p := 2) (K := K) (G := X)) = 33 := by
  let _ := M.actualWeightFintype map_injective map_surjective
  calc
    Fintype.card (CharacterWeight.ConjugacyClass
        (p := 2) (K := K) (G := X)) =
        Fintype.card WeightOutputLabel :=
      (Fintype.card_congr (M.equiv map_injective map_surjective)).symm
    _ = 33 := WeightOutputLabel.card

end LiteralWeightOutputMap

/-! ## Separate block-fibre properties -/

variable {blockIdempotent : Q3Block -> k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut X)ᵐᵒᵖ (PrimitiveBlock k X)]

/-- Literal primitive block containing a function-valued Brauer character. -/
def brauerPrimitiveBlock (phi : IBr iota) : PrimitiveBlock k X :=
  primitiveBlockOfLabel blocks
    (irreducibleBrauerCharacterBlock iota hinj blocks phi)

/-- Exact object-level assertion that the CTblLib block label of every
Brauer position agrees with its literal primitive block. -/
def BrauerBlockFibreCompatible
    (M : LiteralBrauerOutputMap iota) : Prop :=
  ∀ label,
    irreducibleBrauerCharacterBlock iota hinj blocks (M.character label) =
      blockOfBrauerLabel label

/-- The literal Brauer block fibre. -/
abbrev ActualBrauerFibre (block : Q3Block) :=
  IBrBlock iota hinj blocks block

/-- A bijective label map and the separate block-membership property induce
an equivalence on every literal Brauer block fibre. -/
def brauerBlockFibreEquiv
    (M : LiteralBrauerOutputMap iota)
    (map_injective : Function.Injective M.character)
    (map_surjective : Function.Surjective M.character)
    (block_compatible : BrauerBlockFibreCompatible iota hinj blocks M)
    (block : Q3Block) :
    BrauerOutputFibre block ≃ ActualBrauerFibre iota hinj blocks block where
  toFun label := ⟨M.character label.1, by
    rw [block_compatible label.1, label.2]⟩
  invFun phi :=
    let label := (LiteralBrauerOutputMap.equiv iota M
      map_injective map_surjective).symm phi.1
    ⟨label, by
      have hcharacter :=
        (LiteralBrauerOutputMap.equiv iota M
          map_injective map_surjective).apply_symm_apply phi.1
      calc
        blockOfBrauerLabel label =
            irreducibleBrauerCharacterBlock iota hinj blocks
              (M.character label) := (block_compatible label).symm
        _ = irreducibleBrauerCharacterBlock iota hinj blocks phi.1 :=
          congrArg (irreducibleBrauerCharacterBlock iota hinj blocks)
            hcharacter
        _ = block := phi.2⟩
  left_inv label := by
    apply Subtype.ext
    exact (LiteralBrauerOutputMap.equiv iota M
      map_injective map_surjective).symm_apply_apply label.1
  right_inv phi := by
    apply Subtype.ext
    exact (LiteralBrauerOutputMap.equiv iota M
      map_injective map_surjective).apply_symm_apply phi.1

/-- The block label exported for every radical-output occurrence.  The
current `o7radical.out` does not contain this routing data. -/
structure WeightBlockRouting where
  blockOf : WeightOutputLabel -> Q3Block

/-- Exact assertion that the exported weight routing agrees with literal
local block formation, inflation, and block induction. -/
def WeightBlockFibreCompatible
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (routing : WeightBlockRouting) : Prop :=
  ∀ label,
    R.weightBlock (M.classOfLabel label) =
      primitiveBlockOfLabel blocks (routing.blockOf label)

/-- The output occurrences routed to one computed block label. -/
abbrev WeightOutputFibre (routing : WeightBlockRouting) (block : Q3Block) :=
  {label : WeightOutputLabel // routing.blockOf label = block}

/-- A bijective literal weight map and the separate block-routing property
induce an equivalence on every literal weight block fibre. -/
def weightBlockFibreEquiv
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (routing : WeightBlockRouting)
    (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel)
    (block_compatible :
      WeightBlockFibreCompatible blocks R M routing)
    (block : Q3Block) :
    WeightOutputFibre routing block ≃
      R.Fibre (primitiveBlockOfLabel blocks block) where
  toFun label := ⟨M.classOfLabel label.1, by
    change R.weightBlock (M.classOfLabel label.1) =
      primitiveBlockOfLabel blocks block
    rw [block_compatible label.1, label.2]⟩
  invFun weight := by
    let actualWeight : CharacterWeight.ConjugacyClass
        (p := 2) (K := K) (G := X) := weight.1
    let label := (M.equiv map_injective map_surjective).symm actualWeight
    refine ⟨label, ?_⟩
    apply primitiveBlockOfLabel_injective blocks
    have hactualWeight : M.classOfLabel label = actualWeight :=
      (M.equiv map_injective map_surjective).apply_symm_apply actualWeight
    have hweightBlock : R.weightBlock actualWeight =
        primitiveBlockOfLabel blocks block := weight.2
    calc
      primitiveBlockOfLabel blocks (routing.blockOf label) =
          R.weightBlock (M.classOfLabel label) :=
        (block_compatible label).symm
      _ = R.weightBlock actualWeight :=
        congrArg R.weightBlock hactualWeight
      _ = primitiveBlockOfLabel blocks block := hweightBlock
  left_inv label := by
    apply Subtype.ext
    exact (M.equiv map_injective map_surjective).symm_apply_apply label.1
  right_inv weight := by
    apply Subtype.ext
    exact (M.equiv map_injective map_surjective).apply_symm_apply weight.1

/-- Literal block-fibre cardinalities are transported from the exact output
fibres; no cardinality of an abstract weight-label type is assumed. -/
theorem actualWeightBlockFibre_natCard
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (routing : WeightBlockRouting)
    (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel)
    (block_compatible :
      WeightBlockFibreCompatible blocks R M routing)
    (block : Q3Block) :
    Nat.card (R.Fibre (primitiveBlockOfLabel blocks block)) =
      Nat.card (WeightOutputFibre routing block) :=
  Nat.card_congr
    (weightBlockFibreEquiv blocks R M routing map_injective map_surjective
      block_compatible block).symm

/-! ## Separate action properties and their consequences -/

/-- Compatibility of the computed block involution with one actual outer
representative.  This is the precise E3/U block-action boundary. -/
def OuterBlockGeneratorCompatible (outer : (MulAut X)ᵐᵒᵖ) : Prop :=
  ∀ block,
    outer • primitiveBlockOfLabel blocks block =
      primitiveBlockOfLabel blocks (blockOuterAction block)

/-- The exact output permutation that a strengthened radical certificate
would export.  It is data, not a weight bijection. -/
structure WeightOuterActionData where
  permutation : Equiv.Perm WeightOutputLabel

/-- Compatibility of an exported output permutation with the canonical
automorphism action on literal character-weight conjugacy classes. -/
def WeightOuterActionCompatible
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (outer : (MulAut X)ᵐᵒᵖ)
    (action : WeightOuterActionData) : Prop :=
  ∀ label,
    M.classOfLabel (action.permutation label) =
      outer • M.classOfLabel label

/-- The canonical actual permutation on literal weight conjugacy classes. -/
def actualWeightPermutation (outer : (MulAut X)ᵐᵒᵖ) :
    Equiv.Perm
      (CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := X)) :=
  MulAction.toPermHom (MulAut X)ᵐᵒᵖ
    (CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := X)) outer

/-- A bijective object map and the separate action formula identify the two
fixed-point carriers. -/
def weightFixedPointEquiv
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (outer : (MulAut X)ᵐᵒᵖ)
    (action : WeightOuterActionData)
    (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel)
    (action_compatible : WeightOuterActionCompatible M outer action) :
    Function.fixedPoints action.permutation ≃
      Function.fixedPoints (actualWeightPermutation (K := K) outer) where
  toFun label := ⟨M.classOfLabel label.1, by
    change outer • M.classOfLabel label.1 = M.classOfLabel label.1
    rw [← action_compatible label.1, label.2]⟩
  invFun weight := by
    let actualWeight : CharacterWeight.ConjugacyClass
        (p := 2) (K := K) (G := X) := weight.1
    let label := (M.equiv map_injective map_surjective).symm actualWeight
    refine ⟨label, ?_⟩
    change action.permutation label = label
    apply (M.equiv map_injective map_surjective).injective
    change M.classOfLabel (action.permutation label) = M.classOfLabel label
    rw [action_compatible label]
    have hactualWeight : M.classOfLabel label = actualWeight :=
      (M.equiv map_injective map_surjective).apply_symm_apply actualWeight
    have hfixed : outer • actualWeight = actualWeight := weight.2
    calc
      outer • M.classOfLabel label = outer • actualWeight :=
        congrArg (fun weight => outer • weight) hactualWeight
      _ = actualWeight := hfixed
      _ = M.classOfLabel label := hactualWeight.symm
  left_inv label := by
    apply Subtype.ext
    exact (M.equiv map_injective map_surjective).symm_apply_apply label.1
  right_inv weight := by
    apply Subtype.ext
    exact (M.equiv map_injective map_surjective).apply_symm_apply weight.1

/-- Fixed-point counts on the literal carrier are transported from the exact
output permutation. -/
theorem actualWeight_fixedPoint_natCard
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (outer : (MulAut X)ᵐᵒᵖ)
    (action : WeightOuterActionData)
    (map_injective : Function.Injective M.classOfLabel)
    (map_surjective : Function.Surjective M.classOfLabel)
    (action_compatible : WeightOuterActionCompatible M outer action) :
    Nat.card (Function.fixedPoints (actualWeightPermutation (K := K) outer)) =
      Nat.card (Function.fixedPoints action.permutation) :=
  Nat.card_congr
    (weightFixedPointEquiv M outer action map_injective map_surjective
      action_compatible).symm

/-- Weight action and literal block formation force the output block-routing
map to intertwine the two printed block permutations. -/
theorem weightOutput_block_action_compatible
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (M : LiteralWeightOutputMap (K := K) (X := X))
    (routing : WeightBlockRouting)
    (outer : (MulAut X)ᵐᵒᵖ)
    (action : WeightOuterActionData)
    (block_compatible :
      WeightBlockFibreCompatible blocks R M routing)
    (weight_action_compatible : WeightOuterActionCompatible M outer action)
    (block_action_compatible : OuterBlockGeneratorCompatible blocks outer) :
    ∀ label,
      routing.blockOf (action.permutation label) =
        blockOuterAction (routing.blockOf label) := by
  intro label
  apply primitiveBlockOfLabel_injective blocks
  calc
    primitiveBlockOfLabel blocks
        (routing.blockOf (action.permutation label)) =
        R.weightBlock (M.classOfLabel (action.permutation label)) :=
      (block_compatible (action.permutation label)).symm
    _ = R.weightBlock (outer • M.classOfLabel label) := by
      rw [weight_action_compatible label]
    _ = outer • R.weightBlock (M.classOfLabel label) :=
      R.weightBlock_transport outer (M.classOfLabel label)
    _ = outer • primitiveBlockOfLabel blocks (routing.blockOf label) := by
      rw [block_compatible label]
    _ = primitiveBlockOfLabel blocks
        (blockOuterAction (routing.blockOf label)) :=
      block_action_compatible (routing.blockOf label)

/-! ## Literal faithful-block stabilisers -/

/-- The stabiliser of one literal primitive block. -/
def actualBlockStabilizer (block : Q3Block) :
    Subgroup ((MulAut X)ᵐᵒᵖ) :=
  MulAction.stabilizer (MulAut X)ᵐᵒᵖ
    (primitiveBlockOfLabel blocks block)

/-- The existing literal weight-fibre action, exposed through the definition
of the actual block stabiliser. -/
instance actualWeightFibreMulAction
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (block : Q3Block) :
    MulAction (actualBlockStabilizer blocks block)
      (R.Fibre (primitiveBlockOfLabel blocks block)) :=
  CharacterWeight.EquivariantBlockAssignment.fibreMulAction
    R.equivariantBlockAssignment (primitiveBlockOfLabel blocks block)

/-- Every automorphism in the nontrivial outer class acts on literal blocks
as the chosen outer representative.  This is derived from the E1 `C2`
quotient and pointwise inner fixation. -/
theorem block_action_eq_outerGenerator_of_nontrivial
    (quotient : C2OuterQuotientInput ((MulAut X)ᵐᵒᵖ))
    (inner_fixes_blocks : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ block : PrimitiveBlock k X,
        alpha • block = block)
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : quotient.outerClass outer ≠ 1)
    (alpha : (MulAut X)ᵐᵒᵖ)
    (alpha_nontrivial : quotient.outerClass alpha ≠ 1)
    (block : PrimitiveBlock k X) :
    alpha • block = outer • block := by
  have hclasses : quotient.outerClass alpha = quotient.outerClass outer :=
    finTwo_perm_eq_of_ne_one _ _ alpha_nontrivial outer_nontrivial
  let innerPart : (MulAut X)ᵐᵒᵖ := alpha * outer⁻¹
  have hinnerClass : quotient.outerClass innerPart = 1 := by
    simp only [innerPart, map_mul, map_inv, hclasses]
    exact mul_inv_cancel _
  have hinner : innerPart ∈ quotient.innerSubgroup := by
    have : innerPart ∈ quotient.outerClass.ker := hinnerClass
    rwa [quotient.outerClass_ker] at this
  have halpha : alpha = innerPart * outer := by
    simp [innerPart]
  rw [halpha, mul_smul, inner_fixes_blocks innerPart hinner]

/-- The stabiliser of every faithful literal primitive block is inner.  The
conclusion is not a field of the adapter. -/
theorem faithful_actualBlockStabilizer_le_inner
    (quotient : C2OuterQuotientInput ((MulAut X)ᵐᵒᵖ))
    (inner_fixes_blocks : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ block : PrimitiveBlock k X,
        alpha • block = block)
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : quotient.outerClass outer ≠ 1)
    (block_action_compatible : OuterBlockGeneratorCompatible blocks outer)
    (block : Q3Block)
    (hblock : block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9) :
    actualBlockStabilizer blocks block ≤ quotient.innerSubgroup := by
  intro alpha halpha
  by_contra hnotInner
  have hclass : quotient.outerClass alpha ≠ 1 := by
    intro htrivial
    have hker : alpha ∈ quotient.outerClass.ker := htrivial
    rw [quotient.outerClass_ker] at hker
    exact hnotInner hker
  have hacts := block_action_eq_outerGenerator_of_nontrivial
    quotient inner_fixes_blocks outer outer_nontrivial alpha hclass
      (primitiveBlockOfLabel blocks block)
  have houterFixed :
      primitiveBlockOfLabel blocks (blockOuterAction block) =
        primitiveBlockOfLabel blocks block := by
    rw [← block_action_compatible block, ← hacts]
    exact halpha
  exact (faithful_blocks_not_fixed_by_outer block hblock)
    (primitiveBlockOfLabel_injective blocks houterFixed)

/-! ## Derived equivariance on literal faithful block fibres -/

/-- Transport one actual Brauer block fibre by an automorphism stabilising
the corresponding literal primitive block. -/
def brauerFibreAction
    (brauerBlock_transport : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      brauerPrimitiveBlock iota hinj blocks (alpha • phi) =
        alpha • brauerPrimitiveBlock iota hinj blocks phi)
    (block : Q3Block)
    (alpha : actualBlockStabilizer blocks block)
    (phi : ActualBrauerFibre iota hinj blocks block) :
    ActualBrauerFibre iota hinj blocks block :=
  ⟨(alpha : (MulAut X)ᵐᵒᵖ) • phi.1, by
    apply primitiveBlockOfLabel_injective blocks
    calc
      primitiveBlockOfLabel blocks
          (irreducibleBrauerCharacterBlock iota hinj blocks
            ((alpha : (MulAut X)ᵐᵒᵖ) • phi.1)) =
          (alpha : (MulAut X)ᵐᵒᵖ) •
            primitiveBlockOfLabel blocks
              (irreducibleBrauerCharacterBlock iota hinj blocks phi.1) :=
        brauerBlock_transport alpha phi.1
      _ = (alpha : (MulAut X)ᵐᵒᵖ) •
          primitiveBlockOfLabel blocks block := by rw [phi.2]
      _ = primitiveBlockOfLabel blocks block := alpha.2⟩

/-- Once the faithful literal block stabiliser is inner, every equivalence
between its actual Brauer and weight fibres is automatically equivariant.
Only pointwise inner fixation of the two literal carriers is supplied. -/
theorem arbitrary_actualFibre_equiv_is_stabilizer_equivariant
    (quotient : C2OuterQuotientInput ((MulAut X)ᵐᵒᵖ))
    (inner_fixes_blocks : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ block : PrimitiveBlock k X,
        alpha • block = block)
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : quotient.outerClass outer ≠ 1)
    (block_action_compatible : OuterBlockGeneratorCompatible blocks outer)
    (brauerBlock_transport : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      brauerPrimitiveBlock iota hinj blocks (alpha • phi) =
        alpha • brauerPrimitiveBlock iota hinj blocks phi)
    (inner_fixes_brauer : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ phi : IBr iota,
        alpha • phi = phi)
    (inner_fixes_weight : ∀ alpha,
      alpha ∈ quotient.innerSubgroup ->
        ∀ weight : CharacterWeight.ConjugacyClass
          (p := 2) (K := K) (G := X), alpha • weight = weight)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (block : Q3Block)
    (hblock : block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9)
    (equivalence : ActualBrauerFibre iota hinj blocks block ≃
      R.Fibre (primitiveBlockOfLabel blocks block)) :
    ∀ alpha : actualBlockStabilizer blocks block, ∀ phi,
      equivalence
          (brauerFibreAction iota hinj blocks brauerBlock_transport
            block alpha phi) =
        alpha • equivalence phi := by
  intro alpha phi
  have hinner : (alpha : (MulAut X)ᵐᵒᵖ) ∈ quotient.innerSubgroup :=
    faithful_actualBlockStabilizer_le_inner blocks quotient
      inner_fixes_blocks outer outer_nontrivial block_action_compatible
      block hblock alpha.2
  apply Subtype.ext
  have hbrauer :
      brauerFibreAction iota hinj blocks brauerBlock_transport
          block alpha phi = phi := by
    apply Subtype.ext
    exact inner_fixes_brauer alpha hinner phi.1
  calc
    (equivalence
        (brauerFibreAction iota hinj blocks brauerBlock_transport
          block alpha phi)).1 = (equivalence phi).1 :=
      congrArg Subtype.val (congrArg equivalence hbrauer)
    _ = (alpha : (MulAut X)ᵐᵒᵖ) • (equivalence phi).1 :=
      (inner_fixes_weight alpha hinner (equivalence phi).1).symm
    _ = (alpha • equivalence phi).1 := rfl

/-- Exact output-fibre equality constructs a literal Brauer--weight fibre
equivalence; the preceding theorem then derives its stabiliser equivariance.
No equivalence or equivariance is an adapter field. -/
theorem exists_stabilizerEquivariant_actualFibreEquiv_of_output_card
    (quotient : C2OuterQuotientInput ((MulAut X)ᵐᵒᵖ))
    (inner_fixes_blocks : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ block : PrimitiveBlock k X,
        alpha • block = block)
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : quotient.outerClass outer ≠ 1)
    (block_action_compatible : OuterBlockGeneratorCompatible blocks outer)
    (brauerBlock_transport : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      brauerPrimitiveBlock iota hinj blocks (alpha • phi) =
        alpha • brauerPrimitiveBlock iota hinj blocks phi)
    (inner_fixes_brauer : ∀ alpha,
      alpha ∈ quotient.innerSubgroup -> ∀ phi : IBr iota,
        alpha • phi = phi)
    (inner_fixes_weight : ∀ alpha,
      alpha ∈ quotient.innerSubgroup ->
        ∀ weight : CharacterWeight.ConjugacyClass
          (p := 2) (K := K) (G := X), alpha • weight = weight)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (brauerMap : LiteralBrauerOutputMap iota)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible :
      BrauerBlockFibreCompatible iota hinj blocks brauerMap)
    (weightMap : LiteralWeightOutputMap (K := K) (X := X))
    (routing : WeightBlockRouting)
    (weightMap_injective : Function.Injective weightMap.classOfLabel)
    (weightMap_surjective : Function.Surjective weightMap.classOfLabel)
    (weightBlock_compatible :
      WeightBlockFibreCompatible blocks R weightMap routing)
    (block : Q3Block)
    (hblock : block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9)
    (output_card : Fintype.card (WeightOutputFibre routing block) =
      q3BrauerCount block) :
    ∃ equivalence : ActualBrauerFibre iota hinj blocks block ≃
        R.Fibre (primitiveBlockOfLabel blocks block),
      ∀ alpha : actualBlockStabilizer blocks block, ∀ phi,
        equivalence
            (brauerFibreAction iota hinj blocks brauerBlock_transport
              block alpha phi) =
          alpha • equivalence phi := by
  have hlabelCard : Fintype.card (BrauerOutputFibre block) =
      Fintype.card (WeightOutputFibre routing block) := by
    rw [brauerOutputFibre_card, output_card]
  let labelEquiv : BrauerOutputFibre block ≃ WeightOutputFibre routing block :=
    Fintype.equivOfCardEq hlabelCard
  let equivalence : ActualBrauerFibre iota hinj blocks block ≃
      R.Fibre (primitiveBlockOfLabel blocks block) :=
    (brauerBlockFibreEquiv iota hinj blocks brauerMap
      brauerMap_injective brauerMap_surjective
      brauerBlock_compatible block).symm.trans
        (labelEquiv.trans
          (weightBlockFibreEquiv blocks R weightMap routing
            weightMap_injective weightMap_surjective
            weightBlock_compatible block))
  exact ⟨equivalence,
    arbitrary_actualFibre_equiv_is_stabilizer_equivariant
      iota hinj blocks quotient inner_fixes_blocks outer outer_nontrivial
      block_action_compatible brauerBlock_transport inner_fixes_brauer
      inner_fixes_weight R block hblock equivalence⟩

end ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
