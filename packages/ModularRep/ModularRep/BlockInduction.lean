import ModularRep.BlockCentralCharacters

/-!
# Block induction through central functions

For a subgroup `H ≤ G`, the central function induced from a block central
character of `H` is the linear map constructed by coefficient restriction in
`GroupAlgebraCentralFunctions`.  Following Späth's Definition 2.1, block
induction is defined precisely when this central function is multiplicative.
It already preserves one, so in that case it bundles to an algebra
homomorphism from `Z(k[G])` to `k`.

Once catalogues of the block central characters of `H` and `G` are supplied,
exhaustivity gives an ambient block and the delta law makes it unique.  The
induced block below is selected from this kernel proved existence and
uniqueness theorem.  It is never supplied as an input.

Navarro's Theorem (4.14) proves definedness for every local block under
`P C_G(P) ≤ H ≤ N_G(P)` and compares the induced central character with the
interval central Brauer map.  Its containment and idempotent-sum clauses are
not a normaliser correspondence; the exact-defect bijection belongs to
Theorem (4.17).  The first source equality is isolated in the separate
`Navarro414IntervalCentralCharacterSource` adapter rather than assumed here.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

/-- The induced central function preserves one before any multiplicativity
assumption is imposed. -/
@[simp]
theorem inducedCentralFunction_one {k G : Type*} [Field k] [Group G]
    (H : Subgroup G) (lambda : GroupAlgebraCenter k H →ₐ[k] k) :
    inducedCentralFunction H lambda (1 : GroupAlgebraCenter k G) = 1 := by
  rw [inducedCentralFunction_apply, centerCoeffRestrict_one]
  exact map_one lambda

/-- Multiplicativity of the subgroup induced central function. -/
def InducedCentralFunctionMultiplicative
    {k G : Type*} [Field k] [Group G]
    (H : Subgroup G) (lambda : GroupAlgebraCenter k H →ₐ[k] k) : Prop :=
  ∀ x y : GroupAlgebraCenter k G,
    inducedCentralFunction H lambda (x * y) =
      inducedCentralFunction H lambda x * inducedCentralFunction H lambda y

/-- Block induction from `H` to `G` is defined when the induced central
function is multiplicative.  Preservation of one is automatic by
`inducedCentralFunction_one`. -/
abbrev IsBlockInductionDefined
    {k G : Type*} [Field k] [Group G]
    (H : Subgroup G) (lambda : GroupAlgebraCenter k H →ₐ[k] k) : Prop :=
  InducedCentralFunctionMultiplicative H lambda

/-- Bundle a defined induced central function as an algebra homomorphism. -/
def inducedCentralCharacter
    {k G : Type*} [Field k] [Group G]
    (H : Subgroup G) (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (hdefined : IsBlockInductionDefined H lambda) :
    GroupAlgebraCenter k G →ₐ[k] k :=
  AlgHom.ofLinearMap (inducedCentralFunction H lambda)
    (inducedCentralFunction_one H lambda) hdefined

/-- The bundled central character evaluates as the original induced linear
function. -/
@[simp]
theorem inducedCentralCharacter_apply
    {k G : Type*} [Field k] [Group G]
    (H : Subgroup G) (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (hdefined : IsBlockInductionDefined H lambda)
    (z : GroupAlgebraCenter k G) :
    inducedCentralCharacter H lambda hdefined z =
      inducedCentralFunction H lambda z :=
  rfl

/-- The underlying linear map of the bundled central character is exactly
the induced central function. -/
@[simp]
theorem inducedCentralCharacter_toLinearMap
    {k G : Type*} [Field k] [Group G]
    (H : Subgroup G) (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (hdefined : IsBlockInductionDefined H lambda) :
    (inducedCentralCharacter H lambda hdefined).toLinearMap =
      inducedCentralFunction H lambda :=
  AlgHom.toLinearMap_ofLinearMap _ _ _

section Catalogues

variable {k G LocalBlock AmbientBlock : Type*}
variable [Field k] [IsAlgClosed k] [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock]
variable (H : Subgroup G)
local instance blockInductionSubgroupFintype : Fintype H :=
  Fintype.ofFinite H
variable {localBlockIdempotent : LocalBlock → k[H]}
variable {ambientBlockIdempotent : AmbientBlock → k[G]}
variable {localBlocks : BlockIdempotentDecomposition localBlockIdempotent}
variable {ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent}
variable (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
variable (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)

/-- A local block induces to an ambient block when the subgroup induced
central function is defined and its bundled algebra homomorphism is literally
the ambient block central character. -/
def BlockInducesTo (b : LocalBlock) (B : AmbientBlock) : Prop :=
  ∃ hdefined : IsBlockInductionDefined H
      (localCatalogue.centralCharacter b),
    inducedCentralCharacter H (localCatalogue.centralCharacter b) hdefined =
      ambientCatalogue.centralCharacter B

/-- If a local block induces to an ambient block, its induced central
function is defined. -/
theorem isBlockInductionDefined_of_blockInducesTo
    {b : LocalBlock} {B : AmbientBlock}
    (hinduces : BlockInducesTo H localCatalogue ambientCatalogue b B) :
    IsBlockInductionDefined H (localCatalogue.centralCharacter b) :=
  hinduces.choose

/-- Whenever the induced central function is defined, exactly one ambient
block has that central character. -/
theorem existsUnique_blockInducesTo
    (b : LocalBlock)
    (hdefined : IsBlockInductionDefined H
      (localCatalogue.centralCharacter b)) :
    ∃! B, BlockInducesTo H localCatalogue ambientCatalogue b B := by
  obtain ⟨B, hB⟩ := ambientCatalogue.exhaustive
    (inducedCentralCharacter H (localCatalogue.centralCharacter b) hdefined)
  refine ⟨B, ⟨hdefined, hB.symm⟩, ?_⟩
  intro C hC
  obtain ⟨hdefinedC, hC⟩ := hC
  apply ambientCatalogue.centralCharacter_injective
  have hproof : hdefinedC = hdefined := Subsingleton.elim _ _
  rw [hproof] at hC
  exact (hB.trans hC).symm

/-- The ambient block induced from `b`, selected from the preceding
existence and uniqueness theorem. -/
noncomputable def inducedBlock
    (b : LocalBlock)
    (hdefined : IsBlockInductionDefined H
      (localCatalogue.centralCharacter b)) : AmbientBlock :=
  Classical.choose
    (existsUnique_blockInducesTo H localCatalogue ambientCatalogue b hdefined).exists

/-- The selected block is induced from the local block. -/
theorem inducedBlock_spec
    (b : LocalBlock)
    (hdefined : IsBlockInductionDefined H
      (localCatalogue.centralCharacter b)) :
    BlockInducesTo H localCatalogue ambientCatalogue b
      (inducedBlock H localCatalogue ambientCatalogue b hdefined) :=
  Classical.choose_spec
    (existsUnique_blockInducesTo H localCatalogue ambientCatalogue b hdefined).exists

/-- Any ambient block induced from the local block is the selected one. -/
theorem eq_inducedBlock_of_blockInducesTo
    (b : LocalBlock)
    (hdefined : IsBlockInductionDefined H
      (localCatalogue.centralCharacter b))
    {B : AmbientBlock}
    (hB : BlockInducesTo H localCatalogue ambientCatalogue b B) :
    B = inducedBlock H localCatalogue ambientCatalogue b hdefined :=
  (existsUnique_blockInducesTo H localCatalogue ambientCatalogue b hdefined).unique
    hB (inducedBlock_spec H localCatalogue ambientCatalogue b hdefined)

/-- The block central character of the selected ambient block is the induced
central character. -/
theorem inducedBlock_centralCharacter
    (b : LocalBlock)
    (hdefined : IsBlockInductionDefined H
      (localCatalogue.centralCharacter b)) :
    ambientCatalogue.centralCharacter
        (inducedBlock H localCatalogue ambientCatalogue b hdefined) =
      inducedCentralCharacter H (localCatalogue.centralCharacter b) hdefined := by
  obtain ⟨hdefined', hcharacter⟩ :=
    inducedBlock_spec H localCatalogue ambientCatalogue b hdefined
  have hproof : hdefined' = hdefined := Subsingleton.elim _ _
  rw [hproof] at hcharacter
  exact hcharacter.symm

end Catalogues

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
