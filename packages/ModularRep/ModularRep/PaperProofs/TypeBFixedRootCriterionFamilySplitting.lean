import ModularRep.PaperProofs.TypeBCriterionHypotheses

/-!
# The criterion's literal fixed-root family from local reductions

This constructor uses the existing full `LocalReductionData` directly.
Its family has the prescribed subgroup, primitive blocks, root embedding,
block source and selected local reductions. The stabilizers are the full
actual opposite-automorphism stabilizers of those primitive blocks.

The older `toPrimitiveLocalSource` adapter stores an additional ordinary
algebraic-closure field. No such adapter or field is needed for this K
construction. The existing guarded specified block and root-agreement
obligations remain in the input record and are exposed below. This file
introduces no source record, matching, criterion certificate or full
block-condition witness.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBFixedRootCriterionFamilySplitting

open ModularRep FDRepSimpleClassKZero CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open TypeBCriterionHypotheses TypeBFixedRootDefinitionFamily

variable {ell : ℕ} {k K M : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group M] [Finite M]
variable (G : Subgroup M) [G.Normal]

local instance ambientFintype : Fintype M := Fintype.ofFinite _
local instance subgroupFintype : Fintype G := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k M)]
variable [Fintype (LiteralPrimitiveBlock k G)]
variable (iotaG : PrimeRegularRootEmbedding ell k K G)
variable (blocks : BlockData (ell := ell) (k := k) (K := K) G)
variable (hEll : Nat.Prime ell)
variable (hinjG : IrreducibleBrauerCharacterInjectivity iotaG)
variable (data : LocalReductionData G iotaG blocks)

/-- The exact downstairs family, constructed without the older ordinary
algebraic-closure adapter. The entire local-reduction record is retained. -/
def downstairsFamily : Definition35Family ell where
  ellPrime := hEll
  k := k
  K := K
  H := G
  Block := LiteralPrimitiveBlock k G
  blockIdempotent b := b.1
  iota := iotaG
  irreducibleBrauerInjective := hinjG
  blocks := blocks.downstairs
  blockSource := blocks.weightDownstairs
  brauerBlock_transport := primitiveBrauerBlock_transport iotaG hinjG blocks.downstairs
  automorphisms := primitiveBlockAutomorphisms
  localReduction := data.reduction

@[simp]
theorem downstairsFamily_H :
    (downstairsFamily G iotaG blocks hEll hinjG data).H = G := rfl

@[simp]
theorem downstairsFamily_Block :
    (downstairsFamily G iotaG blocks hEll hinjG data).Block =
      LiteralPrimitiveBlock k G := rfl

@[simp]
theorem downstairsFamily_iota :
    (downstairsFamily G iotaG blocks hEll hinjG data).iota = iotaG := rfl

@[simp]
theorem downstairsFamily_blocks :
    (downstairsFamily G iotaG blocks hEll hinjG data).blocks = blocks.downstairs := rfl

@[simp]
theorem downstairsFamily_blockSource :
    (downstairsFamily G iotaG blocks hEll hinjG data).blockSource =
      blocks.weightDownstairs := rfl

@[simp]
theorem downstairsFamily_localReduction (b : LiteralPrimitiveBlock k G)
    (w : LiteralWeightFibre blocks.weightDownstairs b) :
    (downstairsFamily G iotaG blocks hEll hinjG data).localReduction b w =
      data.reduction b w := rfl

/-- The family uses the same local specified block guard stored in the
criterion's full local-reduction domain. -/
theorem downstairsFamily_blockCompatibility :
    GuardedBlockCompatibility
      (downstairsFamily G iotaG blocks hEll hinjG data).iota
      (downstairsFamily G iotaG blocks hEll hinjG data).blockSource.operations :=
  data.blockCompatibility

/-- The selected quotient reduction agrees with the same global root on
the exact roots of its actual normalizer quotient. -/
theorem downstairsFamily_rootAgreement (b : LiteralPrimitiveBlock k G)
    (w : LiteralWeightFibre blocks.weightDownstairs b) :
    QuotientRootAgreement (G := G)
      (downstairsFamily G iotaG blocks hEll hinjG data).iota
      (SelectedRadical (H := G) blocks.weightDownstairs b w)
      ((downstairsFamily G iotaG blocks hEll hinjG data).localReduction b w).iota :=
  data.rootAgreement b w

@[simp]
theorem downstairsFamily_problem_block (b : LiteralPrimitiveBlock k G) :
    ((downstairsFamily G iotaG blocks hEll hinjG data).problem b).block = b := rfl

@[simp]
theorem downstairsFamily_problem_gamma (b : LiteralPrimitiveBlock k G) :
    ((downstairsFamily G iotaG blocks hEll hinjG data).problem b).gamma =
      primitiveStabilizerHom b := rfl

/-- The acting group is already the full actual stabilizer, so the
stabilizer adapter is the identity on that group. -/
def downstairsFamily_stabilizerAdapter (b : LiteralPrimitiveBlock k G) :
    Definition35AutomorphismStabilizerAdapter
      ((downstairsFamily G iotaG blocks hEll hinjG data).problem b) where
  equiv := MulEquiv.refl _
  equiv_coe a := (inverseOpHom_primitiveStabilizerHom b a).symm

@[simp]
theorem downstairsFamily_inverseOpHom (b : LiteralPrimitiveBlock k G)
    (a : PrimitiveBlockStabilizer b) :
    inverseOpHom
      ((downstairsFamily G iotaG blocks hEll hinjG data).problem b).gamma a = a.1 :=
  inverseOpHom_primitiveStabilizerHom b a

end ModularRep.PaperProofs.TypeBFixedRootCriterionFamilySplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
