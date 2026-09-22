import ModularRep.PaperProofs.TypeBSpinCoverSource
import ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
import ModularRep.IBrBlockAutomorphism
import ModularRep.PrimitiveBlockAutomorphism
import ModularRep.NavarroLocalReductionInflationBlockCompatibility

/-!
# The literal Spin block family for the full criterion

This module constructs only the input carrier of the published condition.
The block group is the actual automorphism stabilizer; its adapter is proved,
not sourced. Blocks are primitive central idempotents, and Brauer-block
transport is the existing kernel theorem. The local source retains the exact
ambient idempotent equality and the reduction of each selected defect-zero
character (routine E1, with source realization U). No matching, extension,
intermediate-block witness or full-condition predicate is supplied.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinDefinitionFamily

open ModularRep FDRepSimpleClassKZero
open TypeBCliffordCarriers
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family

variable {n ell : ℕ} {F k K : Type}
variable [Field F] [Field k] [Field K] [CharP k ell] [IsAlgClosed k]
variable [CharZero K]
variable (N : NormSource n F) [Finite (Spin n F N)]

local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

local instance spinAutFinite : Finite (MulAut (Spin n F N)) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

abbrev SpinBlock := LiteralPrimitiveBlock k (Spin n F N)

/-- The opposite-automorphism stabilizer on the specified idempotent. -/
abbrev BlockStabilizer (b : SpinBlock (k := k) N) :=
  MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ b

local instance blockStabilizerFinite (b : SpinBlock (k := k) N) :
    Finite (BlockStabilizer N b) :=
  Finite.of_injective (fun a : BlockStabilizer N b =>
    ((MulOpposite.unop a.1 : MulAut (Spin n F N)) : Spin n F N → Spin n F N))
    (fun a c h => Subtype.ext (MulOpposite.unop_injective (DFunLike.coe_injective h)))

/-- Convert the canonical opposite stabilizer to its actual automorphisms.
The inverse exactly matches the existing right-action convention. -/
def stabilizerHom (b : SpinBlock (k := k) N) :
    BlockStabilizer N b →* MulAut (Spin n F N) where
  toFun a := (MulOpposite.unop a.1)⁻¹
  map_one' := by simp
  map_mul' a c := by simp

@[simp]
theorem inverseOpHom_stabilizerHom (b : SpinBlock (k := k) N)
    (a : BlockStabilizer N b) :
    inverseOpHom (stabilizerHom N b) a = a.1 := by
  simp [inverseOpHom, stabilizerHom]

def blockAutomorphisms (b : SpinBlock (k := k) N) :
    Definition35BlockAutomorphisms (Spin n F N) (SpinBlock (k := k) N) b where
  Gamma := BlockStabilizer N b
  gamma := stabilizerHom N b
  gammaBlock_fixed a := by
    rw [inverseOpHom_stabilizerHom]
    exact a.2

variable [Fintype (SpinBlock (k := k) N)]
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : SpinBlock (k := k) N => b.1))

/-- Literal Brauer-block transport needs no new source premise. -/
theorem brauerBlock_transport (a : (MulAut (Spin n F N))ᵐᵒᵖ)
    (phi : IBr iota) :
    irreducibleBrauerCharacterBlock iota hinj blocks (a • phi) =
      a • irreducibleBrauerCharacterBlock iota hinj blocks phi := by
  simpa only [BlockIdempotentDecomposition.primitiveBlockOfIndex] using
    primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
      iota hinj blocks a phi

/-- Exact local quotient/block source data on the same primitive blocks.
The selected local character is a literal defect-zero character of N(R)/R;
its reduction is the routine defect-zero source theorem, not a matching.
The ambient catalogue cannot silently rename the primitive idempotents. -/
structure LocalSource where
  splitting : IsAlgClosed K
  blockSource : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := Spin n F N)
    (Block := SpinBlock (k := k) N)
  idempotent : ∀ b : SpinBlock (k := k) N,
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1
  localBlockCompatibility : NavarroLocalReductionInflationBlockCompatibility.Source
    blockSource.operations
  reduction : ∀ (b : SpinBlock (k := k) N)
      (w : LiteralWeightFibre blockSource b),
    SelectedLocalReductionSource blockSource b w

/-- A literal input family. Its character/weight matching is deliberately
absent: the complete published criterion must produce that later. -/
def spinFamily (hEll : Nat.Prime ell) (localSource : LocalSource (ell := ell) (k := k) (K := K) N) :
    Definition35Family ell where
  ellPrime := hEll
  k := k
  K := K
  H := Spin n F N
  Block := SpinBlock (k := k) N
  fintypeH := Fintype.ofFinite _
  blockIdempotent b := b.1
  iota := iota
  irreducibleBrauerInjective := hinj
  blocks := blocks
  blockSource := localSource.blockSource
  brauerBlock_transport := brauerBlock_transport N iota hinj blocks
  automorphisms := blockAutomorphisms N
  localReduction := localSource.reduction

/-- The source problem's automorphism group is definitionally the full
literal block stabilizer, so its formerly U adapter is the identity. -/
def spinFamily_stabilizerAdapter (hEll : Nat.Prime ell)
    (localSource : LocalSource (ell := ell) (k := k) (K := K) N) (b : SpinBlock (k := k) N) :
    Definition35AutomorphismStabilizerAdapter
      ((spinFamily N iota hinj blocks hEll localSource).problem b) where
  equiv := MulEquiv.refl _
  equiv_coe a := (inverseOpHom_stabilizerHom N b a).symm

@[simp]
theorem spinFamily_local_idempotent (hEll : Nat.Prime ell)
    (localSource : LocalSource (ell := ell) (k := k) (K := K) N) (b : SpinBlock (k := k) N) :
    (spinFamily N iota hinj blocks hEll localSource).blockSource.operations.ambientBlockData.blockIdempotent b = b.1 :=
  localSource.idempotent b

end ModularRep.PaperProofs.TypeBSpinDefinitionFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
