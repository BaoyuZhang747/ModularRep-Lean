import ModularRep.PaperProofs.SporadicFi24Definition35Operations
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullWitness

/-!
# Clause (3) for all pairs of one fixed correspondence

Each Brauer character is placed in its literal block, with the full opposite
automorphism stabilizer. All selected pairs use the same supplied Omega.
The operations catalogue is identified with any complete primitive block
catalogue, so the block equation uses the actual idempotents.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs

open Formalisation ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullWitness

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

abbrev BlockStabilizer (b : ActualBlock (k := k) (X := X)) :=
  MulAction.stabilizer (MulAut X)ᵐᵒᵖ b

local instance blockStabilizerFinite
    (b : ActualBlock (k := k) (X := X)) : Finite (BlockStabilizer b) :=
  Finite.of_injective
    (fun a : BlockStabilizer b ↦ (a.1.unop : X → X))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

def blockField (b : ActualBlock (k := k) (X := X)) :
    BlockStabilizer b →* MulAut X where
  toFun a := a.1.unop⁻¹
  map_one' := by simp
  map_mul' a c := by simp

omit [IsAlgClosed k] [Fintype X] in
@[simp]
theorem inverseOpHom_blockField (b : ActualBlock (k := k) (X := X))
    (a : BlockStabilizer b) : inverseOpHom (blockField b) a = a.1 := by
  apply MulOpposite.unop_injective
  simp [inverseOpHom, blockField]

omit [IsAlgClosed k] [Fintype X] in
theorem blockField_fixed (b : ActualBlock (k := k) (X := X))
    (a : BlockStabilizer b) : inverseOpHom (blockField b) a • b = b := by
  rw [inverseOpHom_blockField]
  exact a.2

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))

def operationsBlock (phi : IBr iota) : ActualBlock (k := k) (X := X) := by
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact irreducibleBrauerCharacterBlock iota hinj
    R.1.operations.ambientBlockData.blocks phi

theorem operationsBlock_eq
    {BlockIndex : Type u} [Fintype BlockIndex]
    {blockIdempotent : BlockIndex → k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent) (phi : IBr iota) :
    operationsBlock iota hinj R phi = brauerBlock iota hinj blocks phi := by
  dsimp only [operationsBlock]
  let O := R.1.operations
  let : Fintype (ActualBlock (k := k) (X := X)) := O.ambientBlockData.fintypeBlock
  let C := (simpleModuleClassEquivIBr iota hinj).symm phi
  let V := Representation.asModule (simpleClassFDRep C).ρ
  let : IsSimpleModule k[X] V :=
    simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple C)
  change O.ambientBlockData.blocks.moduleBlock (V := V) =
    actualBlockOfIndex blocks (blocks.moduleBlock (V := V))
  symm
  apply O.ambientBlockData.blocks.moduleBlock_eq_of_smul_eq_self
  intro v
  rw [R.2]
  exact blocks.moduleBlock_smul (V := V) v

variable (localReduction :
  ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
    SelectedLocalReductionSource R.1 b w)

def blockProblem (b : ActualBlock (k := k) (X := X)) : Definition35Problem :=
  literalDefinition35Problem iota hinj R b
    (blockField b) (blockField_fixed b) (localReduction b)

def blockAutomorphisms (b : ActualBlock (k := k) (X := X)) :
    Definition35AutomorphismStabilizerAdapter
      (blockProblem iota hinj R localReduction b) where
  equiv := MulEquiv.refl _
  equiv_coe a := (inverseOpHom_blockField b a).symm

def problemAt (phi : IBr iota) : Definition35Problem :=
  blockProblem iota hinj R localReduction (operationsBlock iota hinj R phi)

variable (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
variable (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
  Omega (alpha • phi) = alpha • Omega phi)
variable (hblock : ∀ phi : IBr iota,
  R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)

def matchAt (phi : IBr iota) :
    EquivariantMatch (problemAt iota hinj R localReduction phi) where
  Omega := Omega
  theta := ⟨phi, rfl⟩
  weight := ⟨Omega phi, hblock phi⟩
  equivariant := hOmega
  matched := rfl

@[simp]
theorem matchAt_Omega (phi : IBr iota) :
    (matchAt iota hinj R localReduction Omega hOmega hblock phi).Omega = Omega := rfl

@[simp]
theorem matchAt_theta (phi : IBr iota) :
    (matchAt iota hinj R localReduction Omega hOmega hblock phi).theta.1 = phi := rfl

@[simp]
theorem matchAt_weight (phi : IBr iota) :
    (matchAt iota hinj R localReduction Omega hOmega hblock phi).weight.1 = Omega phi := rfl

theorem exists_namedClause3Family
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (hcenter : Subgroup.center X = ⊥)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    Nonempty (∀ phi : IBr iota,
      NamedClause3Witness (problemAt iota hinj R localReduction phi)
        (matchAt iota hinj R localReduction Omega hOmega hblock phi) S hcenter haut) := by
  refine ⟨fun phi ↦ Classical.choice ?_⟩
  exact namedClause3Witness_of_equivariantMatch
    (problemAt iota hinj R localReduction phi)
    (matchAt iota hinj R localReduction Omega hOmega hblock phi) S hcenter haut principle

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
