import ModularRep.BlockFibreRestriction
import ModularRep.ConlonStabilizerBridge
import ModularRep.IBrBlock

/-!
# Relative endpoint for manuscript Proposition 3.11

This file formalises the deduction specific to Proposition 3.11.  Its modular
carrier is the function-valued set `IBr`, and the selected block on that side
is the literal fibre determined by a block-idempotent decomposition.  Starting
from a global integral basic set, Lean restricts its exact decomposition map to
the selected block, proves equivariance there from source-shaped actions on
exact `K₀`, derives the `2`-hypoelementary condition from the small normal
subgroup in the exact stabiliser calculation, and applies the cited Conlon and
Burnside inputs.

The action on exact `K₀` is deliberately not specialised to automorphism
twisting.  In the manuscript it must be instantiated by the combined action
of tensoring with linear characters and applying field automorphisms.  Thus
the tensor action is not silently replaced by a pure automorphism action.
-/

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddConformalProposition311Relative

open FDRepSimpleClassKZero
open ExactGrothendieckGroup
open DecompositionBasicSetBridge
open BlockFibreRestriction
open IntegralBasicSetBridge
open ManuscriptVerification.ConlonStabilizerBridge

noncomputable section

universe u

variable {p : ℕ} {K k G Basic : Type u}
variable [Field K] [Field k] [CharZero K]
variable [Group G] [Finite G] [CharP k p] [IsAlgClosed k]

/-- A global integral basic set whose modular indexing set is the actual
function-valued set of irreducible Brauer characters.

The modular label is fixed to the inverse of the kernel-checked equivalence
between simple modular representations and `IBr`; it is not an arbitrary
injective labelling supplied by the application.  No action, equivariance, or
blockwise bijection is a field of this structure. -/
structure RestrictedIntegralBasicSetOnIBr
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (Basic : Type u)
    (decomposition : FDRepKZero K G →+ FDRepKZero k G) where
  ordinaryLabel : Basic → SimpleModuleClass K[G]
  ordinaryLabel_injective : Function.Injective ordinaryLabel
  linearEquiv : MonoidAlgebra ℤ Basic ≃ₗ[ℤ] MonoidAlgebra ℤ (IBr iota)
  restricts_decomposition : ∀ v : MonoidAlgebra ℤ Basic,
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (linearEquiv v) =
      decomposition (labelledSimpleClassKZero ordinaryLabel v)

namespace RestrictedIntegralBasicSetOnIBr

/-- Forget the fixed interpretation of the modular labels and expose the
general exact-`K₀` basic-set interface used by the restriction theorem. -/
def toRestrictedIntegralBasicSet
    {iota : PrimeRegularRootEmbedding p k K G}
    {hinj : IrreducibleBrauerCharacterInjectivity iota}
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    (D : RestrictedIntegralBasicSetOnIBr iota hinj Basic decomposition) :
    RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := Basic) (Brauer := IBr iota)
      decomposition where
  ordinaryLabel := D.ordinaryLabel
  ordinaryLabel_injective := D.ordinaryLabel_injective
  modularLabel := (simpleModuleClassEquivIBr iota hinj).symm
  modularLabel_injective := (simpleModuleClassEquivIBr iota hinj).symm.injective
  linearEquiv := D.linearEquiv
  restricts_decomposition := D.restricts_decomposition

@[simp]
theorem toRestrictedIntegralBasicSet_linearEquiv
    {iota : PrimeRegularRootEmbedding p k K G}
    {hinj : IrreducibleBrauerCharacterInjectivity iota}
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    (D : RestrictedIntegralBasicSetOnIBr iota hinj Basic decomposition) :
    D.toRestrictedIntegralBasicSet.linearEquiv = D.linearEquiv := rfl

end RestrictedIntegralBasicSetOnIBr

variable {J BlockIndex CyclicTarget : Type u}
variable [Group J] [Finite J]
variable [Group CyclicTarget] [IsCyclic CyclicTarget]
variable [Finite Basic]
variable [MulAction J Basic]

/-- Restrict an ambient action to one stable block fibre.  Only stability of
the selected block is required; the acting group may permute the other
blocks. -/
@[instance_reducible]
def stableBlockFibreMulAction {X : Type u} [MulAction J X]
    (blockOf : X → BlockIndex) (block : BlockIndex)
    (hstable : ∀ (j : J) (x : X), blockOf x = block →
      blockOf (j • x) = block) :
    MulAction J (BlockFibre blockOf block) where
  smul j x := ⟨j • x.1, hstable j x.1 x.2⟩
  one_smul x := by
    apply Subtype.ext
    exact one_smul J x.1
  mul_smul j₁ j₂ x := by
    apply Subtype.ext
    exact mul_smul j₁ j₂ x.1

/-- The manuscript-specific deduction in Proposition 3.11.

The theorem takes the global integral basic set and its block diagonal
support.  It constructs the restricted linear equivalence and derives its
equivariance from the exact `K₀` actions and reduction naturality.  The normal
subgroup, its order bound, and the quotient embedding are the conclusions of
the preceding exact stabiliser calculation.  No blockwise linear equivalence,
permutation-lattice equivalence, or set bijection is an input. -/
theorem proposition_3_11_relative
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    [MulAction J (IBr iota)]
    [Fintype BlockIndex]
    {blockIdempotent : BlockIndex → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : BlockIndex)
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    (basicSet : RestrictedIntegralBasicSetOnIBr
      iota hinj Basic decomposition)
    (ordinaryBlock : Basic → BlockIndex)
    (hblockDiagonal : BlockDiagonalLinearEquiv ordinaryBlock
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      basicSet.linearEquiv)
    (tensorFieldActions : LabelledKZeroActionData (A := J)
      basicSet.toRestrictedIntegralBasicSet)
    (reductionNatural : DecompositionNatural (A := J) decomposition
      tensorFieldActions.ordinaryAction tensorFieldActions.modularAction)
    (hOrdinaryBlockStable : ∀ (j : J) (x : Basic),
      ordinaryBlock x = block → ordinaryBlock (j • x) = block)
    (hBrauerBlockStable : ∀ (j : J) (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks phi = block →
        irreducibleBrauerCharacterBlock iota hinj blocks (j • phi) = block)
    (smallNormal : Subgroup J) [smallNormal.Normal]
    (hsmall : Nat.card smallNormal ≤ 2)
    (quotientEmbedding : J ⧸ smallNormal →* CyclicTarget)
    (quotientEmbedding_injective : Function.Injective quotientEmbedding)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := 2) (A := J))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := J)) :
    let _ : MulAction J (BlockFibre ordinaryBlock block) :=
      stableBlockFibreMulAction ordinaryBlock block hOrdinaryBlockStable
    let _ : MulAction J
        (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks)
          block) :=
      stableBlockFibreMulAction
        (irreducibleBrauerCharacterBlock iota hinj blocks) block
        hBrauerBlockStable
    ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks)
        block ≃ BlockFibre ordinaryBlock block,
      ∀ (j : J)
        (phi : BlockFibre
          (irreducibleBrauerCharacterBlock iota hinj blocks) block),
        e (j • phi) = j • e phi := by
  dsimp only
  letI : MulAction J (BlockFibre ordinaryBlock block) :=
    stableBlockFibreMulAction ordinaryBlock block hOrdinaryBlockStable
  letI : MulAction J
      (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks)
        block) :=
    stableBlockFibreMulAction
      (irreducibleBrauerCharacterBlock iota hinj blocks) block
      hBrauerBlockStable
  have hOrdinaryAction : BlockFibreActionCompatible
      (A := J) ordinaryBlock block := by
    intro j x
    rfl
  have hBrauerAction : BlockFibreActionCompatible
      (A := J) (irreducibleBrauerCharacterBlock iota hinj blocks) block := by
    intro j phi
    rfl
  let restricted := restrictRestrictedIntegralBasicSet
    basicSet.toRestrictedIntegralBasicSet ordinaryBlock
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      hblockDiagonal block
  have hmatrix : MatrixEquivariant (A := J)
      restricted.linearEquiv.toLinearMap :=
    matrixEquivariant_restrictBlock_of_kZero_naturality
      basicSet.toRestrictedIntegralBasicSet hblockDiagonal
      tensorFieldActions reductionNatural hOrdinaryAction hBrauerAction
  obtain ⟨e, he⟩ :=
    equivariantSetEquiv_of_small_normal_quotient_embedding
      smallNormal hsmall quotientEmbedding quotientEmbedding_injective
      restricted.linearEquiv hmatrix conlon burnside
  exact ⟨e.symm, isEquivariantSetEquiv_symm e he⟩

end

end ModularRep.PaperProofs.OddConformalProposition311Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
