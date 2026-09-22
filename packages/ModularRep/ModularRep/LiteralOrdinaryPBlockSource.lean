import ModularRep.IBrBlock
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.PrimitiveBlockAutomorphism

/-!
# Literal ordinary p-block selector source

This source-facing module records the smallest ordinary-to-modular block
boundary required by literal ordinary-character fibres.  Its selector lands
in the actual subtype of primitive central idempotents of `k[G]`.  The third
field binds that selector to a source-specified genuine nonzero
decomposition-support relation; it is not a K0 coordinate construction.

All three fields are E1/U at a concrete coefficient/carrier binding.  The
file contains no Spath or Navarro (9.9)(c) transport, quotient-block map,
weight, BAW, or iBAW conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep

universe u

variable {p : Nat} {k K G BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Fintype BlockIndex]

/-- The literal modular primitive block containing a function-valued
irreducible Brauer character. -/
noncomputable def literalBrauerBlock
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : BlockIndex -> k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (phi : IBr iota) : LiteralPrimitiveBlock k G :=
  blocks.primitiveBlockOfIndex
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock
      iota hinj blocks phi)

/-- Type-valued E1/U source packet for the ordinary p-block selector in one
fixed splitting modular system.  It is a structure in `Type`, not `Prop`,
because `ordinaryBlock` is source data used by downstream constructions.

`decompositionSupport chi phi` is required at each concrete instance to mean
the genuine assertion that the decomposition number `d_(chi,phi)` is
nonzero.  The bundled third field states both row nonemptiness and universal
soundness of every supported Brauer constituent. -/
structure LiteralOrdinaryPBlockSource
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : BlockIndex -> k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (decompositionSupport :
      OrdinaryIrreducibleCharacter.Irr K G -> IBr iota -> Prop) where
  ordinaryBlock :
    OrdinaryIrreducibleCharacter.Irr K G -> LiteralPrimitiveBlock k G
  ordinaryBlock_surjective : Function.Surjective ordinaryBlock
  support_nonempty_and_sound :
    ∀ chi,
      (∃ phi, decompositionSupport chi phi) ∧
        ∀ phi, decompositionSupport chi phi →
          literalBrauerBlock iota hinj blocks phi = ordinaryBlock chi

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
