import ModularRep.LiteralOrdinaryPBlockSource
import ModularRep.OrdinaryBrauerReductionSurjectiveDescent

/-!
# Literal ordinary block of an actual irreducible Brauer reduction

The uniform hReductionSupport hypothesis is the standard decomposition-number
fact that, when chi^0 = phi is irreducible, d_(chi,phi)=1 and hence is
nonzero. Its decompositionSupport must be the genuine relation in the same
fixed modular system as LiteralOrdinaryPBlockSource; neither a
selected-character support premise nor a block equality is assumed.

The abstract support API contains neither a decomposition expansion nor integer
coefficients, so this coefficient-one fact is an E1 source input rather than a
deduction from its three fields.
-/

noncomputable section

namespace ModularRep.LiteralOrdinaryPBlockSource

open ModularRep.OrdinaryBrauerReductionSurjectiveDescent

universe u

variable {p : Nat} {k K G BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Fintype BlockIndex]
variable {iota : PrimeRegularRootEmbedding p k K G}
variable {hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota}
variable {blockIdempotent : BlockIndex → MonoidAlgebra k G}
variable {blocks : BlockIdempotentDecomposition blockIdempotent}
variable {decompositionSupport :
  OrdinaryIrreducibleCharacter.Irr K G → IBr iota → Prop}

/-- A uniform genuine decomposition-support law and the existing ordinary
selector source identify the two actual primitive block idempotents. -/
theorem ordinaryBlock_eq_literalBrauerBlock_of_reduction
    (S : LiteralOrdinaryPBlockSource iota hinj blocks decompositionSupport)
    (hReductionSupport : ∀ (chi : OrdinaryIrreducibleCharacter.Irr K G)
        (phi : IBr iota),
      IsOrdinaryBrauerReduction iota chi phi → decompositionSupport chi phi)
    (chi : OrdinaryIrreducibleCharacter.Irr K G)
    (phi : IBr iota)
    (hReduction : IsOrdinaryBrauerReduction iota chi phi) :
    S.ordinaryBlock chi = literalBrauerBlock iota hinj blocks phi :=
  ((S.support_nonempty_and_sound chi).2 phi
    (hReductionSupport chi phi hReduction)).symm

end ModularRep.LiteralOrdinaryPBlockSource



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
