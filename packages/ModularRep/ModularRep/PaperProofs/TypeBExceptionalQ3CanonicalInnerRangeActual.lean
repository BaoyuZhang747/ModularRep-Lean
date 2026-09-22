import ModularRep.PaperProofs.TypeBExceptionalQ3CanonicalWeightRouting

/-!
# Canonical inner-range adapter for Type-B q=3 routing

This downstream adapter consumes the public canonical-routing and actual-fibre
interface of TypeBExceptionalQ3CanonicalWeightRouting.

Its E1/E3/U boundary has exactly five fields: an opposite-automorphism
outer-class homomorphism, a selected nontrivial outer element, its exact kernel
as the literal range of RepresentationWeight.innerInverseOpHom, and the
computed action of that element on the literal set of blocks. Two-point
surjectivity and the three inner-fixation statements are derived below. It
neither equates the automorphism group with the inner range nor accepts a
Brauer--weight equivalence or final inductive-condition conclusion.

The canonical block action is essential: the imported routing module obtains it
from LiteralPrimitiveBlock.rightMulAction, rather than from an arbitrary
block-action parameter.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBExceptionalQ3CanonicalInnerRangeActual

open Formalisation.ComputationArithmetic
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Actual
open ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharZero K] [Group X] [Fintype X]
variable [CharP k 2] [IsAlgClosed k]
variable {blockIdempotent : Q3Block -> k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

/-- The remaining E1/E3/U outer-action boundary for the canonical inner-range
route.  It contains no carrier-fixation field and no correspondence data.

`outerClass_ker` identifies the kernel with the literal range of
`x ↦ op (MulAut.conj x⁻¹)`, the orientation used by the canonical right actions.
`computed_outer_block_action` is the independently supplied action of the
chosen nontrivial outer element on the literal set of blocks. -/
structure CanonicalInnerRangeOuterInput where
  outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2)
  outer : (MulAut X)ᵐᵒᵖ
  outer_nontrivial : outerClass outer ≠ 1
  outerClass_ker : outerClass.ker =
    (RepresentationWeight.innerInverseOpHom (G := X)).range
  computed_outer_block_action : OuterBlockGeneratorCompatible blocks outer

namespace CanonicalInnerRangeOuterInput

/-- Package the exact literal inner range into the existing two-point quotient
interface.  Surjectivity is a finite K deduction from the selected nontrivial
outer element, rather than an additional source field. -/
def toC2OuterQuotientInput
    (S : CanonicalInnerRangeOuterInput blocks) :
    C2OuterQuotientInput ((MulAut X)ᵐᵒᵖ) where
  innerSubgroup :=
    (RepresentationWeight.innerInverseOpHom (G := X)).range
  outerClass := S.outerClass
  outerClass_surjective := by
    intro sigma
    by_cases hsigma : sigma = 1
    · refine ⟨1, ?_⟩
      simpa [hsigma]
    · refine ⟨S.outer, ?_⟩
      exact finTwo_perm_eq_of_ne_one
        (S.outerClass S.outer) sigma S.outer_nontrivial hsigma
  outerClass_ker := S.outerClass_ker

end CanonicalInnerRangeOuterInput

/-- Canonical inner automorphisms fix literal primitive blocks.  This is a K
deduction from `LiteralPrimitiveBlock.inner_smul`, not a source field. -/
theorem innerInverseOpRange_fixes_blocks
    (alpha : (MulAut X)ᵐᵒᵖ)
    (halpha : alpha ∈
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (block : PrimitiveBlock k X) :
    alpha • block = block := by
  rcases halpha with ⟨x, rfl⟩
  change MulOpposite.op (MulAut.conj x⁻¹) • block = block
  exact LiteralPrimitiveBlock.inner_smul x block

/-- Canonical inner automorphisms fix function-valued irreducible Brauer
characters.  This is the existing inner-twist theorem, specialized to the
same opposite-group orientation as `innerInverseOpHom`. -/
theorem innerInverseOpRange_fixes_brauer
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (alpha : (MulAut X)ᵐᵒᵖ)
    (halpha : alpha ∈
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (phi : IBr iota) :
    alpha • phi = phi := by
  rcases halpha with ⟨x, rfl⟩
  change IrreducibleBrauerCharacter.twist iota phi
    (MulAut.conj x⁻¹) = phi
  exact IrreducibleBrauerCharacter.twist_eq_self_of_underlying
    iota phi (MulAut.conj x⁻¹)
      (PrimeRegularClassFunction.twist_conj phi.1 x⁻¹)

/-- Canonical inner automorphisms fix ambient conjugacy classes of character
weights.  The proof is the defining orbit-quotient identification and adds no
source fact about weights. -/
theorem innerInverseOpRange_fixes_weight
    (alpha : (MulAut X)ᵐᵒᵖ)
    (halpha : alpha ∈
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (weight : CharacterWeight.ConjugacyClass
      (p := 2) (K := K) (G := X)) :
    alpha • weight = weight := by
  rcases halpha with ⟨x, rfl⟩
  change CharacterWeight.rightTwistConjugacyClass
    (p := 2) (K := K) (G := X) (MulAut.conj x⁻¹) weight = weight
  refine Quotient.inductionOn weight ?_
  intro rawWeight
  apply Quotient.sound
  exact ⟨x, rfl⟩

/-- The direct canonical-routing consumer with its three operational
inner-fixation inputs eliminated. The outer homomorphism, kernel,
nontriviality, and computed outer block action remain explicit fields of S;
all literal maps, sector compatibility, and B8/B9 fibre-cardinality inputs
remain those of the upstream canonical-routing theorem. -/
theorem canonical_faithful_actualFibreEquivs_upToFaithfulSwap_of_innerRange
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : ModularRep.FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (S : CanonicalInnerRangeOuterInput blocks)
    (R : CharacterWeight.LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := X)
      (Block := PrimitiveBlock k X))
    (brauerMap : LiteralBrauerOutputMap iota)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible :
      BrauerBlockFibreCompatible iota hinj blocks brauerMap)
    (weightMap : LiteralWeightOutputMap (K := K) (X := X))
    (weightMap_injective : Function.Injective weightMap.classOfLabel)
    (weightMap_surjective : Function.Surjective weightMap.classOfLabel)
    (sector_compatible :
      canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap
        blocks R weightMap)
    (B8_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B8)) = 2)
    (B9_weight_fibre_card :
      Nat.card (R.Fibre (primitiveBlockOfLabel blocks .B9)) = 2) :
    (∃ equivalence : ActualBrauerFibre iota hinj blocks .B6 ≃
        R.Fibre (primitiveBlockOfLabel blocks .B6),
      ∀ alpha : actualBlockStabilizer blocks .B6, ∀ phi,
        equivalence
            (brauerFibreAction iota hinj blocks
              (canonical_brauerBlock_transport blocks iota hinj)
              .B6 alpha phi) =
          alpha • equivalence phi) ∧
      (∃ equivalence : ActualBrauerFibre iota hinj blocks .B7 ≃
        R.Fibre (primitiveBlockOfLabel blocks .B7),
      ∀ alpha : actualBlockStabilizer blocks .B7, ∀ phi,
        equivalence
            (brauerFibreAction iota hinj blocks
              (canonical_brauerBlock_transport blocks iota hinj)
              .B7 alpha phi) =
          alpha • equivalence phi) := by
  exact canonical_faithful_actualFibreEquivs_upToFaithfulSwap
    blocks iota hinj
    (CanonicalInnerRangeOuterInput.toC2OuterQuotientInput blocks S)
    (by
      intro alpha halpha block
      change alpha ∈
        (RepresentationWeight.innerInverseOpHom (G := X)).range at halpha
      exact innerInverseOpRange_fixes_blocks alpha halpha block)
    S.outer S.outer_nontrivial S.computed_outer_block_action
    (by
      intro alpha halpha phi
      change alpha ∈
        (RepresentationWeight.innerInverseOpHom (G := X)).range at halpha
      exact innerInverseOpRange_fixes_brauer iota alpha halpha phi)
    (by
      intro alpha halpha weight
      change alpha ∈
        (RepresentationWeight.innerInverseOpHom (G := X)).range at halpha
      exact innerInverseOpRange_fixes_weight alpha halpha weight)
    R brauerMap brauerMap_injective brauerMap_surjective
    brauerBlock_compatible weightMap weightMap_injective weightMap_surjective
    sector_compatible B8_weight_fibre_card B9_weight_fibre_card

end ModularRep.PaperProofs.TypeBExceptionalQ3CanonicalInnerRangeActual



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
