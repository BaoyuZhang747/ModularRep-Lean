import ManuscriptIBAW.Library.FixedBasicSet
import ModularRep.IBrBlockBasicSetBridge

/-!
# The fixed basic set in Proposition 3.8

The ordinary basic set is assumed to be an integral basic set for the exact
decomposition map, and its labels have the ordinary automorphism action.
Stable reduction proves naturality of that map. If the automorphisms fix
these ordinary characters pointwise, they also fix every irreducible Brauer
character in the block. Equality of the two ranks gives an equivariant
bijection without Conlon's theorem.

The fraction field of the modular system is not required to be algebraically
closed. Realising the unipotent ordinary characters over that field is a
separate source assumption in the application.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ManuscriptIBAW.TypeC

open ModularRep
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.DecompositionBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock

universe u w

variable {ell : ℕ} {K O k G Basic A : Type u} {I : Type w}
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [CharZero K] [Group G] [Finite G] [Fintype I]
    [CharP k ell] [IsAlgClosed k] [Group A] [MulAction A Basic]
    {iota : PrimeRegularRootEmbedding ell k K G}
    {injective : IrreducibleBrauerCharacterInjectivity iota}
    {idempotent : I → k[G]} {blocks : BlockIdempotentDecomposition idempotent}
    {block : I}

/-- Field invariance of an ordinary integral basic set implies field
invariance of the irreducible Brauer characters of the same block. -/
theorem brauer_characters_fixed_of_basic_set_fixed
    (system : ModularSystem ell K O k)
    (reduction : StableReductionBrauerCharacterCompatibility system iota)
    (basic : RestrictedIntegralBasicSetOnIBrBlock iota injective blocks block Basic
      (decompositionMapOfStableReduction system iota reduction))
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (stable : IsAutomorphismStableIBrBlock automorphism iota injective blocks block)
    (ordinary : OrdinaryTwistCompatibleLabels basic automorphism)
    (fixed : ∀ (a : A) (x : Basic), a • x = x) :
    letI := automorphismIBrBlockMulAction automorphism stable
    ∀ (a : A) (phi : IBrBlock iota injective blocks block), a • phi = phi := by
  let _ := automorphismIBrBlockMulAction automorphism stable
  have natural := matrixEquivariant_of_stableReduction system iota reduction
    basic.toRestrictedIntegralBasicSet automorphism
    (twistCompatibleLabelsOfAutomorphismStableBlock basic automorphism stable ordinary)
  exact modular_basis_fixed_of_basic_set_fixed basic.linearEquiv natural fixed

/-- The direct basic set step of Proposition 3.8, with the canonical action on
the actual set of irreducible Brauer characters belonging to the block. -/
theorem basic_set_brauer_equivariant_bijection
    (system : ModularSystem ell K O k)
    (reduction : StableReductionBrauerCharacterCompatibility system iota)
    (basic : RestrictedIntegralBasicSetOnIBrBlock iota injective blocks block Basic
      (decompositionMapOfStableReduction system iota reduction))
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (stable : IsAutomorphismStableIBrBlock automorphism iota injective blocks block)
    (ordinary : OrdinaryTwistCompatibleLabels basic automorphism)
    (fixed : ∀ (a : A) (x : Basic), a • x = x) :
    letI := automorphismIBrBlockMulAction automorphism stable
    ∃ e : Basic ≃ IBrBlock iota injective blocks block,
      ∀ (a : A) (x : Basic), e (a • x) = a • e x := by
  let _ := automorphismIBrBlockMulAction automorphism stable
  have natural := matrixEquivariant_of_stableReduction system iota reduction
    basic.toRestrictedIntegralBasicSet automorphism
    (twistCompatibleLabelsOfAutomorphismStableBlock basic automorphism stable ordinary)
  exact equivariant_bijection_of_basic_set_fixed basic.linearEquiv natural fixed

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
