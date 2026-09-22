import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# The inductive condition on one literal central-quotient block

The indices are the original family, its universal prime-to-ell cover, and
one specified block. The reference character fixes the actual central kernel
and quotient block through the relative data. The complete quotient
correspondence below is equivariant under the actual block stabilizer.

For every character in that complete quotient block, `matched_preimage`
identifies both the character and the raw weight class with one original
matched pair. That pair supplies its actual ambient group, extensions, and
block induction equalities for all intermediate subgroups. The finite-root
agreements retain the specified interpretation of those block equalities.

This is the single-block formulation in Brough--Spath, Definition 4.3 and
Remark 4.4, and Koshitani--Spath, Definition 3.2, on the central quotient in
the manuscript preliminaries. It contains no family of correspondences for
other blocks. This module defines the output and supplies no inhabitant.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBFixedBlockDecodedCondition

open ModularRep FDRepSimpleClassKZero
open CyclicOuterLemma37ActualBlockFibres
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open TypeBFullBlockCondition

universe u

local instance quotientFintype {ell : ℕ}
    {family : Definition35Family.{u} ell}
    {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
    (relative : RelativeBlockConditionWitness family cover block) :
    Fintype (QuotientCarrier relative) := Fintype.ofFinite _

/-- The literal inductive condition for the selected block, expressed on
its actual central character quotient and complete character and weight
fibres. The image of each character uses the same matched ambient and
extension data as its identified original preimage. -/
structure DecodedCondition {ell : ℕ}
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H) (block : family.Block) where
  relative : RelativeBlockConditionWitness family cover block
  roots : FixedQuotientRootSource relative
  [quotientBlockAction :
    MulAction (MulAut (QuotientCarrier relative))ᵐᵒᵖ relative.QuotientBlock]
  quotientBlockSource : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := family.k) (K := family.K)
    (G := QuotientCarrier relative) (Block := relative.QuotientBlock)
  quotientBlockIdempotent : ∀ b : relative.QuotientBlock,
    quotientBlockSource.operations.ambientBlockData.blockIdempotent b =
      relative.quotientBlockIdempotent b
  quotientBlockCompatibility :
    TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
      (fixedQuotientRoot relative) quotientBlockSource.operations
  quotientRoots_agree : ∀ zeta : rootsOfUnity
      (primeRegularExponent ell (QuotientCarrier relative)) family.k,
    (fixedQuotientRoot relative).lift (((zeta : family.kˣ) : family.k)) =
      family.iota.lift (((zeta : family.kˣ) : family.k))
  quotientWeight_roots : ∀ psi : Definition35Brauer (family.problem block),
    TypeBFixedRootDefinitionFamily.QuotientRootAgreement
      (fixedQuotientRoot relative)
      (quotientRadical (family.problem block) relative.reference
        (relative.omega psi)) (relative.matched psi).weight.iota
  quotientInflation_roots : ∀ psi : Definition35Brauer (family.problem block),
    TypeBFixedRootDefinitionFamily.NormalizerRootAgreement
      (fixedQuotientRoot relative)
      (quotientRadical (family.problem block) relative.reference
        (relative.omega psi)) (relative.matched psi).localInflation.iota
  quotientAmbient_roots : ∀ psi : Definition35Brauer (family.problem block),
    RootLiftAgreement (relative.matched psi).quotient.iota
      (relative.matched psi).extensions.ambientRoot
  localAmbient_roots : ∀ psi : Definition35Brauer (family.problem block),
    RootLiftAgreement (relative.matched psi).extensions.localAmbientRoot
      (relative.matched psi).extensions.ambientRoot
  intermediate_roots : ∀ (psi : Definition35Brauer (family.problem block))
      (J : Subgroup (relative.matched psi).ambient.A)
      (hJ : (relative.matched psi).ambient.base ≤ J),
    RootLiftAgreement
        ((relative.matched psi).intermediateBlocks.equalityAt J hJ).globalRoot
        (relative.matched psi).extensions.ambientRoot ∧
      RootLiftAgreement
        ((relative.matched psi).intermediateBlocks.equalityAt J hJ).localRoot
        (relative.matched psi).extensions.ambientRoot
  quotientBrauerBlock_transport : ∀
      (alpha : (MulAut (QuotientCarrier relative))ᵐᵒᵖ)
      (phi : IBr (fixedQuotientRoot relative)),
    irreducibleBrauerCharacterBlock (fixedQuotientRoot relative)
        (fixedQuotientBrauerInjective relative) relative.quotientBlocks
        (alpha • phi) =
      alpha • irreducibleBrauerCharacterBlock (fixedQuotientRoot relative)
        (fixedQuotientBrauerInjective relative) relative.quotientBlocks phi
  omega : FixedQuotientBrauerFibre relative ≃
    WeightFibre quotientBlockSource relative.quotientBlock
  equivariant : ∀
      (alpha : (MulAut (QuotientCarrier relative))ᵐᵒᵖ),
    alpha • relative.quotientBlock = relative.quotientBlock →
    ∀ (phi chi : FixedQuotientBrauerFibre relative),
      chi.1 = alpha • phi.1 →
      (omega chi).1 = alpha • (omega phi).1
  centralFaithful : ∀ phi : FixedQuotientBrauerFibre relative,
    Subgroup.center (QuotientCarrier relative) ⊓
        (chosenIBrRepresentation (fixedQuotientRoot relative) phi.1).ρ.ker = ⊥
  /-- Both equalities refer to one preimage. Its computed raw weight has
  precisely the class selected by the complete quotient correspondence. -/
  matched_preimage : ∀ phi : FixedQuotientBrauerFibre relative,
    ∃ psi : Definition35Brauer (family.problem block),
      fixedDescendedBrauer relative roots psi = phi.1 ∧
      quotientWeightClass relative psi = (omega phi).1

attribute [instance] DecodedCondition.quotientBlockAction

end ModularRep.PaperProofs.TypeBFixedBlockDecodedCondition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
