import ModularRep.PaperProofs.TypeBFixedBlockDecodedCondition

/-!
# The complete quotient correspondence for one specified block

The full block construction supplies two complete fibres and an invariant
matching graph. This module turns that graph into equivariance for the
actual stabilizer of the quotient block. Every quotient character is
centrally faithful, and both sides of the correspondence retain the same
original preimage and its stored extension and intermediate block data.

These are the bijection and central faithfulness clauses of Brough--Spath,
Definition 4.3. No family of other blocks or trivial-radical normalization
is required for this deduction.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFixedBlockQuotientEquivariance

open ModularRep CharacterWeight FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open TypeBFullBlockCondition

universe u

section RootTransport

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]

/-- Equality of root records transports central faithfulness of the same
irreducible character, including its chosen affording representation. -/
theorem transportIBrRoot_centralFaithful
    {iota j : PrimeRegularRootEmbedding p k K G}
    (h : iota = j) (phi : IBr iota)
    (hfaithful : Subgroup.center G ⊓
      (chosenIBrRepresentation iota phi).ρ.ker = ⊥) :
    Subgroup.center G ⊓
      (chosenIBrRepresentation j (transportIBrRoot h phi)).ρ.ker = ⊥ := by
  subst j
  exact hfaithful

end RootTransport

variable {ell : ℕ} {family : Definition35Family.{u} ell}
  {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
  (W : BlockWitness family cover block)

local instance quotientFintype : Fintype (QuotientCarrier W.relative) :=
  Fintype.ofFinite _

/-- The full actual automorphism stabilizer of this quotient block. -/
abbrev BlockStabilizer :=
  MulAction.stabilizer (MulAut (QuotientCarrier W.relative))ᵐᵒᵖ
    W.relative.quotientBlock

/-- Universal block transport restricts the actual Brauer action to the
whole quotient block under its full stabilizer. -/
theorem quotientBlock_stable :
    IsAutomorphismStableIBrBlock
      (BlockStabilizer W).subtype
      (fixedQuotientRoot W.relative)
      (fixedQuotientBrauerInjective W.relative)
      W.relative.quotientBlocks W.relative.quotientBlock := by
  intro a phi hphi
  rw [W.quotientBrauerBlock_transport, hphi]
  exact a.property

/-- Restriction of the canonical opposite-automorphism action, with no new
action chosen on individual characters. -/
@[instance_reducible]
def quotientBrauerAction :
    MulAction (BlockStabilizer W) (FixedQuotientBrauerFibre W.relative) :=
  automorphismIBrBlockMulAction (BlockStabilizer W).subtype
    (quotientBlock_stable W)

attribute [local instance] quotientBrauerAction

/-- The restricted action has precisely the original character values. -/
@[simp] theorem quotientBrauerAction_val
    (a : BlockStabilizer W) (phi : FixedQuotientBrauerFibre W.relative) :
    (a • phi).val = a.val • phi.val := rfl

/-- The unique original character obtained from the existing complete
Brauer fibre equivalence. This makes no new selection of matched tails. -/
def preimage (phi : FixedQuotientBrauerFibre W.relative) :
    Definition35Brauer (family.problem block) :=
  (originalBrauerFibreEquivFixedQuotientBrauerFibre
    W.relative W.roots W.brauerReverse).symm phi

/-- The preimage descends to this very quotient character. -/
theorem preimage_brauer (phi : FixedQuotientBrauerFibre W.relative) :
    fixedDescendedBrauer W.relative W.roots (preimage W phi) = phi.val := by
  exact congrArg Subtype.val
    ((originalBrauerFibreEquivFixedQuotientBrauerFibre
      W.relative W.roots W.brauerReverse).apply_symm_apply phi)

/-- The quotient correspondence uses the weight of the same preimage. -/
theorem preimage_weight (phi : FixedQuotientBrauerFibre W.relative) :
    quotientWeightClass W.relative (preimage W phi) =
      (quotientEquiv W phi).val := rfl

/-- Every character of the full quotient block is centrally faithful in
the one fixed root convention used for that block. -/
theorem quotientEquiv_centralFaithful
    (phi : FixedQuotientBrauerFibre W.relative) :
    Subgroup.center (QuotientCarrier W.relative) ⊓
      (chosenIBrRepresentation (fixedQuotientRoot W.relative) phi.val).ρ.ker = ⊥ := by
  rw [← preimage_brauer W phi]
  exact transportIBrRoot_centralFaithful
    (W.roots.matchedRoot_eq_reference (preimage W phi))
    (W.relative.matched (preimage W phi)).quotient.brauer
    (W.relative.matched (preimage W phi)).quotient.centralFaithful

/-- Invariance of the stored graph becomes invariance of the complete
quotient correspondence, for actual quotient automorphisms. -/
theorem quotientEquiv_graph
    (alpha : (MulAut (QuotientCarrier W.relative))ᵐᵒᵖ)
    (phi chi : FixedQuotientBrauerFibre W.relative)
    (h : chi.val = alpha • phi.val) :
    (quotientEquiv W chi).val = alpha • (quotientEquiv W phi).val := by
  rw [← preimage_weight W chi, ← preimage_weight W phi]
  apply W.quotient_equivariant
  rw [preimage_brauer W chi, preimage_brauer W phi]
  exact h

/-- Definition 4.3(i), expressed on the underlying actual character and
weight actions of the full block stabilizer. -/
theorem quotientEquiv_equivariant_val
    (a : BlockStabilizer W) (phi : FixedQuotientBrauerFibre W.relative) :
    (quotientEquiv W (a • phi)).val = a.val • (quotientEquiv W phi).val :=
  quotientEquiv_graph W a.val phi (a • phi) rfl

/-- The same equivariance as an equality inside the complete weight fibre. -/
theorem quotientEquiv_equivariant
    (a : BlockStabilizer W) (phi : FixedQuotientBrauerFibre W.relative) :
    quotientEquiv W (a • phi) = a • quotientEquiv W phi := by
  apply Subtype.ext
  exact quotientEquiv_equivariant_val W a phi

/-- Decode the internally constructed full witness into the independent
single-block condition. The complete correspondence, its equivariance and
central faithfulness are derived above; all matched data are retained. -/
def fromBlockWitness :
    TypeBFixedBlockDecodedCondition.DecodedCondition family cover block where
  relative := W.relative
  roots := W.roots
  quotientBlockAction := W.quotientBlockAction
  quotientBlockSource := W.quotientBlockSource
  quotientBlockIdempotent := W.quotientBlockIdempotent
  quotientBlockCompatibility := W.quotientBlockCompatibility
  quotientRoots_agree := W.quotientRoots_agree
  quotientWeight_roots := W.quotientWeight_roots
  quotientInflation_roots := W.quotientInflation_roots
  quotientAmbient_roots := W.quotientAmbient_roots
  localAmbient_roots := W.localAmbient_roots
  intermediate_roots := W.intermediate_roots
  quotientBrauerBlock_transport := W.quotientBrauerBlock_transport
  omega := quotientEquiv W
  equivariant := fun alpha _ phi chi h => quotientEquiv_graph W alpha phi chi h
  centralFaithful := quotientEquiv_centralFaithful W
  matched_preimage := fun phi =>
    ⟨preimage W phi, preimage_brauer W phi, preimage_weight W phi⟩

end ModularRep.PaperProofs.TypeBFixedBlockQuotientEquivariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
