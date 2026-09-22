import ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientAction
import ModularRep.PaperProofs.EvenFieldStrongRelativeRootGuards

/-!
# Complete one specified block of the same strong relative witness

This K construction retains W verbatim. Its own quotient pair, both complete
fibres, stored specified label, all finite-root guards and actual quotient
graph come from the preceding computed consumers.

The specified quotient operations and their exact local support interpretation
remain explicit. Individual primitive equations do not imply that support
law for all compatible reductions. No new source record, matching, graph,
extension, intermediate choice or final family is supplied or selected here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldStrongRelativeCompleteBlock

open ModularRep CharacterWeight
open CyclicOuterLemma37ActualBlockFibres
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open EvenFieldFLZ57ChosenRootMetadata EvenFieldStrongRelativeQuotientWeight
open EvenFieldStrongRelativeQuotientBrauer EvenFieldStrongRelativeQuotientAction
open TypeBFullBlockCondition TypeBFixedRootDefinitionFamily
open TypeCCoherentFiniteRootConvention OddTwoGroupEquivWeightBlocks

universe u

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
variable (W : RelativeBlockConditionWitness family cover block)
variable (hcenter : Subgroup.center family.H = ⊥)
variable (C : Convention ell family.k family.K)
variable (admissible : FamilyRootAdmissibility family C)
variable (metadata : RelativeRootMetadata C W)

local instance quotientFintype : Fintype (QuotientCarrier W) := Fintype.ofFinite _

variable (SH :
  letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
  LocalBlockInductionSource (p := ell) (k := family.k) (K := family.K)
  (G := QuotientCarrier W) (Block := W.QuotientBlock))
variable (sourceAmbient : ∀ b : family.Block,
  family.blockSource.operations.ambientBlockData.blockIdempotent b = family.blockIdempotent b)
variable (targetAmbient :
  letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
  ∀ c : W.QuotientBlock,
  SH.operations.ambientBlockData.blockIdempotent c = W.quotientBlockIdempotent c)
variable (ownPrimitive :
  letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
  ∀ V : CharacterWeight ell family.K family.H,
  MonoidAlgebra.domCongr family.k family.k
      (normalizerEquiv (EvenFieldStrongRelativeQuotientWeight.quotientEquiv W hcenter) V.subgroup)
      (ownNormalizerBlock family.blockSource.operations V).1 =
    (ownNormalizerBlock SH.operations (V.mapGroupEquiv
      (EvenFieldStrongRelativeQuotientWeight.quotientEquiv W hcenter))).1)
variable (physical :
  letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
  OddTwoActualLocalBlockSupport.Source
  (fixedQuotientRoot W) SH.operations)

include physical in
/-- The existing specified law yields its guarded form on these SAME
operations; full finite-domain agreement implies the required restriction
compatibility, not conversely. -/
def guardedCompatibility :
    letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
    GuardedBlockCompatibility (fixedQuotientRoot W) SH.operations := by
  letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
  exact
    { normalizer_block_of_reduction V iotaN phiN roots reduction :=
        physical.normalizer_block_of_reduction V iotaN phiN
          (fun rho => Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
            rho.ρ (fixedQuotientRoot W) iotaN
            (Subgroup.normalizer (V.subgroup : Set (QuotientCarrier W))).subtype roots)
          reduction }

/-- Complete the literal single-block output while keeping W and every
one of its selected matched records unchanged. -/
def completeBlock : BlockWitness family cover block := by
  letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
  exact
    { relative := W
      roots := metadata.fixedQuotientRootSource
      brauerReverse := reverseSource W hcenter C admissible metadata
      quotientBlockAction := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
      quotientBlockSource := SH
      quotientBlockIdempotent := targetAmbient
      quotientBlockCompatibility := guardedCompatibility W hcenter SH physical
      quotientRoots_agree :=
        EvenFieldStrongRelativeRootGuards.quotientRoots_agree W C admissible metadata
      quotientWeight_roots := EvenFieldStrongRelativeRootGuards.quotientWeight_roots W C metadata
      quotientInflation_roots := EvenFieldStrongRelativeRootGuards.quotientInflation_roots W C metadata
      quotientAmbient_roots := EvenFieldStrongRelativeRootGuards.quotientAmbient_roots W C metadata
      localAmbient_roots := EvenFieldStrongRelativeRootGuards.localAmbient_roots W C metadata
      intermediate_roots := EvenFieldStrongRelativeRootGuards.intermediate_roots W C metadata
      quotientBrauerBlock_transport :=
        EvenFieldStrongRelativeQuotientAction.quotientBrauerBlock_transport
          W hcenter C admissible metadata
      weight_liesInQuotientBlock psi :=
        (quotientWeightClass_liesInPhysicalBlock W hcenter SH
          sourceAmbient targetAmbient ownPrimitive psi).trans
            (storedLabel_eq_physical W hcenter C admissible metadata).symm
      weight_injective := quotientWeightClass_injective W hcenter
      weight_reverse w := by
        let v : SH.Fibre (physicalLabel W hcenter) :=
          ⟨w.1, w.2.trans (storedLabel_eq_physical W hcenter C admissible metadata)⟩
        exact EvenFieldStrongRelativeQuotientWeight.weight_reverse W hcenter SH
          sourceAmbient targetAmbient ownPrimitive v
      quotient_equivariant := quotient_graph_equivariant W hcenter C admissible metadata }

/-- Every relative field, including all extensions and every-J packets, is
literally preserved rather than merely identified by an output premise. -/
@[simp] theorem completeBlock_relative :
    letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
    (completeBlock W hcenter C admissible metadata SH sourceAmbient targetAmbient
      ownPrimitive physical).relative = W := rfl

@[simp] theorem completeBlock_omega :
    letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
    (completeBlock W hcenter C admissible metadata SH sourceAmbient targetAmbient
      ownPrimitive physical).relative.omega = W.omega := rfl

@[simp] theorem completeBlock_source :
    letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
    (completeBlock W hcenter C admissible metadata SH sourceAmbient targetAmbient
      ownPrimitive physical).quotientBlockSource = SH := rfl

end ModularRep.PaperProofs.EvenFieldStrongRelativeCompleteBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
