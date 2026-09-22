import ModularRep.PaperProofs.TypeBFullBlockCondition
import ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
import ModularRep.PaperProofs.EvenFieldPhysicalBlockFibreReindexing

/-!
# The own quotient weight of an existing strong centreless witness

The relative witness is already returned by the stronger source. Its stored
ordinary descent equation and the actual centreless quotient isomorphism
identify its WHOLE raw quotient weight with the image of its own selected
weight. No equality of selected pairs or roots is an input.

The specified consumers use the two actual operation sets and the existing
individual primitive equations. They complete the weight fibre at the
COMPUTED specified label. Identification with the relative witness's stored
quotientBlock, its Brauer roots, global orbit choices and Q=1 normalization
remain separate. All matched extensions and intermediate records are kept.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientWeight

open ModularRep CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZCentrelessLocalPackets
open TypeBFullBlockCondition OddTwoGroupEquivWeightBlocks

universe u

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
variable (W : RelativeBlockConditionWitness family cover block)
variable (hcenter : Subgroup.center family.H = ⊥)

local instance quotientFintype : Fintype (QuotientCarrier W) := Fintype.ofFinite _

/-- The actual canonical quotient homomorphism, with its proved inverse. -/
abbrev quotientEquiv : family.H ≃* QuotientCarrier W :=
  centerlessCentralCharacterQuotientMapEquiv (family.problem block) hcenter W.reference

@[simp] theorem quotientEquiv_apply (x : family.H) :
    quotientEquiv W hcenter x =
      centralCharacterQuotientMap (family.problem block) W.reference x := rfl

/-- The original ordinaryDescends field determines the whole image pair.
The root and Brauer fields are not used to deduce this ordinary equality. -/
theorem quotientRawWeight_eq_map (psi : Definition35Brauer (family.problem block)) :
    quotientRawWeight W psi =
      (selectedCharacterWeight family.blockSource block (W.omega psi)).mapGroupEquiv
        (quotientEquiv W hcenter) := by
  symm
  apply mapGroupEquiv_eq_of_normalizer_coordinates
    (selectedCharacterWeight family.blockSource block (W.omega psi))
    (quotientEquiv W hcenter) (quotientRawWeight W psi) rfl
    (normalizerEquiv (quotientEquiv W hcenter)
      (selectedCharacterWeight family.blockSource block (W.omega psi)).subgroup)
  · intro x
    rfl
  · intro x
    exact (W.matched psi).weight.ordinaryDescends (QuotientGroup.mk x)

/-- The existing quotient class is the actual image of this same omega. -/
theorem quotientWeightClass_eq_map (psi : Definition35Brauer (family.problem block)) :
    quotientWeightClass W psi =
      conjugacyClassGroupEquiv (quotientEquiv W hcenter) (W.omega psi).1 := by
  have h := congrArg (conjugacyClassGroupEquiv (quotientEquiv W hcenter))
    (selectedCharacterWeight_spec family.blockSource block (W.omega psi))
  change (Quotient.mk'' (Quotient.mk''
    ((selectedCharacterWeight family.blockSource block (W.omega psi)).mapGroupEquiv
      (quotientEquiv W hcenter))) :
      ConjugacyClass (p := ell) (K := family.K) (G := QuotientCarrier W)) = _ at h
  exact (congrArg (fun V : CharacterWeight ell family.K (QuotientCarrier W) =>
    (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := ell) (K := family.K) (G := QuotientCarrier W)))
    (quotientRawWeight_eq_map W hcenter psi)).trans h

include hcenter in
/-- Injectivity follows from the two actual equivalences, without a reverse
quotient-fibre source or another correspondence. -/
theorem quotientWeightClass_injective : Function.Injective (quotientWeightClass W) := by
  intro psi chi h
  apply W.omega.injective
  apply Subtype.ext
  apply (conjugacyClassGroupEquiv (quotientEquiv W hcenter)).injective
  exact (quotientWeightClass_eq_map W hcenter psi).symm.trans
    (h.trans (quotientWeightClass_eq_map W hcenter chi))

/-- The entire class carrier uses the original right-action convention. -/
theorem quotientClassMap_twist
    (a : (MulAut family.H)ᵐᵒᵖ)
    (v : ConjugacyClass (p := ell) (K := family.K) (G := family.H)) :
    conjugacyClassGroupEquiv (quotientEquiv W hcenter) (a • v) =
      MulOpposite.op (MulAut.congr (quotientEquiv W hcenter) a.unop) •
        conjugacyClassGroupEquiv (quotientEquiv W hcenter) v :=
  conjugacyClassGroupEquiv_op_smul (quotientEquiv W hcenter) a v

section PhysicalFibre

variable [MulAction (MulAut (QuotientCarrier W))ᵐᵒᵖ W.QuotientBlock]
variable (SH : LocalBlockInductionSource (p := ell) (k := family.k) (K := family.K)
  (G := QuotientCarrier W) (Block := W.QuotientBlock))
variable (sourceAmbient : ∀ b : family.Block,
  family.blockSource.operations.ambientBlockData.blockIdempotent b = family.blockIdempotent b)
variable (targetAmbient : ∀ c : W.QuotientBlock,
  SH.operations.ambientBlockData.blockIdempotent c = W.quotientBlockIdempotent c)
variable (ownPrimitive : ∀ V : CharacterWeight ell family.K family.H,
  MonoidAlgebra.domCongr family.k family.k (normalizerEquiv (quotientEquiv W hcenter) V.subgroup)
    (ownNormalizerBlock family.blockSource.operations V).1 =
      (ownNormalizerBlock SH.operations (V.mapGroupEquiv (quotientEquiv W hcenter))).1)

/-- The complete primitive catalogues determine this label. No equality
with the separately stored W.quotientBlock is assumed or asserted here. -/
def physicalLabel : W.QuotientBlock :=
  EvenFieldPhysicalBlockFibreReindexing.blockLabelEquiv
    family.blocks W.quotientBlocks (quotientEquiv W hcenter) block

theorem physicalLabel_primitive :
    W.quotientBlockIdempotent (physicalLabel W hcenter) =
      MonoidAlgebra.domCongr family.k family.k (quotientEquiv W hcenter)
        (family.blockIdempotent block) :=
  EvenFieldPhysicalBlockFibreReindexing.blockLabelEquiv_primitive
    family.blocks W.quotientBlocks (quotientEquiv W hcenter) block

/-- Restrict the actual whole-weight map to the two specified fibres. -/
def weightFibreEquiv : Definition35Weight (family.problem block) ≃
    SH.Fibre (physicalLabel W hcenter) :=
  EvenFieldPhysicalBlockFibreReindexing.weightEquiv
    family.blocks W.quotientBlocks (quotientEquiv W hcenter)
    family.blockSource SH sourceAmbient targetAmbient ownPrimitive block

/-- The stored omega, followed by the computed specified fibre map. -/
def matchedWeightFibreEquiv : Definition35Brauer (family.problem block) ≃
    SH.Fibre (physicalLabel W hcenter) :=
  W.omega.trans (weightFibreEquiv W hcenter SH sourceAmbient targetAmbient ownPrimitive)

theorem matchedWeightFibreEquiv_value (psi : Definition35Brauer (family.problem block)) :
    (matchedWeightFibreEquiv W hcenter SH sourceAmbient targetAmbient ownPrimitive psi).1 =
      quotientWeightClass W psi :=
  (quotientWeightClass_eq_map W hcenter psi).symm

include sourceAmbient targetAmbient ownPrimitive in
theorem quotientWeightClass_liesInPhysicalBlock
    (psi : Definition35Brauer (family.problem block)) :
    SH.weightBlock (quotientWeightClass W psi) = physicalLabel W hcenter :=
  (congrArg SH.weightBlock
    (matchedWeightFibreEquiv_value W hcenter SH sourceAmbient targetAmbient ownPrimitive psi).symm).trans
      (matchedWeightFibreEquiv W hcenter SH sourceAmbient targetAmbient ownPrimitive psi).2

include sourceAmbient targetAmbient ownPrimitive in
/-- Completeness of this actual weight fibre follows by the computed inverse.
It supplies no Brauer reverse source or comparison of independent roots. -/
theorem weight_reverse (v : SH.Fibre (physicalLabel W hcenter)) :
    ∃ psi : Definition35Brauer (family.problem block), quotientWeightClass W psi = v.1 := by
  let E := matchedWeightFibreEquiv W hcenter SH sourceAmbient targetAmbient ownPrimitive
  refine ⟨E.symm v, ?_⟩
  exact (matchedWeightFibreEquiv_value W hcenter SH sourceAmbient targetAmbient ownPrimitive
    (E.symm v)).symm.trans (congrArg Subtype.val (E.apply_symm_apply v))

end PhysicalFibre
end ModularRep.PaperProofs.EvenFieldStrongRelativeQuotientWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
