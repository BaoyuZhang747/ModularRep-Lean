import ModularRep.PaperProofs.EvenFieldFLZ57ChosenRootMetadata
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# Finite-root guards for the same selected strong FLZ packets

The standard convention and its chosen metadata are fixed inputs to this K
consumer. Actual subgroup, quotient and base-equivalence cardinal divisibility
gives every finite-domain root agreement required by the complete block target.
No representation-level compatibility is used to infer all-root equality.
No character, extension, intermediate record or matching is replaced.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldStrongRelativeRootGuards

open ModularRep CharacterWeight
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open EvenFieldFLZ57ChosenRootMetadata TypeCCoherentFiniteRootConvention
open TypeBFullBlockCondition TypeBFixedRootDefinitionFamily

universe u

private theorem agreement_of_eq {ell : ℕ} {k K G H : Type u}
    [Field k] [Field K] [Group G] [Finite G] [Group H] [Finite H]
    (C : Convention ell k K)
    (iG : PrimeRegularRootEmbedding ell k K G)
    (iH : PrimeRegularRootEmbedding ell k K H)
    (hG : iG = C.rootAt G) (hH : iH = C.rootAt H)
    (card : Nat.card G ∣ Nat.card H) : RootLiftAgreement iG iH := by
  subst iG
  subst iH
  exact C.rootAt_lift_of_card_dvd card

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
variable (W : RelativeBlockConditionWitness family cover block)
variable (C : Convention ell family.k family.K)
variable (admissible : FamilyRootAdmissibility family C)
variable (metadata : RelativeRootMetadata C W)

local instance strongQuotientFintype : Fintype (QuotientCarrier W) := Fintype.ofFinite _
local instance strongSubgroupFintype {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : Fintype N := Fintype.ofFinite _

include metadata in
/-- This is the root already stored at the actual reference character. -/
theorem fixedRoot_eq : fixedQuotientRoot W = C.rootAt (QuotientCarrier W) :=
  (metadata.matched W.reference).quotient_eq

include admissible metadata in
/-- The actual central quotient's cardinality divides the original group. -/
theorem quotientRoots_agree : RootLiftAgreement (fixedQuotientRoot W) family.iota :=
  agreement_of_eq C _ _ (fixedRoot_eq W C metadata) admissible.ambient_eq
    (centralCharacterKernel (family.problem block) W.reference).card_quotient_dvd_card

variable (psi : Definition35Brauer (family.problem block))

include metadata in
/-- Own quotient roots agree on their entire finite domain with the SAME
fixed quotient root, by the two actual cardinal divisibilities. -/
theorem quotientWeight_roots :
    QuotientRootAgreement (fixedQuotientRoot W)
      (quotientRadical (family.problem block) W.reference (W.omega psi))
      (W.matched psi).weight.iota := by
  let Q := quotientRadical (family.problem block) W.reference (W.omega psi)
  let N := Subgroup.normalizer (Q : Set (QuotientCarrier W))
  exact agreement_of_eq C _ _ (metadata.matched psi).weight_eq
    (fixedRoot_eq W C metadata)
    ((Q.subgroupOf N).card_quotient_dvd_card.trans (Subgroup.card_subgroup_dvd_card N))

include metadata in
/-- The own normalizer is the literal subgroup of the SAME quotient. -/
theorem quotientInflation_roots :
    NormalizerRootAgreement (fixedQuotientRoot W)
      (quotientRadical (family.problem block) W.reference (W.omega psi))
      (W.matched psi).localInflation.iota :=
  agreement_of_eq C _ _ (metadata.matched psi).normalizer_eq
    (fixedRoot_eq W C metadata)
    (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer
      (quotientRadical (family.problem block) W.reference (W.omega psi) :
        Set (QuotientCarrier W))))

include metadata in
/-- The quotient is the actual normal base of the selected ambient group. -/
theorem quotientAmbient_roots :
    RootLiftAgreement (W.matched psi).quotient.iota
      (W.matched psi).extensions.ambientRoot :=
  agreement_of_eq C _ _ (metadata.matched psi).quotient_eq
    (metadata.matched psi).ambient_eq
    ((Nat.card_congr (W.matched psi).ambient.baseEquiv.toEquiv).dvd.trans
      (Subgroup.card_subgroup_dvd_card (W.matched psi).ambient.base))

include metadata in
/-- The actual local ambient normalizer is a subgroup of that same A. -/
theorem localAmbient_roots :
    RootLiftAgreement (W.matched psi).extensions.localAmbientRoot
      (W.matched psi).extensions.ambientRoot :=
  agreement_of_eq C _ _ (metadata.matched psi).localAmbient_eq
    (metadata.matched psi).ambient_eq
    (Subgroup.card_subgroup_dvd_card
      (AmbientLocalGroup (family.problem block) W.reference psi (W.omega psi)
        (W.matched psi).quotient (W.matched psi).ambient))

variable (J : Subgroup (W.matched psi).ambient.A)
variable (hJ : (W.matched psi).ambient.base ≤ J)

local instance strongIntermediateGroup : Group ↥J :=
  @Subgroup.toGroup (W.matched psi).ambient.A (W.matched psi).ambient.groupA J

include metadata in
/-- Both guards belong to the SAME selected record for EVERY actual J. -/
theorem intermediate_roots :
    RootLiftAgreement ((W.matched psi).intermediateBlocks.equalityAt J hJ).globalRoot
        (W.matched psi).extensions.ambientRoot ∧
      RootLiftAgreement ((W.matched psi).intermediateBlocks.equalityAt J hJ).localRoot
        (W.matched psi).extensions.ambientRoot := by
  have h := (metadata.matched psi).intermediate_eq J hJ
  constructor
  · exact agreement_of_eq C _ _ h.1 (metadata.matched psi).ambient_eq
      (Subgroup.card_subgroup_dvd_card J)
  · exact agreement_of_eq C _ _ h.2 (metadata.matched psi).ambient_eq
      ((Subgroup.card_subgroup_dvd_card
        (IntermediateLocalNormalizer (w := W.omega psi) (W.matched psi).ambient J)).trans
        (Subgroup.card_subgroup_dvd_card J))

end ModularRep.PaperProofs.EvenFieldStrongRelativeRootGuards


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
