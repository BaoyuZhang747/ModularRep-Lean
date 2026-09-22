import ModularRep.PaperProofs.TypeCOddTwoChosenRootMetadata
import ModularRep.PaperProofs.TypeCOddTwoOriginalIntermediateTransport
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# All finite-root guards for the same original chosen packets

The only scalar bindings are the actual target root, its selected quotient
roots and metadata of ONE jointly chosen original witness. The computed
coherent target supplies the first two bindings definitionally. No arbitrary
matched packet is upgraded and no representation compatibility is used to
infer an all-root assertion. Actual subgroup/quotient cardinalities and the
already proved coordinate equivalences supply every finite-domain guard.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalRootGuards

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open OddTwoLiteralSpathTarget TypeCCoherentFiniteRootConvention
open TypeCOddTwoChosenRootMetadata TypeCOddTwoOriginalBlockMatching
open TypeCOddTwoOriginalQuotientFibres TypeCOddTwoOriginalReferenceAmbient
open TypeCOddTwoOriginalChosenExtensions TypeCOddTwoOriginalIntermediateTransport
open TypeBFullBlockCondition

universe u

private abbrev HasConventionRoot
    {p : ℕ} {k K G : Type u} [Field k] [Field K] [Group G] [Finite G]
    (C : Convention p k K) (r : PrimeRegularRootEmbedding p k K G) : Prop :=
  r = C.rootAt G

private theorem transportedRoot_eq
    {p : ℕ} {k K G H : Type u} [Field k] [Field K]
    [Group G] [Finite G] [Group H] [Finite H]
    (C : Convention p k K) (r : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (hr : r = C.rootAt G) :
    r.alongMulEquiv e = C.rootAt H :=
  (congrArg (fun t : PrimeRegularRootEmbedding p k K G => t.alongMulEquiv e) hr).trans
    (C.rootAt_alongMulEquiv e)

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable {P : Problem n F} (D : Definition41 P) (C : Convention 2 P.k P.K)
variable (hRoot : P.iota = C.rootAt (X n F))
variable (hSelected : ∀ (b : P.Block)
  (w : CyclicOuterLemma37LiteralLocalExtension.LiteralWeightFibre P.blockSource b),
  HasConventionRoot C (P.localReduction b w).iota)
variable (metadata : ChosenRootMetadata C D)
variable (b : P.Block) (reference psi : Definition35Brauer (P.blockProblem b))

local instance guardSubgroupFintype {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Fintype H := Fintype.ofFinite _

local instance guardQuotientFintype :
    Fintype (CentralCharacterQuotient (P.blockProblem b) reference) := Fintype.ofFinite _

include hRoot in
/-- The reference quotient root is computed from the actual target root. -/
theorem quotient_root_eq :
    quotientRoot P b reference =
      C.rootAt (CentralCharacterQuotient (P.blockProblem b) reference) := by
  change P.iota.alongMulEquiv (referenceQuotientEquiv b reference) = _
  rw [hRoot]
  exact C.rootAt_alongMulEquiv (referenceQuotientEquiv b reference)

include hSelected in
/-- The selected quotient character retains its computed own root table. -/
theorem weight_root_eq :
    (quotientPacket D b reference psi).iota =
      C.rootAt (NormalizerQuotient
        (quotientRadical (P.blockProblem b) reference (blockEquiv D b psi))) := by
  rw [quotientPacket_root, hSelected b (blockEquiv D b psi)]
  exact C.rootAt_alongMulEquiv
    (EvenFieldFLZCentrelessLocalPackets.centerlessQuotientNormalizerEquiv
      (P.blockProblem b) P.center_eq_bot
      reference (blockEquiv D b psi))

include metadata in
/-- Only the original D.matched reduction supplies the normalizer metadata. -/
theorem inflation_root_eq :
    (localInflation D b reference psi).iota =
      C.rootAt (ReferenceNormalizer D b reference psi) := by
  change (selectedMatched D b psi).localReduction.root.alongMulEquiv
    (referenceNormalizerEquiv D b reference psi) = _
  rw [(metadata.matched (selectedRadical D b psi) (selectedPart D b psi)).normalizer_eq]
  exact C.rootAt_alongMulEquiv (referenceNormalizerEquiv D b reference psi)

include metadata in
theorem ambient_root_eq :
    (referenceExtensions D b reference psi).ambientRoot =
      C.rootAt (selectedReferenceAmbient D b reference psi).A :=
  (metadata.matched (selectedRadical D b psi) (selectedPart D b psi)).ambient_eq

include metadata in
theorem local_ambient_root_eq :
    (referenceExtensions D b reference psi).localAmbientRoot =
      C.rootAt (ReferenceLocalGroup D b reference psi) := by
  change (selectedMatched D b psi).extensions.localAmbientRoot.alongMulEquiv
    (ambientLocalEquiv D b reference psi) = _
  rw [(metadata.matched (selectedRadical D b psi) (selectedPart D b psi)).localAmbient_eq]
  exact C.rootAt_alongMulEquiv (ambientLocalEquiv D b reference psi)

include hRoot hSelected in
/-- Every quotient-normalizer root is bounded by the actual reference group. -/
theorem quotientWeight_roots :
    TypeBFixedRootDefinitionFamily.QuotientRootAgreement
      (quotientRoot P b reference)
      (quotientRadical (P.blockProblem b) reference (blockEquiv D b psi))
      (quotientPacket D b reference psi).iota := by
  rw [weight_root_eq D C hSelected b reference psi,
    quotient_root_eq C hRoot b reference]
  intro z
  let Q := quotientRadical (P.blockProblem b) reference (blockEquiv D b psi)
  let N := Subgroup.normalizer (Q : Set
    (CentralCharacterQuotient (P.blockProblem b) reference))
  exact C.rootAt_lift_of_card_dvd
    ((Q.subgroupOf N).card_quotient_dvd_card.trans
      (Subgroup.card_subgroup_dvd_card N)) z

include hRoot metadata in
/-- Every normalizer root is bounded by the same actual reference group. -/
theorem quotientInflation_roots :
    TypeBFixedRootDefinitionFamily.NormalizerRootAgreement
      (quotientRoot P b reference)
      (quotientRadical (P.blockProblem b) reference (blockEquiv D b psi))
      (localInflation D b reference psi).iota := by
  rw [inflation_root_eq D C metadata b reference psi,
    quotient_root_eq C hRoot b reference]
  exact C.rootAt_lift_subgroup (ReferenceNormalizer D b reference psi)

include hRoot metadata in
/-- The actual base equivalence bounds reference-quotient roots in A. -/
theorem quotientAmbient_roots :
    RootLiftAgreement (referenceSource P b reference psi).iota
      (referenceExtensions D b reference psi).ambientRoot := by
  change RootLiftAgreement (quotientRoot P b reference) _
  rw [quotient_root_eq C hRoot b reference,
    ambient_root_eq D C metadata b reference psi]
  intro z
  exact C.rootAt_lift_of_card_dvd
    ((Nat.card_congr (selectedReferenceAmbient D b reference psi).baseEquiv.toEquiv).dvd.trans
      (Subgroup.card_subgroup_dvd_card
        (selectedReferenceAmbient D b reference psi).base)) z

include metadata in
/-- The actual local ambient subgroup gives all its roots in A. -/
theorem localAmbient_roots :
    RootLiftAgreement (referenceExtensions D b reference psi).localAmbientRoot
      (referenceExtensions D b reference psi).ambientRoot := by
  rw [local_ambient_root_eq D C metadata b reference psi,
    ambient_root_eq D C metadata b reference psi]
  exact C.rootAt_lift_subgroup (ReferenceLocalGroup D b reference psi)

variable (J : Subgroup (selectedMatched D b psi).ambient.A)
variable (hJ : (selectedMatched D b psi).ambient.base ≤ J)

local instance guardReferenceAmbientGroup :
    Group (selectedReferenceAmbient D b reference psi).A :=
  (selectedMatched D b psi).ambient.groupA

local instance guardJGroup : Group ↥J :=
  @Subgroup.toGroup (selectedMatched D b psi).ambient.A
    (selectedMatched D b psi).ambient.groupA J

include metadata in
/-- The very same original intermediate choice carries its two root bindings. -/
theorem intermediate_root_eq :
    (intermediateAt D b reference psi J hJ).globalRoot = C.rootAt ↥J ∧
      (intermediateAt D b reference psi J hJ).localRoot =
        C.rootAt (NewLocal D b reference psi J) := by
  have hm := (metadata.matched (selectedRadical D b psi)
    (selectedPart D b psi)).intermediate_eq
      (directH D b psi J) (directH_le D b psi J)
      (base_inter_le_directH D b psi J hJ)
  have hg : (sourceIntermediate D b psi J hJ).globalRoot =
      C.rootAt ↥((selectedMatched D b psi).ambient.base ⊔ directH D b psi J) := hm.1
  have hl : (sourceIntermediate D b psi J hJ).localRoot =
      C.rootAt (OldLocal D b psi J) := hm.2
  exact ⟨transportedRoot_eq C (sourceIntermediate D b psi J hJ).globalRoot
      (globalEquiv D b psi J hJ) hg,
    transportedRoot_eq C (sourceIntermediate D b psi J hJ).localRoot
      (localEquiv D b reference psi J hJ) hl⟩

include metadata in
/-- Both finite-domain guards for EVERY actual J containing the same base. -/
theorem intermediate_roots :
    RootLiftAgreement (H := ↥J) (A := (selectedMatched D b psi).ambient.A)
        (intermediateAt D b reference psi J hJ).globalRoot
        (referenceExtensions D b reference psi).ambientRoot ∧
      RootLiftAgreement (H := ↥(NewLocal D b reference psi J))
        (A := (selectedMatched D b psi).ambient.A)
        (intermediateAt D b reference psi J hJ).localRoot
        (referenceExtensions D b reference psi).ambientRoot := by
  rw [(intermediate_root_eq D C metadata b reference psi J hJ).1,
    (intermediate_root_eq D C metadata b reference psi J hJ).2,
    ambient_root_eq D C metadata b reference psi]
  constructor
  · exact C.rootAt_lift_subgroup J
  · intro z
    exact C.rootAt_lift_of_card_dvd
      ((Subgroup.card_subgroup_dvd_card (NewLocal D b reference psi J)).trans
        (Subgroup.card_subgroup_dvd_card J)) z

end ModularRep.PaperProofs.TypeCOddTwoOriginalRootGuards


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
