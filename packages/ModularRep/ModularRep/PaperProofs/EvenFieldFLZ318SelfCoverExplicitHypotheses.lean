import ModularRep.PaperProofs.EvenFieldFLZ318NormalizerIdentification
import ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverEqualGroupClauseIII
import ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverLinearReductionBridge

/-!
# Explicit self-cover hypotheses for Feng--Li--Zhang, Theorem 3.18

This module packages the hypotheses of Feng--Li--Zhang, Theorem 3.18(i)--(iv),
in the centreless self-cover situation used in manuscript Lemma 2.10.  It stops
before the cited theorem is applied and defines neither BAW-goodness nor iBAW.

The package has explicit external boundaries.  The caller supplies the named
source operations in clause (iii), their identification with the equal-group
candidates, and the coherent-root inputs used to turn representation
extensions into character extensions in clause (iv).  These inputs are U/E2,
not kernel evidence for the corresponding source semantics.  Once the root
inputs are supplied, clause (iv) stores actual extension witnesses rather than
conditional implications.  The typed clause-(iii) adapters remain explicit at
the final Theorem 3.18 application boundary.

The package distinguishes literal kernel evidence from the remaining source
semantics.  The operations in `ClauseIIISourceOperations` stand for the exact
restriction, weight-covering, Clifford, induction, and `Delta` operations in
the cited sources.  `ClauseIIISelfCoverAdapters` asks separately for their
identification with the uniquely forced equal-group candidates.  The
restriction and carrier identifications are U; weight covering, Clifford,
induction, and `Delta` use the cited DGN/Clifford theory and are E2/U.  Clause
(iii)(c) retains the chosen extension as data and makes induction, `Delta`, and
literal block induction depend on that same choice.  None of these source
identifications is derived from equality of the candidate carriers.

The sets of ordinary and modular linear characters of the quotient used below are
the literal homomorphism carriers already constructed in the project.  Their
reduction equivalence and field equivariance are kernel checked.  Identifying
them with the exact packaged `Lin_{ell'}` and `LinBr` carriers and actions of
the source remains U.

Clause (iv)(b) uses only the canonical normaliser-quotient input.  Its stored
character-level witness is obtained on the full pair stabiliser and transported
through the typed equality `D intersection H = N_H(Q)`.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverExplicitHypotheses

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZ318CharacterExtensions
open ModularRep.PaperProofs.EvenFieldFLZ318InflatedLocalCharacterExtension
open ModularRep.PaperProofs.EvenFieldFLZ318NormalizerIdentification
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverEqualGroupClauseIII
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverLinearReductionBridge

universe u

section ClauseIIISourceInterface

variable {p : ℕ} {k K H ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

/-- Caller-supplied source-operation interface for clause (iii).  Each field
has the carrier and arity of one named source operation, but its identification
with that operation remains U/E2 and receives no kernel credit. -/
structure ClauseIIISourceOperations where
  brauerRestrictsTo :
    BrauerFibre iota hinj blocks block →
      BrauerFibre iota hinj blocks block → Prop
  weightCovers :
    WeightFibre blockSource block → WeightFibre blockSource block → Prop
  brauerCentralFibre :
    (Subgroup.center H →* Kˣ) → Set (BrauerFibre iota hinj blocks block)
  weightCentralFibre :
    (Subgroup.center H →* Kˣ) → Set (WeightFibre blockSource block)
  cliffordCorrespondentOf :
    BrauerFibre iota hinj blocks block →
      BrauerFibre iota hinj blocks block →
      BrauerFibre iota hinj blocks block → Prop
  localInductionResultOf :
    {w : WeightFibre blockSource block} →
      SameGroupLocalCharacterExtensionData blockSource block w →
        CharacterWeight p K H → Prop
  deltaImageOf :
    {w : WeightFibre blockSource block} →
      SameGroupLocalCharacterExtensionData blockSource block w →
        CharacterWeight p K H → CharacterWeight p K H → Prop

/-- The source fibres determined by the two covering relations. -/
def ClauseIIISourceOperations.brauerCoveringFibre
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (psi : BrauerFibre iota hinj blocks block) :
    Set (BrauerFibre iota hinj blocks block) :=
  {psiTilde | operations.brauerRestrictsTo psiTilde psi}

def ClauseIIISourceOperations.weightCoveringFibre
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (w : WeightFibre blockSource block) :
    Set (WeightFibre blockSource block) :=
  {wTilde | operations.weightCovers wTilde w}

/-- Exact self-cover adapters for the named source operations.  The restriction
and two central-fibre fields are carrier identifications (U).  Weight covering
and the final three relation fields use DGN, Clifford, character induction, or
`Delta` content and remain E2/U. -/
structure ClauseIIISelfCoverAdapters
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block) where
  brauerRestriction_iff_candidate :
    ∀ psiTilde psi : BrauerFibre iota hinj blocks block,
      operations.brauerRestrictsTo psiTilde psi ↔
        SameGroupBrauerRestriction iota hinj blocks block psiTilde psi
  weightCovering_iff_candidate :
    ∀ wTilde w : WeightFibre blockSource block,
      operations.weightCovers wTilde w ↔
        SameGroupWeightCoveringCandidate blockSource block wTilde w
  brauerCentralFibre_eq_candidate :
    ∀ (hcenter : Subgroup.center H = ⊥) (nu : Subgroup.center H →* Kˣ),
      operations.brauerCentralFibre nu =
        SameGroupBrauerCentralFibre
          iota hinj blocks block hcenter nu
  weightCentralFibre_eq_candidate :
    ∀ (hcenter : Subgroup.center H = ⊥) (nu : Subgroup.center H →* Kˣ),
      operations.weightCentralFibre nu =
        SameGroupWeightCentralFibre blockSource block hcenter nu
  clifford_iff_candidate :
    ∀ hatPsi psiTilde psi : BrauerFibre iota hinj blocks block,
      operations.cliffordCorrespondentOf hatPsi psiTilde psi ↔
        SameGroupBrauerRestriction
            iota hinj blocks block psiTilde psi ∧
          SameGroupCliffordCorrespondentCandidate
            iota hinj blocks block hatPsi psiTilde
  localInduction_iff_candidate :
    ∀ {w : WeightFibre blockSource block}
      (extensionData :
        SameGroupLocalCharacterExtensionData blockSource block w)
      (induced : CharacterWeight p K H),
      operations.localInductionResultOf extensionData induced ↔
        induced = selectedCharacterWeight blockSource block w
  delta_iff_candidate :
    ∀ {w : WeightFibre blockSource block}
      (extensionData :
        SameGroupLocalCharacterExtensionData blockSource block w)
      (image source : CharacterWeight p K H),
      operations.deltaImageOf extensionData image source ↔
        SameGroupDeltaInductionCandidate image source

theorem sourceBrauerCoveringFibre_eq_candidate
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (adapters : ClauseIIISelfCoverAdapters
      iota hinj blocks blockSource block operations)
    (psi : BrauerFibre iota hinj blocks block) :
    ClauseIIISourceOperations.brauerCoveringFibre
        iota hinj blocks blockSource block operations psi =
      SameGroupBrauerCoveringFibre iota hinj blocks block psi := by
  ext psiTilde
  exact adapters.brauerRestriction_iff_candidate psiTilde psi

theorem sourceWeightCoveringFibre_eq_candidate
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (adapters : ClauseIIISelfCoverAdapters
      iota hinj blocks blockSource block operations)
    (w : WeightFibre blockSource block) :
    ClauseIIISourceOperations.weightCoveringFibre
        iota hinj blocks blockSource block operations w =
      SameGroupWeightCoveringCandidateFibre blockSource block w := by
  ext wTilde
  exact adapters.weightCovering_iff_candidate wTilde w

end ClauseIIISourceInterface

section ClauseIIIData

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (field : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks field block)

/-- The literal self-cover model of the group acting in clause (iii): the
group of ordinary linear characters of the quotient, with its field action, extended
by `E`.  Its identification with the exact source `Lin_{ell'} ⋊ E_B` is U. -/
abbrev ClauseIIIActingGroup :=
  SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H) ⋊[
    LinearCharactersTrivialOn.fieldAction (k := K) field
      (selfCoverTop_isFieldStable field)] E

/-- Since the quotient-linear character factor is trivial, the literal action
on the Brauer block fibre factors through `E`. -/
@[instance_reducible]
def clauseIIIBrauerAction :
    MulAction (ClauseIIIActingGroup (K := K) field)
      (BrauerFibre iota hinj blocks block) := by
  let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks field block
      T.outerBlock_fixed T.brauerBlock_transport
  exact MulAction.compHom _ (SemidirectProduct.rightHom
    (φ := LinearCharactersTrivialOn.fieldAction (k := K) field
      (selfCoverTop_isFieldStable field)))

/-- The corresponding action on the literal weight block fibre. -/
@[instance_reducible]
def clauseIIIWeightAction :
    MulAction (ClauseIIIActingGroup (K := K) field)
      (WeightFibre blockSource block) := by
  let _ : MulAction E (WeightFibre blockSource block) :=
    rightWeightFibreMulAction field blockSource block T.outerBlock_fixed
  exact MulAction.compHom _ (SemidirectProduct.rightHom
    (φ := LinearCharactersTrivialOn.fieldAction (k := K) field
      (selfCoverTop_isFieldStable field)))

theorem cyclicEndgameOmega_clauseIII_equivariant
    {localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w}
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction)
    (a : ClauseIIIActingGroup (K := K) field)
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction (ClauseIIIActingGroup (K := K) field)
        (BrauerFibre iota hinj blocks block) :=
      clauseIIIBrauerAction iota hinj blocks field block T
    let _ : MulAction (ClauseIIIActingGroup (K := K) field)
        (WeightFibre blockSource block) :=
      clauseIIIWeightAction iota hinj blocks field blockSource block T
    endgame.omega.toEquiv (a • psi) = a • endgame.omega.toEquiv psi := by
  dsimp only
  exact endgame.omega.equivariant a.right psi

/-- Clause (iii)(c) with every source operation separately named.  A single
chosen extension feeds both induction and `Delta`, while its inflated block
literally induces to the Clifford correspondent's block.  The named source
relations retain their U/E2 boundary. -/
structure ClauseIIIcSourceData
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (psi : BrauerFibre iota hinj blocks block) where
  liftedBrauer : BrauerFibre iota hinj blocks block
  liftedBrauer_restricts : operations.brauerRestrictsTo liftedBrauer psi
  cliffordBrauer : BrauerFibre iota hinj blocks block
  clifford_spec :
    operations.cliffordCorrespondentOf cliffordBrauer liftedBrauer psi
  liftedWeight : CharacterWeight p K H
  liftedWeight_spec :
    (Quotient.mk'' (Quotient.mk'' liftedWeight) :
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H)) =
        (omega liftedBrauer).1
  localCharacterExtension :
    SameGroupLocalCharacterExtensionData blockSource block (omega psi)
  inducedWeight : CharacterWeight p K H
  induction_spec :
    operations.localInductionResultOf localCharacterExtension inducedWeight
  delta_spec : operations.deltaImageOf localCharacterExtension
    liftedWeight inducedWeight
  block_induction : SameGroupLocalExtensionBlockInducesTo
    iota hinj blocks blockSource block (omega psi)
    localCharacterExtension cliffordBrauer

/-- Convert the kernel-checked equal-group candidate into source-shaped data
only after the narrow source adapters have been supplied. -/
def clauseIIIcSourceData_of_candidate
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (adapters : ClauseIIISelfCoverAdapters
      iota hinj blocks blockSource block operations)
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (psi : BrauerFibre iota hinj blocks block)
    (candidate : EqualGroupClauseIIIcCarrierCandidateData
      iota hinj blocks blockSource block omega psi) :
    ClauseIIIcSourceData iota hinj blocks blockSource block
      operations omega psi where
  liftedBrauer := candidate.liftedBrauer
  liftedBrauer_restricts :=
    (adapters.brauerRestriction_iff_candidate
      candidate.liftedBrauer psi).2
        candidate.liftedBrauer_restrictionCandidate
  cliffordBrauer := candidate.cliffordCandidate
  clifford_spec :=
    (adapters.clifford_iff_candidate
      candidate.cliffordCandidate candidate.liftedBrauer psi).2
        ⟨candidate.liftedBrauer_restrictionCandidate,
          candidate.cliffordCandidate_spec⟩
  liftedWeight := candidate.liftedWeight
  liftedWeight_spec := candidate.liftedWeight_spec
  localCharacterExtension := candidate.localCharacterExtension
  inducedWeight := candidate.inducedWeight
  induction_spec :=
    (adapters.localInduction_iff_candidate
      candidate.localCharacterExtension candidate.inducedWeight).2
        candidate.inducedWeight_spec
  delta_spec :=
    (adapters.delta_iff_candidate
      candidate.localCharacterExtension
      candidate.liftedWeight candidate.inducedWeight).2
        candidate.deltaInduction_spec
  block_induction := sameGroupLocalExtensionBlockInducesTo
    iota hinj blocks blockSource block (omega psi)
      candidate.localCharacterExtension candidate.cliffordCandidate

/-- The exact source-shaped content retained for clause (iii).  Its source
relations are obtained only through `ClauseIIISelfCoverAdapters`; the literal
block induction is kernel combined from the chosen extension and the fixed
block catalogues.  This structure does not assert that the adapters have been
proved in Lean. -/
structure ClauseIIIHypotheses
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (omega : EquivariantEquiv E
      (BrauerFibre iota hinj blocks block)
      (WeightFibre blockSource block)
      (rightIBrBlockMulAction iota hinj blocks field block
        T.outerBlock_fixed T.brauerBlock_transport).smul
      (rightWeightFibreMulAction field blockSource block
        T.outerBlock_fixed).smul) where
  ordinaryToBrauerLinearReduction :
    SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H) ≃*
      SelfCoverLinearBrauerCharacters (p := p) (k := k) (H := H)
  ordinaryToBrauerLinearReduction_field_equivariant :
    ∀ (e : E)
      (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)),
      ordinaryToBrauerLinearReduction
          (LinearCharactersTrivialOn.fieldAction (k := K) field
            (selfCoverTop_isFieldStable field) e lambda) =
        LinearCharactersTrivialOn.fieldAction (k := k) field
          (selfCoverTop_isFieldStable field) e
          (ordinaryToBrauerLinearReduction lambda)
  liftedOmega_linearFieldEquivariant :
    ∀ (a : ClauseIIIActingGroup (K := K) field)
      (psi : BrauerFibre iota hinj blocks block),
      let _ : MulAction (ClauseIIIActingGroup (K := K) field)
          (BrauerFibre iota hinj blocks block) :=
        clauseIIIBrauerAction iota hinj blocks field block T
      let _ : MulAction (ClauseIIIActingGroup (K := K) field)
          (WeightFibre blockSource block) :=
        clauseIIIWeightAction iota hinj blocks field blockSource block T
      omega.toEquiv (a • psi) = a • omega.toEquiv psi
  covering_fibres :
    ∀ psi : BrauerFibre iota hinj blocks block,
      omega.toEquiv ''
          ClauseIIISourceOperations.brauerCoveringFibre
            iota hinj blocks blockSource block operations psi =
        ClauseIIISourceOperations.weightCoveringFibre
          iota hinj blocks blockSource block operations (omega.toEquiv psi)
  central_character_fibres :
    ∀ nu : Subgroup.center H →* Kˣ,
      omega.toEquiv '' operations.brauerCentralFibre nu =
        operations.weightCentralFibre nu
  block_clifford_delta_data :
    ∀ psi : BrauerFibre iota hinj blocks block,
      ClauseIIIcSourceData iota hinj blocks blockSource block
        operations omega.toEquiv psi

def clauseIIIHypotheses_of_cyclicEndgame
    {localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w}
    (hcenter : Subgroup.center H = ⊥)
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (adapters : ClauseIIISelfCoverAdapters
      iota hinj blocks blockSource block operations)
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction) :
    ClauseIIIHypotheses iota hinj blocks field blockSource block T
      operations endgame.omega where
  ordinaryToBrauerLinearReduction :=
    selfCoverOrdinaryToBrauerReductionEquiv iota
  ordinaryToBrauerLinearReduction_field_equivariant := fun e lambda ↦
    selfCoverOrdinaryToBrauerReduction_field_equivariant iota field e lambda
  liftedOmega_linearFieldEquivariant := fun a psi ↦
    cyclicEndgameOmega_clauseIII_equivariant
      iota hinj blocks field blockSource block T endgame a psi
  covering_fibres := fun psi ↦ by
    rw [sourceBrauerCoveringFibre_eq_candidate
      iota hinj blocks blockSource block operations adapters psi]
    rw [sourceWeightCoveringFibre_eq_candidate
      iota hinj blocks blockSource block operations adapters
        (endgame.omega.toEquiv psi)]
    exact sameGroupCoveringCandidateFibre_image
      iota hinj blocks blockSource block endgame.omega.toEquiv psi
  central_character_fibres := fun nu ↦ by
    rw [adapters.brauerCentralFibre_eq_candidate hcenter nu]
    rw [adapters.weightCentralFibre_eq_candidate hcenter nu]
    exact sameGroupCentralFibre_image iota hinj blocks blockSource block
      endgame.omega.toEquiv hcenter nu
  block_clifford_delta_data := fun psi ↦
    clauseIIIcSourceData_of_candidate iota hinj blocks blockSource block
      operations adapters endgame.omega.toEquiv psi
      (equalGroupClauseIIIcCarrierCandidateData_of_cyclicEndgame
        iota hinj blocks field blockSource block T localReduction endgame psi)

end ClauseIIIData

section SourceClausePackage

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (field : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks field block)
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)

/-- The identity extension for a raw weight character in the self-cover.
This is quantified before passage to conjugacy classes, as in
Feng--Li--Zhang, Theorem 3.18(i)(d). -/
def RawClauseIDSelfCoverExtension
    (w : CharacterWeight p K H) : Prop :=
  let Q := w.subgroup
  let N := Subgroup.normalizer (Q : Set H)
  let QN := Q.subgroupOf N
  ∃ R : OrdinaryIrreducibleCharacter.Realisation K (N ⧸ QN)
      w.localCharacter.1,
    Nonempty (Representation.Extension
      (⊤ : Subgroup N)
      (Representation.pullback
        (Representation.pullback R.representation (QuotientGroup.mk' QN))
        (⊤ : Subgroup N).subtype))

/-- Every raw weight character has the required identity extension when
the regular overgroup is the group itself. -/
theorem rawClauseIDSelfCoverExtension
    (w : CharacterWeight p K H) :
    RawClauseIDSelfCoverExtension (K := K) w := by
  dsimp only [RawClauseIDSelfCoverExtension]
  rcases w.localCharacter.2 with ⟨R⟩
  exact ⟨R, ⟨identityExtension
    (Representation.pullback R.representation
      (QuotientGroup.mk'
        (w.subgroup.subgroupOf
          (Subgroup.normalizer (w.subgroup : Set H)))))⟩⟩

/-- The self-cover specialisation of clause (i).  The extension fields are
the literal identity-extension statements available in the project.  Their
identification with the source's packaged ordinary and Brauer character
notions remains U. -/
structure ClauseIHypotheses where
  selfCover_normal : (EmbeddedSelfCover field).Normal
  perfect : Group.IsPerfect H
  outer_abelian : IsMulCommutative E
  block_invariant : ∀ g : H ⋊[field] E,
    let _ : MulAction H ι := SelfCoverBlockHAction
    let _ : MulAction E ι := SelfCoverBlockEAction field
    let _ : MulAction (H ⋊[field] E) ι :=
      semidirectMulAction field
        (rightAutomorphismSemidirectCompatible (X := ι) field)
    g • block = block
  centralizer :
    Subgroup.centralizer (EmbeddedSelfCover field : Set (H ⋊[field] E)) =
      EmbeddedSelfCoverCentre field
  embeddedCentre_normal : (EmbeddedSelfCoverCentre field).Normal
  automorphismQuotient :
    letI : (EmbeddedSelfCoverCentre field).Normal := embeddedCentre_normal
    Nonempty (((H ⋊[field] E) ⧸ EmbeddedSelfCoverCentre field) ≃* MulAut H)
  globalSelfCoverExtension :
    ∀ psi : BrauerFibre iota hinj blocks block,
      ClauseICSelfCoverExtension iota hinj blocks block psi
  localSelfCoverExtension :
    ∀ w : CharacterWeight p K H,
      blockSource.operations.rawWeightBlock w = block →
        RawClauseIDSelfCoverExtension (K := K) w

/-- Clause (ii) for one fixed bijection on the literal block fibres and their
canonical right actions. -/
structure ClauseIIHypotheses
    (omega : EquivariantEquiv E
    (BrauerFibre iota hinj blocks block)
    (WeightFibre blockSource block)
    (rightIBrBlockMulAction iota hinj blocks field block
      T.outerBlock_fixed T.brauerBlock_transport).smul
    (rightWeightFibreMulAction field blockSource block
      T.outerBlock_fixed).smul) where
  semidirect_equivariant :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks field block
        T.outerBlock_fixed T.brauerBlock_transport
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction field blockSource block T.outerBlock_fixed
    let _ : MulAction (H ⋊[field] E)
        (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction field
        (FibreTransportSource.brauerFibre_compatible
          (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
          (blockSource := blockSource) (block := block) (T := T))
    let _ : MulAction (H ⋊[field] E)
        (WeightFibre blockSource block) :=
      semidirectMulAction field
        (FibreTransportSource.weightFibre_compatible
          (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
          (blockSource := blockSource) (block := block) (T := T))
    ∀ (g : H ⋊[field] E) (psi : BrauerFibre iota hinj blocks block),
      omega.toEquiv (g • psi) = g • omega.toEquiv psi

/-- The root embedding and compatibility input used to turn the protected
global representation extension into a character extension.  This is a
narrow E2/U source input, not kernel evidence. -/
structure ClauseIVAGlobalRootInput
    (psi : BrauerFibre iota hinj blocks block) where
  iotaAmbient :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks field block
        T.outerBlock_fixed T.brauerBlock_transport
    let haction := FibreTransportSource.brauerFibre_compatible
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) (T := T)
    let _ : MulAction (H ⋊[field] E)
        (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction field haction
    PrimeRegularRootEmbedding p k K
      (semidirectStabilizer (phi := field) psi)
  compatible :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks field block
        T.outerBlock_fixed T.brauerBlock_transport
    let haction := FibreTransportSource.brauerFibre_compatible
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) (T := T)
    let _ : MulAction (H ⋊[field] E)
        (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction field haction
    let hinner : ∀ h : H,
        (SemidirectProduct.inl h : H ⋊[field] E) • psi = psi := fun h ↦ by
      rw [semidirect_inl_smul]
      exact FibreTransportSource.inner_fixes_brauerFibre
        (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
        (blockSource := blockSource) (block := block) (T := T) h psi
    let eH := canonicalHToEmbeddedEquiv psi hinner
    let iotaEmbedded := iota.alongMulEquiv eH
    ∀ (W : FDRep k (embeddedHStabilizer (phi := field) psi))
      (extension : Representation.Extension
        (embeddedHStabilizer (phi := field) psi) W.ρ),
      Representation.BrauerRootLiftCompatibleAlong
        extension.representation iotaAmbient iotaEmbedded
        (embeddedHStabilizer (phi := field) psi).subtype

/-- The nonconditional global character-extension result for a fixed root
input. -/
def ClauseIVAGlobalExtensionResult
    (psi : BrauerFibre iota hinj blocks block)
    (roots : ClauseIVAGlobalRootInput
      iota hinj blocks field blockSource block T psi) : Prop :=
  let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (FibreTransportSource.innerBlock_fixed
        (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks field block
      T.outerBlock_fixed T.brauerBlock_transport
  let haction := FibreTransportSource.brauerFibre_compatible
    (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
    (blockSource := blockSource) (block := block) (T := T)
  let _ : MulAction (H ⋊[field] E)
      (BrauerFibre iota hinj blocks block) :=
    semidirectMulAction field haction
  let hinner : ∀ h : H,
      (SemidirectProduct.inl h : H ⋊[field] E) • psi = psi := fun h ↦ by
    rw [semidirect_inl_smul]
    exact FibreTransportSource.inner_fixes_brauerFibre
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) (T := T) h psi
  let eH := canonicalHToEmbeddedEquiv psi hinner
  let iotaEmbedded := iota.alongMulEquiv eH
  ∃ psiEmbedded : IBr iotaEmbedded,
    psiEmbedded.1 = pullbackPrimeRegularAlongEquiv eH psi.1.1 ∧
    Nonempty
      (Representation.Extension.BrauerCharacterExtensionWitness
        roots.iotaAmbient iotaEmbedded psiEmbedded)

/-- Chosen roots together with an actual global character-extension witness. -/
structure ClauseIVAGlobalCharacterExtensionData
    (psi : BrauerFibre iota hinj blocks block) where
  roots : ClauseIVAGlobalRootInput
    iota hinj blocks field blockSource block T psi
  extension : ClauseIVAGlobalExtensionResult
    iota hinj blocks field blockSource block T psi roots

/-- Build the stored global character extension from the protected cyclic
endgame theorem and the explicit coherent-root input. -/
def clauseIVAGlobalCharacterExtensionData_of_cyclicEndgame
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction)
    (psi : BrauerFibre iota hinj blocks block)
    (roots : ClauseIVAGlobalRootInput
      iota hinj blocks field blockSource block T psi) :
    ClauseIVAGlobalCharacterExtensionData
      iota hinj blocks field blockSource block T psi where
  roots := roots
  extension := globalBrauerCharacterExtension_of_cyclicEndgame
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (field := field) (blockSource := blockSource) (block := block) (T := T)
    (quotientInput := canonicalRawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (localReduction := localReduction) endgame psi
    roots.iotaAmbient roots.compatible

/-- The three coherent-root inputs needed for the local character extension.
They are narrowly typed E2/U inputs and use only the canonical normaliser
quotient. -/
structure ClauseIVBLocalRootInput
    (w : LiteralWeightFibre blockSource block) where
  iotaQuotient :
    letI : (EmbeddedRadical field blockSource block
        (canonicalRawNormalizerQuotientInput
          (p := p) (K := K) (H := H)) w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        (canonicalRawNormalizerQuotientInput
          (p := p) (K := K) (H := H)) w
    PrimeRegularRootEmbedding p k K
      (PairStabilizer field blockSource block w ⧸
        EmbeddedRadical field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w)
  iotaPair : PrimeRegularRootEmbedding p k K
    (PairStabilizer field blockSource block w)
  iotaEmbeddedLocal : PrimeRegularRootEmbedding p k K
    (EmbeddedPairHStabilizer field blockSource block w)
  quotientCompatible :
    letI : (EmbeddedRadical field blockSource block
        (canonicalRawNormalizerQuotientInput
          (p := p) (K := K) (H := H)) w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        (canonicalRawNormalizerQuotientInput
          (p := p) (K := K) (H := H)) w
    ∀ (W : FDRep k (LocalBase field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w))
      (extension : Representation.Extension
        (LocalBase field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w) W.ρ),
      Representation.BrauerRootLiftCompatibleAlong
        extension.representation iotaQuotient
        (transportedLocalRootEmbedding field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w (localReduction w))
        (LocalBase field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w).subtype
  pairInflationCompatible :
    letI : (EmbeddedRadical field blockSource block
        (canonicalRawNormalizerQuotientInput
          (p := p) (K := K) (H := H)) w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        (canonicalRawNormalizerQuotientInput
          (p := p) (K := K) (H := H)) w
    ∀ (W : FDRep k (LocalBase field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w))
      (extension : Representation.Extension
        (LocalBase field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w) W.ρ),
      Representation.BrauerRootLiftCompatibleAlong
        extension.representation iotaQuotient iotaPair
        (QuotientGroup.mk' (EmbeddedRadical field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w))
  localInflationCompatible :
    letI : (EmbeddedRadical field blockSource block
        (canonicalRawNormalizerQuotientInput
          (p := p) (K := K) (H := H)) w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        (canonicalRawNormalizerQuotientInput
          (p := p) (K := K) (H := H)) w
    ∀ W : FDRep k (LocalBase field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w),
      Representation.BrauerRootLiftCompatibleAlong W.ρ
        (transportedLocalRootEmbedding field blockSource block
          (canonicalRawNormalizerQuotientInput
            (p := p) (K := K) (H := H)) w (localReduction w))
        iotaEmbeddedLocal
        (subgroupToQuotientImage
          (EmbeddedRadical field blockSource block
            (canonicalRawNormalizerQuotientInput
              (p := p) (K := K) (H := H)) w)
          (EmbeddedPairHStabilizer field blockSource block w))

/-- The nonconditional local character-extension result for fixed coherent
roots. -/
def ClauseIVBLocalExtensionResult
    (w : LiteralWeightFibre blockSource block)
    (roots : ClauseIVBLocalRootInput
      (field := field) (blockSource := blockSource) (block := block)
      (localReduction := localReduction) w) : Prop :=
  letI : (EmbeddedRadical field blockSource block
      (canonicalRawNormalizerQuotientInput
        (p := p) (K := K) (H := H)) w).Normal :=
    embeddedRadical_normal
      (phi := field) (blockSource := blockSource) (block := block)
      (canonicalRawNormalizerQuotientInput
        (p := p) (K := K) (H := H)) w
  ∃ quotientWitness :
          Representation.Extension.BrauerCharacterExtensionWitness
            roots.iotaQuotient
            (transportedLocalRootEmbedding field blockSource block
              (canonicalRawNormalizerQuotientInput
                (p := p) (K := K) (H := H)) w (localReduction w))
            (transportedLocalBrauer field blockSource block
              (canonicalRawNormalizerQuotientInput
                (p := p) (K := K) (H := H)) w (localReduction w)),
        ∃ inflatedLocal : IBr roots.iotaEmbeddedLocal,
          ∃ pairWitness :
              Representation.Extension.BrauerCharacterExtensionWitness
                roots.iotaPair roots.iotaEmbeddedLocal inflatedLocal,
            (IrreducibleBrauerCharacter.alongMulEquiv roots.iotaEmbeddedLocal
                (embeddedPairHStabilizerEquivNormalizer
                  field blockSource block w) inflatedLocal).1 =
              PrimeRegularClassFunction.pullback
                (selectedNormalizerQuotientHom blockSource block w)
                (localReduction w).brauer.1 ∧
            pairWitness.1.1 =
              PrimeRegularClassFunction.pullback
                (QuotientGroup.mk' (EmbeddedRadical field blockSource block
                  (canonicalRawNormalizerQuotientInput
                    (p := p) (K := K) (H := H)) w))
                quotientWitness.1.1

/-- Chosen coherent roots together with actual quotient and pair-stabiliser
character-extension witnesses. -/
structure ClauseIVBLocalCharacterExtensionData
    (w : LiteralWeightFibre blockSource block) where
  roots : ClauseIVBLocalRootInput
    (field := field) (blockSource := blockSource) (block := block)
    (localReduction := localReduction) w
  extension : ClauseIVBLocalExtensionResult
    (field := field) (blockSource := blockSource) (block := block)
    (localReduction := localReduction) w roots

/-- Build the stored local character extension from the protected theorem and
the explicit coherent-root input. -/
def clauseIVBLocalCharacterExtensionData_of_cyclicEndgame
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction)
    (psi : BrauerFibre iota hinj blocks block)
    (roots : ClauseIVBLocalRootInput
      (field := field) (blockSource := blockSource) (block := block)
      (localReduction := localReduction)
        (endgame.omega.toEquiv psi)) :
    ClauseIVBLocalCharacterExtensionData
      (field := field) (blockSource := blockSource) (block := block)
      (localReduction := localReduction)
        (endgame.omega.toEquiv psi) where
  roots := roots
  extension := localBrauerCharacterExtension_on_normalizer_of_cyclicEndgame
    (field := field) (blockSource := blockSource) (block := block)
    (iota := iota) (hinj := hinj) (blocks := blocks) (T := T)
    (quotientInput := canonicalRawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (localReduction := localReduction) endgame psi
    roots.iotaQuotient roots.iotaPair roots.iotaEmbeddedLocal
    roots.quotientCompatible roots.pairInflationCompatible
    roots.localInflationCompatible

/-- Clause (iv) in the literal self-cover.  Its two character fields are the
protected character-level endpoints, not representation-level proxies. -/
structure ClauseIVHypotheses
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction) where
  orbitRepresentative :
    ∀ psi : BrauerFibre iota hinj blocks block,
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    MulAction.orbit H psi = {psi}
  globalFactorization :
    ∀ psi : BrauerFibre iota hinj blocks block,
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks field block
        T.outerBlock_fixed T.brauerBlock_transport
    let _ : MulAction (H ⋊[field] E)
        (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction field
        (FibreTransportSource.brauerFibre_compatible
          (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
          (blockSource := blockSource) (block := block) (T := T))
    ∀ g : H ⋊[field] E,
      g ∈ MulAction.stabilizer (H ⋊[field] E) psi ↔
        ∃ h : H, ∃ e : E,
          e ∈ MulAction.stabilizer E psi ∧
            g = SemidirectProduct.inl h * SemidirectProduct.inr e
  globalCharacterExtension : ∀ psi : BrauerFibre iota hinj blocks block,
    ClauseIVAGlobalCharacterExtensionData
      iota hinj blocks field blockSource block T psi
  localFactorization :
    ∀ psi : BrauerFibre iota hinj blocks block,
    let w := endgame.omega.toEquiv psi
    ∀ d : PairStabilizer field blockSource block w,
      ∃ h : EmbeddedPairHStabilizer field blockSource block w,
        ∃ x : PairStabilizer field blockSource block w,
          (d : H ⋊[field] E) =
            (((h : PairStabilizer field blockSource block w) : H ⋊[field] E) *
              (x : H ⋊[field] E))
  localCharacterExtension : ∀ psi : BrauerFibre iota hinj blocks block,
    ClauseIVBLocalCharacterExtensionData
      (field := field) (blockSource := blockSource) (block := block)
      (localReduction := localReduction)
        (endgame.omega.toEquiv psi)

/-- The four source-shaped hypothesis clauses in the centreless self-cover.
This is only an input package for the cited theorem.  It carries no theorem
application and no BAW-good or iBAW conclusion. -/
structure ExplicitSelfCoverHypotheses
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction) where
  clauseI : ClauseIHypotheses iota hinj blocks field blockSource block
  clauseII : ClauseIIHypotheses iota hinj blocks field blockSource block T
    endgame.omega
  clauseIII : ClauseIIIHypotheses iota hinj blocks field blockSource block T
    operations endgame.omega
  clauseIV : ClauseIVHypotheses iota hinj blocks field blockSource block T
    localReduction endgame

/-- Combine the explicit hypothesis package from the structural source, the
cyclic endgame, and the separately supplied source adapters.  The construction
uses only the canonical normaliser quotient. -/
def explicitSelfCoverHypotheses_of_cyclicEndgame
    (structural : StructuralSource field)
    (operations : ClauseIIISourceOperations
      iota hinj blocks blockSource block)
    (operationAdapters : ClauseIIISelfCoverAdapters
      iota hinj blocks blockSource block operations)
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      localReduction)
    (globalRootInputs : ∀ psi : BrauerFibre iota hinj blocks block,
      ClauseIVAGlobalRootInput
        iota hinj blocks field blockSource block T psi)
    (localRootInputs : ∀ psi : BrauerFibre iota hinj blocks block,
      ClauseIVBLocalRootInput
        (field := field) (blockSource := blockSource) (block := block)
        (localReduction := localReduction)
          (endgame.omega.toEquiv psi)) :
    ExplicitSelfCoverHypotheses iota hinj blocks field blockSource block T
      localReduction operations endgame := by
  let skeleton := selfCoverClauseSkeletonOfCyclicEndgame
    iota hinj blocks field blockSource block T
    (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
    localReduction structural endgame
  refine {
    clauseI := {
      selfCover_normal := skeleton.i_a_normal
      perfect := skeleton.i_a_perfect
      outer_abelian := skeleton.i_a_outer_abelian
      block_invariant := skeleton.i_a_singletonBlock_invariant
      centralizer := skeleton.i_b_centralizer
      embeddedCentre_normal := skeleton.i_b_embeddedCentre_normal
      automorphismQuotient := skeleton.i_b_automorphismQuotient
      globalSelfCoverExtension := skeleton.i_c_brauerIdentityExtension
      localSelfCoverExtension := fun w _hblock ↦
        rawClauseIDSelfCoverExtension (K := K) w }
    clauseII := {
      semidirect_equivariant := endgame.semidirect_equivariant }
    clauseIII := clauseIIIHypotheses_of_cyclicEndgame
      iota hinj blocks field blockSource block T structural.centerless
      operations operationAdapters endgame
    clauseIV := {
      orbitRepresentative := skeleton.iv_orbitRepresentative
      globalFactorization := skeleton.iv_a_globalFactorization
      globalCharacterExtension := fun psi ↦
        clauseIVAGlobalCharacterExtensionData_of_cyclicEndgame
          iota hinj blocks field blockSource block T localReduction
          endgame psi (globalRootInputs psi)
      localFactorization := skeleton.iv_b_localFactorization
      localCharacterExtension := fun psi ↦
        clauseIVBLocalCharacterExtensionData_of_cyclicEndgame
          iota hinj blocks field blockSource block T localReduction
          endgame psi (localRootInputs psi) }
  }

end SourceClausePackage

end ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverExplicitHypotheses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
