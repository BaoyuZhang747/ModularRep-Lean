import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import ModularRep.PaperProofs.EvenFieldFLZSourceConditions
import ModularRep.PaperProofs.SporadicFi24GlobalEquivToSectorInput
import ModularRep.PaperProofs.SporadicFi24P3PlusRankSourceFacingComposite

/-!
# A moving window for Späth, Lemma 6.1, in the `Fi'_{24}` application

Späth, *A reduction theorem for the blockwise Alperin weight conjecture*,
Lemma 6.1, assumes that the simple group is AWC-good, assumes the block
induction clause in Definition 4.1(ii)(3), and proves the extension and
intermediate-block clauses in Definition 4.1(iii) for a Brauer character
whose outer stabiliser is cyclic.  Its final sentence applies this to every
Brauer character when the full outer automorphism quotient is cyclic.

This file records precisely that moving window.  The full modular
character-triple clause from An--Dietrich, Definition 4.4(3), is an explicit
input to `AWCGoodDefinition44Witness`; it is not a conclusion of Lemma 6.1.
Literal block induction is a separate input.  The only fields returned by
the published-theorem certificate are compatible extensions and the
intermediate block equalities.

The three relations needed by the older sector API are fixed together in
`SpathLemma61Semantics`.  This is an interpretation index, not evidence for
any of its propositions.  `SpathLemma61PublishedCertificate` is the single
E2/source boundary: its implication has exactly the hypotheses and the
Definition 4.1(iii) conclusion used from the published lemma.  In
particular it has no BAW/iBAW field and cannot manufacture the character
triple clause.

The final adapter invokes the plus-rank source-facing Fischer endpoint.
Lean derives cyclicity of the literal outer quotient from its proved
cardinality two and constructs the central-sector input.  It deliberately
returns a function waiting for the still-external, full Definition 4.4(3)
witness.  Thus neither an arbitrary target predicate nor the downstream
`SpathLemma61Input` is accepted as a premise.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3SpathLemma61MovingWindow

open Formalisation
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24GlobalEquivToSectorInput
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
open ModularRep.PaperProofs.SporadicFi24P3BlockIndexBindingFromCardinality
open ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus
open ModularRep.PaperProofs.SporadicFi24P3PlusRankLiteralBridge
open ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract
open ModularRep.PaperProofs.SporadicFi24P3PlusRankSourceFacingComposite
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources
open ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

omit [Fintype X] in
/-- Conjugation preserves the range of the literal inner-automorphism map. -/
private theorem innerInverseOpRange_normal :
    (RepresentationWeight.innerInverseOpHom (G := X)).range.Normal := by
  constructor
  intro beta hbeta alpha
  rcases hbeta with ⟨x, rfl⟩
  refine ⟨(alpha.unop⁻¹) x, ?_⟩
  apply MulOpposite.unop_injective
  ext y
  simp [RepresentationWeight.innerInverseOpHom, mul_assoc]

local instance innerInverseOpRangeNormal :
    (RepresentationWeight.innerInverseOpHom (G := X)).range.Normal :=
  innerInverseOpRange_normal

noncomputable local instance mulAutFinite : Finite (MulAut X) :=
  Finite.of_injective (fun alpha : MulAut X ↦ (alpha : X → X))
    DFunLike.coe_injective

noncomputable local instance mulAutOpFinite : Finite (MulAut X)ᵐᵒᵖ :=
  Finite.of_equiv (MulAut X) MulOpposite.opEquiv

noncomputable local instance literalOuterQuotientFinite :
    Finite
      ((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range) :=
  Finite.of_surjective
    (QuotientGroup.mk'
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (QuotientGroup.mk'_surjective
      (RepresentationWeight.innerInverseOpHom (G := X)).range)

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R :
  LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-! ## The fixed interpretation and the exact published implication -/

/-- One fixed interpretation of the three source-level relations occurring
at the Lemma 6.1 window.  This structure contains no proof that any matched
pair satisfies any of the relations. -/
structure SpathLemma61Semantics where
  modularCharacterTriple :
    IBr iota → WeightClass (p := 3) (K := K) (X := X) → Prop
  intermediateBlockEqualities :
    IBr iota → WeightClass (p := 3) (K := K) (X := X) → Prop
  compatibleExtensions :
    IBr iota → WeightClass (p := 3) (K := K) (X := X) → Prop

/-- The full An--Dietrich Definition 4.4(3) contribution which Lemma 6.1
requires upstream.  The concrete bijection and its equivariance are separate
arguments of the published implication below.  Lemma 6.1 does not prove this
field. -/
structure AWCGoodDefinition44Witness
    (Semantics : SpathLemma61Semantics iota)
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)) where
  definition44Part3 : ∀ phi,
    Semantics.modularCharacterTriple phi (Omega phi)

/-- Späth, Definition 4.1(ii)(3), on the literal global map.  It remains
separate from AWC-goodness, exactly as in Lemma 6.1. -/
structure Definition41II3BlockInductionWitness
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)) where
  blockInduction : ∀ phi,
    R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi

/-- Exactly the two clauses contributed by Lemma 6.1 for one matched pair.
The full character-triple clause is intentionally absent. -/
structure SpathLemma61ConditionIIIAt
    (Semantics : SpathLemma61Semantics iota)
    (phi : IBr iota)
    (weight : WeightClass (p := 3) (K := K) (X := X)) : Prop where
  intermediateBlockEqualities :
    Semantics.intermediateBlockEqualities phi weight
  compatibleExtensions :
    Semantics.compatibleExtensions phi weight

/-- The literal outer automorphism quotient used in the Fischer endpoint.
For an exact universal prime-to-three cover this is the concrete analogue of
the quotient `Aut(S) / S` in the final sentence of Späth, Lemma 6.1. -/
abbrev LiteralOuterQuotient (X : Type u) [Group X] :=
  (MulAut X)ᵐᵒᵖ ⧸
    (RepresentationWeight.innerInverseOpHom (G := X)).range

/-- The sole E2/source-theorem boundary.  The exact universal cover is an
index.  The implication requires a fixed equivariant AWC-good bijection,
its already concrete Definition 4.4(3) witnesses, the independent block
induction clause, and cyclicity of the full outer quotient.  Its output is
only Definition 4.1(iii), pointwise on the same bijection. -/
structure SpathLemma61PublishedCertificate
    (Cover : EllPrimeCoverSource 3 X)
    (Semantics : SpathLemma61Semantics iota) where
  conditionIII_of_cyclicOuter :
    ∀ (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) →
      AWCGoodDefinition44Witness iota Semantics Omega →
      Definition41II3BlockInductionWitness (R := R)
        iota hinj blocks Omega →
      IsCyclic (LiteralOuterQuotient X) →
      ∀ phi, SpathLemma61ConditionIIIAt iota Semantics phi (Omega phi)

/-! ## Kernel construction after applying the cited lemma -/

/-- Build the exact central-sector input to which the older Fischer
construction API applies.  All three fields are obtained from the same global
map; the character-triple field is copied only from the explicit upstream
Definition 4.4(3) witness. -/
def anDietrichSectorInput
    {Semantics : SpathLemma61Semantics iota}
    {Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)}
    (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi)
    (AWC : AWCGoodDefinition44Witness iota Semantics Omega)
    (BlockInduction :
      Definition41II3BlockInductionWitness (R := R)
        iota hinj blocks Omega) :
    AnDietrichSectorInput iota hinj blocks E1
      Semantics.modularCharacterTriple :=
  anDietrichSectorInput_ofGlobalEquiv iota hinj blocks E1
    Semantics.modularCharacterTriple Omega hOmega
      BlockInduction.blockInduction AWC.definition44Part3

/-- Apply the published moving-window certificate pointwise and repackage
its two outputs in the existing sector-shaped `SpathLemma61Input`.  This is
a kernel-only change of indexing from the global map to its central-sector
restrictions. -/
theorem spathLemma61Input_of_publishedCertificate
    {Semantics : SpathLemma61Semantics iota}
    (Cover : EllPrimeCoverSource 3 X)
    (Published : SpathLemma61PublishedCertificate (R := R)
      iota hinj blocks Cover Semantics)
    {Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)}
    (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi)
    (AWC : AWCGoodDefinition44Witness iota Semantics Omega)
    (BlockInduction :
      Definition41II3BlockInductionWitness (R := R)
        iota hinj blocks Omega)
    (hcyclic : IsCyclic (LiteralOuterQuotient X)) :
    SpathLemma61Input iota hinj blocks E1
      Semantics.intermediateBlockEqualities
      Semantics.compatibleExtensions
      Semantics.modularCharacterTriple
      (anDietrichSectorInput iota hinj blocks E1 hOmega AWC
        BlockInduction) where
  intermediateBlockEqualities _sector phi := by
    change Semantics.intermediateBlockEqualities phi.1 (Omega phi.1)
    exact (Published.conditionIII_of_cyclicOuter Omega hOmega AWC
      BlockInduction hcyclic phi.1).intermediateBlockEqualities
  compatibleExtensions _sector phi := by
    change Semantics.compatibleExtensions phi.1 (Omega phi.1)
    exact (Published.conditionIII_of_cyclicOuter Omega hOmega AWC
      BlockInduction hcyclic phi.1).compatibleExtensions

/-- A quotient of cardinality two is cyclic.  This is the only group-theory
step needed to turn the plus-rank endpoint's literal outer-order computation
into the cyclic hypothesis of the published moving window. -/
theorem literalOuterQuotient_isCyclic_of_card_two
    (hcard : Nat.card (LiteralOuterQuotient X) = 2) :
    IsCyclic (LiteralOuterQuotient X) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCyclic_of_prime_card hcard

/-! ## The `Fi'_{24}`, `p = 3`, plus-rank adapter -/

variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]

/-- Invoke the compiled plus-rank Fischer endpoint and expose the exact
remaining Lemma 6.1 boundary.

The endpoint supplies `Omega`, full automorphism equivariance, literal block
induction, and `Q = 1` normalisation.  Its order-two computation supplies
cyclicity of the literal outer quotient.  Applying the final function still
requires an `AWCGoodDefinition44Witness`, whose sole field is precisely the
missing full An--Dietrich Definition 4.4(3) evidence.  Once that evidence is
given, the cited `Published` certificate supplies—and only supplies—the two
Definition 4.1(iii) fields in `SpathLemma61Input`. -/
theorem exists_plusRankOmega_with_spathLemma61_movingWindow
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (E1 : RoutineTransportInput iota hinj blocks R)
    (Cover : EllPrimeCoverSource 3 X)
    (Semantics : SpathLemma61Semantics iota)
    (Published :
      SpathLemma61PublishedCertificate (R := R)
        iota hinj blocks Cover Semantics)
    (AD : AnDietrichFi24P3SourceCertificate
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight))
    (Bridge : AnDietrichFi24P3LiteralCarrierBridge
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)
    (hCenter : Subgroup.center X = ⊥)
    (Involution : SelectedOuterInvolutionCarrier X)
    (BlockInjection : Fi24P3BlockIndexInjectionSource BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockInjection.toBlockIndexBinding)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (DefectZeroCompatibility :
      TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (DefectZeroBlocks : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (DefectZeroSubgroups :
      DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (DefectZeroIdentification :
      Fi24DefectZeroBlockIdentification iota hinj blocks D
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction))
    (RestrictionBinding :
      BrauerRestrictionSpaceBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction))
    (Replay : Fi24P3PlusRankReplaySource K)
    (LiteralBinding :
      Fi24P3PlusRankLiteralBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        RestrictionBinding Replay)
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (TableBlockMatch : Fi24P3NamedTableIntervalCentralCharacterMatch
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding
            BlockAction).nonprincipalBlock
        Q table)
    (LocalCensus : Fi24P3LocalDefectZeroCensusBinding R Q table)
    (RadicalSupport : Fi24P3NonprincipalRadicalSupportSource
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        Q table)
    (WeightActionAlignment :
      Fi24P3NonprincipalTable8ActionAlignment
        R
          (fi24ThreeBlockSourceOfBindings
            blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
          Q table S414 TableBlockMatch
          (nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
            R
              (fi24ThreeBlockSourceOfBindings
                blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
              Q table LocalCensus RadicalSupport))
    (hOuterQuotientCard :
      Nat.card (LiteralOuterQuotient X) = 2) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      ∃ hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi,
      ∃ hblock : ∀ phi,
        R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi,
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        Omega (D.reduce (iota := iota) d) = T.atOne d) ∧
      (∀ AWC : AWCGoodDefinition44Witness iota Semantics Omega,
        Nonempty (SpathLemma61Input iota hinj blocks E1
          Semantics.intermediateBlockEqualities
          Semantics.compatibleExtensions
          Semantics.modularCharacterTriple
          (anDietrichSectorInput iota hinj blocks E1 hOmega AWC
            { blockInduction := hblock }))) := by
  obtain ⟨Omega, hOmega, hblock, hqOne⟩ :=
    exists_blockPreservingAutEquivariantEquiv_with_qOne_from_plus_rank_sources
      (R := R) iota hinj blocks E1 AD Bridge hCenter Involution
        BlockInjection BlockAction D T DefectZeroCompatibility
        DefectZeroBlocks DefectZeroSubgroups DefectZeroIdentification
        RestrictionBinding Replay LiteralBinding Q table S414
        TableBlockMatch LocalCensus RadicalSupport WeightActionAlignment
        hOuterQuotientCard
  refine ⟨Omega, hOmega, hblock, hqOne, ?_⟩
  intro AWC
  let BlockInduction :
      Definition41II3BlockInductionWitness (R := R)
        iota hinj blocks Omega :=
    { blockInduction := hblock }
  exact ⟨spathLemma61Input_of_publishedCertificate
    iota hinj blocks E1 Cover Published hOmega AWC BlockInduction
      (literalOuterQuotient_isCyclic_of_card_two hOuterQuotientCard)⟩

end ModularRep.PaperProofs.SporadicFi24P3SpathLemma61MovingWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
