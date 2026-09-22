import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate

/-!
# Current Lemma 2.10: the BAW-good conclusion of the cyclic criterion

Feng--Li--Zhang, *Jordan decomposition for weights and the blockwise
Alperin weight conjecture*, Theorem 3.18, concludes BAW-goodness.  The older fixed
gate retains only its Definition 3.5 consequence.  This additive interface
uses the very same canonical construction of the theorem's hypotheses and
exposes its actual, stronger, fixed codomain.

The theorem source below is E2, and the interpretation of the published
BAW matched-pair relation is U.  Neither is constructed here.  The root
extension inputs, coefficient conventions, structural source and singleton
block are unchanged.  No implication from an iBAW bijection to BAW-goodness
is assumed or proved.  The separate forward passage retains the same map.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CurrentCyclicOuterBAW

open ModularRep Formalisation
open ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverExplicitHypotheses
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

universe u

/-- Agreement on precisely the finite root domain used by the first group. -/
def RootAgreement {ell : ℕ} {k K H A : Type u}
    [Field k] [Field K] [Group H] [Finite H] [Group A] [Finite A]
    (r : PrimeRegularRootEmbedding ell k K H)
    (s : PrimeRegularRootEmbedding ell k K A) : Prop :=
  ∀ z : rootsOfUnity (primeRegularExponent ell H) k,
    r.lift (((z : kˣ) : k)) = s.lift (((z : kˣ) : k))

/-- A concrete matched packet with common coefficient conventions on every
quotient, local inflation, ambient extension and intermediate restriction.
This is output data; no instance is assumed for a desired matching. -/
structure CoherentMatchedCondition (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) (weight : Definition35Weight P) where
  condition : SpathMatchedBlockCondition P psi psi weight
  quotient_roots : RootAgreement condition.quotient.iota P.iota
  weight_roots : RootAgreement condition.weight.iota condition.quotient.iota
  inflation_roots : RootAgreement condition.localInflation.iota condition.quotient.iota
  quotientAmbient_roots : RootAgreement condition.quotient.iota
    condition.extensions.ambientRoot
  inflationAmbient_roots : RootAgreement condition.localInflation.iota
    condition.extensions.localAmbientRoot
  localAmbient_roots : RootAgreement condition.extensions.localAmbientRoot
    condition.extensions.ambientRoot
  intermediate_roots : ∀ (J : Subgroup condition.ambient.A)
      (hJ : condition.ambient.base ≤ J),
    RootAgreement (condition.intermediateBlocks.equalityAt J hJ).globalRoot
        condition.extensions.ambientRoot ∧
      RootAgreement (condition.intermediateBlocks.equalityAt J hJ).localRoot
        condition.extensions.ambientRoot

/-- Universal U authentication of the source relation against actual
central-quotient, corresponding weight reduction, ambient group, extension and
intermediate block-induction data.  This is an equivalence of meanings for
every pair; it supplies no matched pair and no proof of either relation. -/
structure BAWGoodRelationIdentification
    {P : Definition35Problem.{u}}
    {automorphisms : Definition35AutomorphismStabilizerAdapter P}
    {cover : EllPrimeCoverSource P.p P.H}
    (relation : FLZBAWGoodRelation P automorphisms cover) : Prop where
  relation_iff : ∀ (psi : Definition35Brauer P) (weight : Definition35Weight P),
    relation.bawGoodBlockIsomorphic psi weight ↔
      Nonempty (CoherentMatchedCondition P psi weight)

/-- Decoding a BAW-good witness supplies the actual extension and block data
for the SAME matched weight under coherent coefficient conventions. -/
theorem coherentMatched_of_bawGood
    {P : Definition35Problem.{u}}
    {automorphisms : Definition35AutomorphismStabilizerAdapter P}
    {cover : EllPrimeCoverSource P.p P.H}
    {relation : FLZBAWGoodRelation P automorphisms cover}
    (identification : BAWGoodRelationIdentification relation)
    (good : FLZBAWGoodBlockWitness P automorphisms cover relation)
    (psi : Definition35Brauer P) :
    Nonempty (CoherentMatchedCondition P psi (good.omega psi)) :=
  (identification.relation_iff psi (good.omega psi)).mp (good.blockIsomorphism psi)

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι] {blockIdempotent : ι → k[H]}
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
variable (structural : StructuralSource field)
variable (endgame : CyclicEndgameData
  (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
  (blockSource := blockSource) (block := block) T
  (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
  localReduction)
variable (identification : SelfCoverSourceIdentification (p := p) (H := H))

local notation "P" => SelfCoverProblem iota hinj blocks field blockSource block T localReduction
local notation "Aut" => SelfCoverAutomorphisms iota hinj blocks field blockSource block T
  localReduction structural

/-- The exact E2 conclusion of Theorem 3.18 on the centreless self-cover.
The source owns the clause-(iii) operations and adapters; its argument is
the canonical completed package, not an opaque assertion of all clauses.
The fixed cover is the cover in the same simple-group identification. -/
structure FLZ318BAWGoodSource
    (relation : FLZBAWGoodRelation P Aut identification.ellPrimeCover) where
  relationIdentification : BAWGoodRelationIdentification relation
  operations : ClauseIIISourceOperations iota hinj blocks blockSource block
  operationAdapters : ClauseIIISelfCoverAdapters
    iota hinj blocks blockSource block operations
  applyTheorem318 :
    CompletedExplicitPackage iota hinj blocks field blockSource block T
      localReduction endgame structural operations operationAdapters →
    Nonempty (FLZBAWGoodBlockWitness P Aut identification.ellPrimeCover relation)

/-- Apply the published criterion after the previously proved canonical
cyclic construction.  This is current Lemma 2.10 under its explicit E1/E2/U
coefficient, extension and source-identification inputs. -/
theorem lemma_2_10_bawGood
    (relation : FLZBAWGoodRelation P Aut identification.ellPrimeCover)
    (source : FLZ318BAWGoodSource iota hinj blocks field blockSource block T
      localReduction structural endgame identification relation)
    (globalRootInputs : ∀ psi : BrauerFibre iota hinj blocks block,
      ClauseIVAGlobalRootInput iota hinj blocks field blockSource block T psi)
    (localRootInputs : ∀ psi : BrauerFibre iota hinj blocks block,
      ClauseIVBLocalRootInput
        (field := field) (blockSource := blockSource) (block := block)
        (localReduction := localReduction) (endgame.omega.toEquiv psi)) :
    Nonempty (FLZBAWGoodBlockWitness P Aut identification.ellPrimeCover relation) :=
  source.applyTheorem318
    (completedExplicitPackage_of_cyclicEndgame iota hinj blocks field
      blockSource block T localReduction structural source.operations
      source.operationAdapters endgame globalRootInputs localRootInputs)

section Passage

variable {P₀ : Definition35Problem.{u}}
variable {automorphisms : Definition35AutomorphismStabilizerAdapter P₀}
variable {cover : EllPrimeCoverSource P₀.p P₀.H}
variable (relation : FLZBAWGoodRelation P₀ automorphisms cover)
variable (definition35 : FLZSourceSemantics P₀ automorphisms)

/-- The independently published forward implication following equation
(3.17).  It asserts no relation truth and contains no converse. -/
structure BAWGoodToDefinition35Source : Prop where
  relation_implication : ∀ (psi : Definition35Brauer P₀)
      (weight : Definition35Weight P₀),
    relation.bawGoodBlockIsomorphic psi weight →
      definition35.definition35BlockIsomorphic psi weight

/-- The stronger output supplies the weaker bijection with exactly the
same character-to-weight map and equivariance proof. -/
def toDefinition35
    (passage : BAWGoodToDefinition35Source relation definition35)
    (good : FLZBAWGoodBlockWitness P₀ automorphisms cover relation) :
    Definition35IBAWBijection P₀ automorphisms definition35 where
  omega := good.omega
  equivariant := good.equivariant
  blockIsomorphism psi := passage.relation_implication psi (good.omega psi)
    (good.blockIsomorphism psi)

@[simp] theorem toDefinition35_omega
    (passage : BAWGoodToDefinition35Source relation definition35)
    (good : FLZBAWGoodBlockWitness P₀ automorphisms cover relation) :
    (toDefinition35 relation definition35 passage good).omega = good.omega := rfl

end Passage
end ModularRep.PaperProofs.CurrentCyclicOuterBAW


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
