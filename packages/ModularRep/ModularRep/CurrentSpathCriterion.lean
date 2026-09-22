import ModularRep.PaperProofs.CurrentCyclicOuterBAW
import ModularRep.PaperProofs.OddTwoActualStabilizerTriple

/-!
# Current Theorem 2.3: the two sides of Spath's Theorem 4.4

The published theorem is an explicit E2 source, not reproved here. Its
two sides are fixed mathematical carriers: the four extension/block
conditions on the full central character quotient, and the actual modular
block-triple relation on the same quotient character and own ordinary
weight. In particular the right side includes containment of the WHOLE
raw-pair stabilizer in the global character stabilizer. An intersection
alone is not the published condition.

The lower E1/U data record the full universal cover, literal block
identifications, ordinary descent, root agreement, and the lift of the
downstairs automorphisms. They contain neither side of the equivalence.
The coefficient field of ordinary character values is algebraically closed;
the residue field and all finite groups retain the scope of the existing
literal sets of Brauer characters.

Source: B. Spath, *Inductive conditions for counting conjectures via
character triples* (2017), Theorem 4.4, p. 678,
https://doi.org/10.4171/171-1/23.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.CurrentSpathCriterion

open Formalisation ModularRep CharacterWeight FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.CurrentCyclicOuterBAW
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

open ModularRep.PaperProofs

universe u

/-- The full cover is independent of the characteristic. In particular its
centre is not assumed to have order prime to `P.p`. -/
structure FullCover (P : Definition35Problem.{u}) where
  S : Type u
  [groupS : Group S]
  [finiteS : Finite S]
  simple : IsSimpleGroup S
  nonabelian : ¬ IsMulCommutative S
  projection : P.H →* S
  universal : IsUniversalCentralExtension projection
  kernel_center : projection.ker = Subgroup.center P.H

attribute [instance] FullCover.groupS FullCover.finiteS

/-- Fixed lower quotient data. The reference is exactly `psi`, so the
kernel is the full central character kernel, including its central
`p`-part. No ambient extension or triple relation is part of this data. -/
structure PairData (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) (w : Definition35Weight P) where
  quotient : CentralQuotientBrauerSource P psi psi
  weight : QuotientWeightBrauerSource P psi w
  localInflation : QuotientLocalInflationSource P psi w weight
  quotient_roots : RootAgreement quotient.iota P.iota
  weight_roots : RootAgreement weight.iota quotient.iota
  inflation_roots : RootAgreement localInflation.iota quotient.iota
  original_weight_roots : RootAgreement (P.localReduction w).iota P.iota

variable {P : Definition35Problem.{u}} {psi : Definition35Brauer P}
  {w : Definition35Weight P}

local instance quotientFintype : Fintype (CentralCharacterQuotient P psi) :=
  Fintype.ofFinite _

/-- The ordinary character in the right-hand triple is constructed from
the SAME descended defect-zero character in the fixed pair data. -/
def PairData.rawWeight (D : PairData P psi w) :
    CharacterWeight P.p P.K (CentralCharacterQuotient P psi) where
  prime := P.iota.prime
  subgroup := quotientRadical P psi w
  radical := D.weight.radical
  localCharacter := D.weight.ordinary
  defectZero := D.weight.defectZero

/-- Reduction and inflation are composed on actual prime regular elements. -/
def PairData.ownReduction (D : PairData P psi w) :
    OddTwoActualStabilizerTriple.OwnNormalizerReduction (k := P.k) D.rawWeight where
  root := D.localInflation.iota
  brauer := D.localInflation.brauer
  own_reduction := by
    intro g
    let q := QuotientGroup.mk'
      ((quotientRadical P psi w).subgroupOf
        (Subgroup.normalizer (quotientRadical P psi w :
          Set (CentralCharacterQuotient P psi))))
    exact (D.weight.reduction (PrimeRegularElement.map q g)).trans
      (congrArg (fun f : PrimeRegularClassFunction P.K
        (Subgroup.normalizer (quotientRadical P psi w :
          Set (CentralCharacterQuotient P psi))) P.p => f g)
        D.localInflation.inflation)

abbrev PairData.action (_D : PairData P psi w) :
    MulAut (CentralCharacterQuotient P psi) →*
      MulAut (CentralCharacterQuotient P psi) := MonoidHom.id _

abbrev PairData.Semidirect (D : PairData P psi w) :=
  (CentralCharacterQuotient P psi) ⋊[D.action]
    MulAut (CentralCharacterQuotient P psi)

/-- Lower source identifications for the original hatted pair and its
literal blocks. `normalizerInertia` authenticates the full hatted
normalizer/ordinary-character stabilizer, not an intersection with the
global stabilizer. Its inverse is the existing right-action convention. -/
structure HattedPairJoins (D : PairData P psi w) where
  hattedReduction : OddTwoActualStabilizerTriple.OwnNormalizerReduction (k := P.k)
    (selectedCharacterWeight P.blockSource P.block w)
  hatted_roots : RootAgreement hattedReduction.root P.iota
  hattedInjective : IrreducibleBrauerCharacterInjectivity hattedReduction.root
  ambient_idempotents : ∀ b : P.Block,
    P.blockSource.operations.ambientBlockData.blockIdempotent b =
      P.blockIdempotent b
  local_block :
    let W := selectedCharacterWeight P.blockSource P.block w
    let O := P.blockSource.operations
    let localData := O.inflatedNormalizerBlockData W.subgroup
    letI := localData.fintypeBlock
    irreducibleBrauerCharacterBlock hattedReduction.root hattedInjective
        localData.blocks hattedReduction.brauer =
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)
  local_descent : PrimeRegularClassFunction.pullback
      (normalizerMap (centralCharacterQuotientMap P psi) (selectedRadical P w))
      D.localInflation.brauer.1 = hattedReduction.brauer.1
  normalizer_surjective : Function.Surjective
    (normalizerMap (centralCharacterQuotientMap P psi) (selectedRadical P w))
  liftAutomorphism : MulAut (CentralCharacterQuotient P psi) →* MulAut P.H
  lift_natural : ∀ (a : MulAut (CentralCharacterQuotient P psi)) (x : P.H),
    centralCharacterQuotientMap P psi (liftAutomorphism a x) =
      a (centralCharacterQuotientMap P psi x)
  normalizerInertia : ∀ a : D.Semidirect,
    a ∈ OddTwoActualStabilizerTriple.rawStabilizer D.action D.rawWeight ↔
      ∃ localActor : MulAut (Subgroup.normalizer (selectedRadical P w : Set P.H)),
        (∀ x, (localActor x).val =
          liftAutomorphism ((MulAut.conj a.left * a.right)⁻¹) x.val) ∧
        ∀ x, (selectedCharacterWeight P.blockSource P.block w).localCharacter
            (QuotientGroup.mk (localActor x)) =
          (selectedCharacterWeight P.blockSource P.block w).localCharacter
            (QuotientGroup.mk x)

/-- The four conditions in the proof of Theorem 4.4, at fixed quotient
and own local character. Every intermediate subgroup is quantified. -/
structure ClauseIII (D : PairData P psi w) where
  ambient : SpathAmbientGroup P psi psi D.quotient
  extensions : SpathCharacterExtensions P psi psi w D.quotient D.weight
    D.localInflation ambient
  intermediateBlocks : IntermediateBlockSource P psi psi w D.quotient
    D.weight D.localInflation ambient extensions
  quotientAmbient_roots : RootAgreement D.quotient.iota extensions.ambientRoot
  inflationAmbient_roots : RootAgreement D.localInflation.iota extensions.localAmbientRoot
  localAmbient_roots : RootAgreement extensions.localAmbientRoot extensions.ambientRoot
  intermediate_roots : ∀ (J : Subgroup ambient.A) (hJ : ambient.base ≤ J),
    RootAgreement (intermediateBlocks.equalityAt J hJ).globalRoot
        extensions.ambientRoot ∧
      RootAgreement (intermediateBlocks.equalityAt J hJ).localRoot
        extensions.ambientRoot

/-- The existing concrete Spath carrier is recovered without changing any
quotient, ordinary weight, root, extension, or intermediate block. -/
def ClauseIII.coherentMatched {D : PairData P psi w} (c : ClauseIII D) :
    CoherentMatchedCondition P psi w where
  condition := { quotient := D.quotient, tail :=
    { weight := D.weight, localInflation := D.localInflation,
      ambient := c.ambient, extensions := c.extensions,
      intermediateBlocks := c.intermediateBlocks } }
  quotient_roots := D.quotient_roots
  weight_roots := D.weight_roots
  inflation_roots := D.inflation_roots
  quotientAmbient_roots := c.quotientAmbient_roots
  inflationAmbient_roots := c.inflationAmbient_roots
  localAmbient_roots := c.localAmbient_roots
  intermediate_roots := c.intermediate_roots

/-- The tuple is computed from the same quotient and ordinary weight. -/
def PairData.arguments (D : PairData P psi w) : BlockTripleArguments P.p P.k P.K :=
  OddTwoActualStabilizerTriple.arguments D.quotient.iota D.action D.quotient.brauer D.rawWeight D.ownReduction

/-- The WHOLE local stabilizer condition, followed by the literal
block-isomorphism relation. The containment is a conclusion of the forward
published theorem, not an extra premise in `PairData`. -/
structure TripleCondition (D : PairData P psi w)
    (semantics : BlockTripleSourceSemantics P.p P.k P.K) : Prop where
  fullLocal : OddTwoActualStabilizerTriple.rawStabilizer D.action D.rawWeight ≤
    OddTwoActualStabilizerTriple.globalStabilizer D.quotient.iota D.action D.quotient.brauer
  blockIsomorphic : semantics.blockIsomorphic D.arguments

/-- The right side really uses the whole local group. -/
def TripleCondition.fullLocalEquiv {D : PairData P psi w}
    {semantics : BlockTripleSourceSemantics P.p P.k P.K}
    (t : TripleCondition D semantics) :
    OddTwoActualStabilizerTriple.rawStabilizer D.action D.rawWeight ≃*
      OddTwoActualStabilizerTriple.localSubgroup D.quotient.iota D.action D.quotient.brauer D.rawWeight :=
  OddTwoActualStabilizerTriple.fullRawStabilizerEquiv D.quotient.iota D.action D.quotient.brauer
    D.rawWeight t.fullLocal

/-- Exact uniform E2 interpretation of Spath 2017, Theorem 4.4. Neither
side is a free predicate: only the usual U meaning of block-isomorphic
ACTUAL modular triples is supplied by `semantics`. Algebraic closure of
the ordinary value field supplies the splitting scope of the published
ordinary characters and all extension root systems. -/
structure Theorem44Source (P : Definition35Problem.{u})
    (semantics : BlockTripleSourceSemantics P.p P.k P.K) : Prop where
  equivalence : ∀ [IsAlgClosed P.K] (cover : FullCover P)
      (psi : Definition35Brauer P) (w : Definition35Weight P)
      (D : PairData P psi w) (joins : HattedPairJoins D)
      (fieldScope : SpathCoefficientField P.p P.k P.iota.prime),
    Nonempty (ClauseIII D) ↔ TripleCondition D semantics

theorem current_theorem_2_3 [IsAlgClosed P.K]
    (semantics : BlockTripleSourceSemantics P.p P.k P.K)
    (source : Theorem44Source P semantics) (cover : FullCover P)
    (D : PairData P psi w) (joins : HattedPairJoins D)
    (fieldScope : SpathCoefficientField P.p P.k P.iota.prime) :
    Nonempty (ClauseIII D) ↔ TripleCondition D semantics :=
  source.equivalence cover psi w D joins fieldScope

theorem clauseIII_to_actual_triples [IsAlgClosed P.K]
    (semantics : BlockTripleSourceSemantics P.p P.k P.K)
    (source : Theorem44Source P semantics) (cover : FullCover P)
    (D : PairData P psi w) (joins : HattedPairJoins D)
    (fieldScope : SpathCoefficientField P.p P.k P.iota.prime) (c : ClauseIII D) :
    TripleCondition D semantics :=
  (current_theorem_2_3 semantics source cover D joins fieldScope).mp ⟨c⟩

theorem actual_triples_to_clauseIII [IsAlgClosed P.K]
    (semantics : BlockTripleSourceSemantics P.p P.k P.K)
    (source : Theorem44Source P semantics) (cover : FullCover P)
    (D : PairData P psi w) (joins : HattedPairJoins D)
    (fieldScope : SpathCoefficientField P.p P.k P.iota.prime)
    (t : TripleCondition D semantics) : Nonempty (ClauseIII D) :=
  (current_theorem_2_3 semantics source cover D joins fieldScope).mpr t

end ModularRep.CurrentSpathCriterion


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
