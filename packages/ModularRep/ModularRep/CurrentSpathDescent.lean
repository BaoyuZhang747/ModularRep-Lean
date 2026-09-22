import ModularRep.PaperProofs.CurrentCyclicOuterBAW
import ModularRep.PaperProofs.OddTwoActualStabilizerTriple
import ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily

/-!
# Current Corollary 2.5: descent from the prime-to-p cover to the simple group

This additive source interface separates the FULL universal central cover
from its quotient by the central p-core, which is the universal prime-to-p
cover. No full-universal property is asserted for the latter. The exact
E2 source is Spath 2013, Proposition 4.6 with r=1, followed by the forward
character-triple passage in Spath 2017, Theorem 4.4. It returns fixed
literal character/weight bijections and coherent extension/block packets.

The lower dictionaries name the actual maps, common roots, hatted Brauer
inflation, dominated blocks and own ordinary weight inflations. They do
not contain a matching or a character-triple conclusion. The same-map
passage to any authenticated Definition 3.5 semantics is proved below.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.CurrentSpathDescent

open Formalisation ModularRep CharacterWeight FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.CurrentCyclicOuterBAW
open ModularRep.PaperProofs
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

/-- Actual full-cover / prime-to-p-cover diagram of one simple group. -/
structure FullCoverPrimeToDiagram {p : ℕ} (family : Definition35Family.{u} p)
    (cover : EllPrimeCoverSource p family.H) where
  Hhat : Type u
  [groupHhat : Group Hhat]
  [fintypeHhat : Fintype Hhat]
  fullProjection : Hhat →* cover.S
  fullUniversal : IsUniversalCentralExtension fullProjection
  fullKernel : fullProjection.ker = Subgroup.center Hhat
  primeProjection : Hhat →* family.H
  primeSurjective : Function.Surjective primeProjection
  primeKernel : primeProjection.ker = pCore p Hhat
  coreCentral : pCore p Hhat ≤ Subgroup.center Hhat
  triangle : cover.quotient.comp primeProjection = fullProjection
  hattedRoot : PrimeRegularRootEmbedding p family.k family.K Hhat
  roots : RootAgreement family.iota hattedRoot

attribute [instance] FullCoverPrimeToDiagram.groupHhat
  FullCoverPrimeToDiagram.fintypeHhat

/-- The prime-to-p cover is identified by the displayed quotient map. -/
def FullCoverPrimeToDiagram.primeQuotientEquiv {p : ℕ}
    {family : Definition35Family.{u} p} {cover : EllPrimeCoverSource p family.H}
    (D : FullCoverPrimeToDiagram family cover) :
    D.Hhat ⧸ pCore p D.Hhat ≃* family.H :=
  (QuotientGroup.quotientMulEquivOfEq D.primeKernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective D.primeProjection D.primeSurjective)

@[simp] theorem FullCoverPrimeToDiagram.primeQuotientEquiv_mk {p : ℕ}
    {family : Definition35Family.{u} p} {cover : EllPrimeCoverSource p family.H}
    (D : FullCoverPrimeToDiagram family cover) (x : D.Hhat) :
    D.primeQuotientEquiv (QuotientGroup.mk' (pCore p D.Hhat) x) =
      D.primeProjection x := rfl

/-- Explicit E1/U inflation dictionary on the same diagram. The block
families and all character equations are literal; the local ordinary
character of every hatted weight is the inflation of its own input. -/
structure FullCoverInflation {p : ℕ} {family : Definition35Family.{u} p}
    {cover : EllPrimeCoverSource p family.H}
    (D : FullCoverPrimeToDiagram family cover) where
  brauerInflate : IBr family.iota → IBr D.hattedRoot
  brauer_values : ∀ psi : IBr family.iota,
    PrimeRegularClassFunction.pullback D.primeProjection psi.1 =
      (brauerInflate psi).1
  hattedInjective : IrreducibleBrauerCharacterInjectivity D.hattedRoot
  blockIdempotent : family.Block → family.k[D.Hhat]
  blocks : BlockIdempotentDecomposition blockIdempotent
  block_projection : ∀ b : family.Block,
    MonoidAlgebra.mapDomainRingHom family.k D.primeProjection (blockIdempotent b) =
      family.blockIdempotent b
  blockInflation : ∀ psi : IBr family.iota,
    irreducibleBrauerCharacterBlock D.hattedRoot hattedInjective blocks
        (brauerInflate psi) =
      irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks psi
  hattedWeight : CharacterWeight p family.K family.H →
    CharacterWeight p family.K D.Hhat
  hattedSubgroup : ∀ W,
    (hattedWeight W).subgroup = W.subgroup.comap D.primeProjection
  normalizerProjection : ∀ W,
    Subgroup.normalizer ((hattedWeight W).subgroup : Set D.Hhat) →*
      Subgroup.normalizer (W.subgroup : Set family.H)
  normalizer_natural : ∀ W x,
    (normalizerProjection W x).val = D.primeProjection x.val
  normalizer_surjective : ∀ W, Function.Surjective (normalizerProjection W)
  ordinary_inflation : ∀ W x,
    (hattedWeight W).localCharacter (QuotientGroup.mk x) =
      W.localCharacter (QuotientGroup.mk (normalizerProjection W x))

/-- Coefficient identification on the target root domain. Separate fields
may be used by the bundled families, but they represent one coefficient
system throughout the source application. -/
structure Coefficients {p : ℕ} (coverFamily targetFamily : Definition35Family.{u} p) where
  residue : coverFamily.k ≃+* targetFamily.k
  ordinary : coverFamily.K ≃+* targetFamily.K
  roots : ∀ z : rootsOfUnity (primeRegularExponent p targetFamily.H) coverFamily.k,
    ordinary (coverFamily.iota.lift (((z : coverFamily.kˣ) : coverFamily.k))) =
      targetFamily.iota.lift (residue (((z : coverFamily.kˣ) : coverFamily.k)))

/-- Specified block support and selected reductions in the family's own
root convention. The guarded local dictionary does not identify the
ordinary block with reductions at unrelated roots. -/
structure PhysicalFamilySource {p : ℕ} (family : Definition35Family.{u} p) where
  ordinaryRoots : HasEnoughRootsOfUnity family.K (Nat.card family.H)
  idempotents : ∀ b : family.Block,
    family.blockSource.operations.ambientBlockData.blockIdempotent b = family.blockIdempotent b
  localBlocks : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
    family.iota family.blockSource.operations
  selected_roots : ∀ b (w : Definition35Weight (family.problem b)),
    RootAgreement (family.localReduction b w).iota family.iota
  ownReduction : ∀ W : CharacterWeight p family.K family.H,
    OddTwoActualStabilizerTriple.OwnNormalizerReduction (k := family.k) W
  own_roots : ∀ W, RootAgreement (ownReduction W).root family.iota

/-- A fixed target block packet. No relation is supplied as a free
predicate: the finite extension, roots and all intermediate block
equalities of the actual matched pair are the required output. -/
structure CoherentBlockBijection {p : ℕ} (family : Definition35Family.{u} p)
    (block : family.Block) where
  omega : Definition35Brauer (family.problem block) ≃
    Definition35Weight (family.problem block)
  equivariant : Definition35Equivariant (family.problem block) omega
  matched : ∀ psi : Definition35Brauer (family.problem block),
    CoherentMatchedCondition (family.problem block) psi (omega psi)

structure CoherentFamilyBijection {p : ℕ} (family : Definition35Family.{u} p) where
  blockWitness : ∀ block : family.Block, CoherentBlockBijection family block

/-- The source's exact target relation can itself serve as a fixed
Definition 3.5 semantic carrier. Its authentication with the published
Definition 3.5 is supplied separately below. -/
def coherentSemantics {p : ℕ} (family : Definition35Family.{u} p)
    (automorphisms : ∀ b, Definition35AutomorphismStabilizerAdapter (family.problem b))
    (block : family.Block) : FLZSourceSemantics (family.problem block) (automorphisms block) where
  definition35BlockIsomorphic psi w := Nonempty (CoherentMatchedCondition (family.problem block) psi w)

/-- The standard same-raw modular triples, for every representative of
the weight class and every compatible own ordinary reduction. Whole local
stabilizer containment is part of the condition. -/
def LiteralTripleCondition (P : Definition35Problem.{u})
    (standard : BlockTripleSourceSemantics P.p P.k P.K)
    (psi : Definition35Brauer P) (weight : Definition35Weight P) : Prop :=
  ∀ W : CharacterWeight P.p P.K P.H,
    (Quotient.mk'' (Quotient.mk'' W : CharacterWeight.IsoClass) :
      CharacterWeight.ConjugacyClass) = weight.1 →
    ∀ R : OddTwoActualStabilizerTriple.OwnNormalizerReduction (k := P.k) W,
      RootAgreement R.root P.iota →
      OddTwoActualStabilizerTriple.rawStabilizer P.gamma W ≤
          OddTwoActualStabilizerTriple.globalStabilizer P.iota P.gamma psi.1 ∧
        standard.blockIsomorphic
          (OddTwoActualStabilizerTriple.arguments P.iota P.gamma psi.1 W R)

/-- Uniform forward E2 on actual triples and a separate U identification
of Definition 3.5 with those SAME tuples. No direct implication into an
uninterpreted target relation or matched-pair existence is a field. -/
structure CoherentToDefinition35Source {p : ℕ} (family : Definition35Family.{u} p)
    (centerless : Subgroup.center family.H = ⊥)
    (automorphisms : ∀ b, Definition35AutomorphismStabilizerAdapter (family.problem b))
    (standard : BlockTripleSourceSemantics p family.k family.K)
    (semantics : ∀ b, FLZSourceSemantics (family.problem b) (automorphisms b)) : Prop where
  actual_triples : ∀ (b : family.Block)
      (omega : Definition35Brauer (family.problem b) ≃ Definition35Weight (family.problem b)),
    Definition35Equivariant (family.problem b) omega →
    ∀ psi : Definition35Brauer (family.problem b),
      Nonempty (CoherentMatchedCondition (family.problem b) psi (omega psi)) →
        LiteralTripleCondition (family.problem b) standard psi (omega psi)
  definition35_iff : ∀ (b : family.Block) (psi : Definition35Brauer (family.problem b))
      (w : Definition35Weight (family.problem b)),
    (semantics b).definition35BlockIsomorphic psi w ↔
      LiteralTripleCondition (family.problem b) standard psi w

theorem CoherentToDefinition35Source.implication {p : ℕ}
    {family : Definition35Family.{u} p}
    {automorphisms : ∀ b, Definition35AutomorphismStabilizerAdapter (family.problem b)}
    {centerless : Subgroup.center family.H = ⊥}
    {standard : BlockTripleSourceSemantics p family.k family.K}
    {semantics : ∀ b, FLZSourceSemantics (family.problem b) (automorphisms b)}
    (source : CoherentToDefinition35Source family centerless automorphisms standard semantics)
    (b : family.Block)
    (omega : Definition35Brauer (family.problem b) ≃ Definition35Weight (family.problem b))
    (equivariant : Definition35Equivariant (family.problem b) omega)
    (psi : Definition35Brauer (family.problem b))
    (h : Nonempty (CoherentMatchedCondition (family.problem b) psi (omega psi))) :
    (semantics b).definition35BlockIsomorphic psi (omega psi) :=
  (source.definition35_iff b psi (omega psi)).mpr
    (source.actual_triples b omega equivariant psi h)

def CoherentFamilyBijection.toDefinition35 {p : ℕ} {family : Definition35Family.{u} p}
    {automorphisms : ∀ b, Definition35AutomorphismStabilizerAdapter (family.problem b)}
    {centerless : Subgroup.center family.H = ⊥}
    {standard : BlockTripleSourceSemantics p family.k family.K}
    {semantics : ∀ b, FLZSourceSemantics (family.problem b) (automorphisms b)}
    (passage : CoherentToDefinition35Source family centerless automorphisms standard semantics)
    (C : CoherentFamilyBijection family) :
    Definition35IBAWFamilyWitness family automorphisms semantics where
  blockWitness b :=
    { omega := (C.blockWitness b).omega
      equivariant := (C.blockWitness b).equivariant
      blockIsomorphism := fun psi => passage.implication b (C.blockWitness b).omega
        (C.blockWitness b).equivariant psi ⟨(C.blockWitness b).matched psi⟩ }

@[simp] theorem CoherentFamilyBijection.toDefinition35_omega {p : ℕ}
    {family : Definition35Family.{u} p}
    {automorphisms : ∀ b, Definition35AutomorphismStabilizerAdapter (family.problem b)}
    {centerless : Subgroup.center family.H = ⊥}
    {standard : BlockTripleSourceSemantics p family.k family.K}
    {semantics : ∀ b, FLZSourceSemantics (family.problem b) (automorphisms b)}
    (passage : CoherentToDefinition35Source family centerless automorphisms standard semantics)
    (C : CoherentFamilyBijection family) (b : family.Block) :
    ((C.toDefinition35 passage).blockWitness b).omega = (C.blockWitness b).omega := rfl

section Descent

variable {p : ℕ} {coverFamily targetFamily : Definition35Family.{u} p}
variable (coverMatch : EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily)
variable (targetCenterless : Subgroup.center targetFamily.H = ⊥)
variable (diagram : FullCoverPrimeToDiagram coverFamily coverMatch.cover)
variable (inflation : FullCoverInflation diagram)
variable (coefficients : Coefficients coverFamily targetFamily)
variable (coverPhysical : PhysicalFamilySource coverFamily)
variable (targetPhysical : PhysicalFamilySource targetFamily)
variable (coverAutomorphisms : ∀ b,
  Definition35AutomorphismStabilizerAdapter (coverFamily.problem b))
variable (coverSemantics : FLZBAWGoodFamilySemantics coverFamily coverMatch.cover coverAutomorphisms)
variable (coverMeaning : ∀ b, BAWGoodRelationIdentification (coverSemantics.relation b))
variable (globalSemantics : SpathDefinition41GlobalSemantics coverFamily coverMatch.cover
  coverAutomorphisms coverSemantics)

/-- Exact published forward source, Spath 2013 Proposition 4.6 at r=1
and Spath 2017 Theorem 4.4's forward triple passage. The finite perfect
target is the SAME nonabelian simple quotient because `coverMatch` and
`targetCenterless` are fixed. Full-cover inflation is indexed on the
separate full-cover diagram, never on `coverMatch.cover.quotient`.

The U meaning of the full Definition 4.1 witness retains its radical-indexed
partition, equivariant local bijections, central character/block clauses,
and the Q=1 normalization, as well as the explicit family naturality.
The source is uniform in that actual full Definition 4.1 witness and the
compatible epimorphism; it does not accept a desired target witness.
-/
structure Proposition46Theorem44Source
    (coverMatch : EllPrimeCoverCentralExtensionFamilyMatch coverFamily targetFamily)
    (targetCenterless : Subgroup.center targetFamily.H = ⊥)
    (diagram : FullCoverPrimeToDiagram coverFamily coverMatch.cover)
    (inflation : FullCoverInflation diagram)
    (coefficients : Coefficients coverFamily targetFamily)
    (coverPhysical : PhysicalFamilySource coverFamily)
    (targetPhysical : PhysicalFamilySource targetFamily)
    (coverAutomorphisms : ∀ b,
      Definition35AutomorphismStabilizerAdapter (coverFamily.problem b))
    (coverSemantics : FLZBAWGoodFamilySemantics coverFamily coverMatch.cover coverAutomorphisms)
    (coverMeaning : ∀ b, BAWGoodRelationIdentification (coverSemantics.relation b))
    (globalSemantics : SpathDefinition41GlobalSemantics coverFamily coverMatch.cover
      coverAutomorphisms coverSemantics) : Prop where
  applyPublished : ∀ [IsAlgClosed coverFamily.K] [IsAlgClosed targetFamily.K]
      (coverField : SpathCoefficientField p coverFamily.k coverFamily.ellPrime)
      (targetField : SpathCoefficientField p targetFamily.k targetFamily.ellPrime)
      (definition41 : SpathDefinition41FamilyWitness globalSemantics)
      (coverToTarget : coverFamily.H →* targetFamily.H),
    Function.Surjective coverToTarget →
    coverMatch.targetQuotient.comp coverToTarget = coverMatch.cover.quotient →
    Nonempty (CoherentFamilyBijection targetFamily)

/-- The group epimorphism required by the published source is constructed
by maximality of the prime-to-p cover. -/
theorem current_corollary_2_5_coherent
    [IsAlgClosed coverFamily.K] [IsAlgClosed targetFamily.K]
    (source : Proposition46Theorem44Source coverMatch targetCenterless diagram inflation
      coefficients coverPhysical targetPhysical coverAutomorphisms coverSemantics coverMeaning globalSemantics)
    (coverField : SpathCoefficientField p coverFamily.k coverFamily.ellPrime)
    (targetField : SpathCoefficientField p targetFamily.k targetFamily.ellPrime)
    (definition41 : SpathDefinition41FamilyWitness globalSemantics) :
    Nonempty (CoherentFamilyBijection targetFamily) := by
  obtain ⟨q, hq, commutes⟩ := coverMatch.exists_coverToTarget
  exact source.applyPublished coverField targetField definition41 q hq commutes

theorem current_corollary_2_5
    [IsAlgClosed coverFamily.K] [IsAlgClosed targetFamily.K]
    (source : Proposition46Theorem44Source coverMatch targetCenterless diagram inflation
      coefficients coverPhysical targetPhysical coverAutomorphisms coverSemantics coverMeaning globalSemantics)
    (coverField : SpathCoefficientField p coverFamily.k coverFamily.ellPrime)
    (targetField : SpathCoefficientField p targetFamily.k targetFamily.ellPrime)
    (definition41 : SpathDefinition41FamilyWitness globalSemantics)
    (targetAutomorphisms : ∀ b,
      Definition35AutomorphismStabilizerAdapter (targetFamily.problem b))
    (targetSemantics : ∀ b, FLZSourceSemantics (targetFamily.problem b) (targetAutomorphisms b))
    (standard : BlockTripleSourceSemantics p targetFamily.k targetFamily.K)
    (passage : CoherentToDefinition35Source targetFamily targetCenterless targetAutomorphisms standard targetSemantics) :
    Nonempty (Definition35IBAWFamilyWitness targetFamily targetAutomorphisms targetSemantics) := by
  obtain ⟨C⟩ := current_corollary_2_5_coherent coverMatch targetCenterless diagram inflation
    coefficients coverPhysical targetPhysical coverAutomorphisms coverSemantics coverMeaning globalSemantics source
    coverField targetField definition41
  exact ⟨C.toDefinition35 passage⟩

end Descent

end ModularRep.CurrentSpathDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
