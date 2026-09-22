import ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
import ModularRep.PaperProofs.EvenFieldProposition39StructuralCases

/-!
# A nonselective relative carrier for the source class `H_G`

Feng--Li--Zhang, p. 31, define `H_G` as the class of every pair consisting
of a simple algebraic group of simply connected type in the ambient defining
characteristic and a Steinberg endomorphism, subject to simplicity of the
finite central quotient and the Dynkin-subdiagram condition.  Hypothesis
5.5(b) quantifies over every pair in that class and every strictly
quasi-isolated block of its fixed-point group.  Proposition 5.6 uses this
full quantification after the derived Levi subgroup is split into rational
factors.

The earlier `FLZHGClass` allowed its carrier to be selected by a caller and
therefore could be empty.  This module instead fixes the relative carrier to
all `FLZHGCertifiedPair` structures in one Lean universe whose diagrams
satisfy the stated subdiagram predicate.  `FullHG` contains the ambient pair
canonically, so no list, representative family, or further membership
predicate can make this relative carrier empty.

There is not yet a library of algebraic groups, Steinberg endomorphisms, or
Dynkin diagrams.  Their meanings are consequently isolated in the fixed
indexed interface `FLZHGSourcePredicateAdapter` and remain E1/U.  Therefore
`FullHG` is not by itself a proof that the Lean carrier is the exact
mathematical class `H_G`: validating those predicates against the source is
still U.  In particular, a misinterpreted predicate could omit a genuine
source pair, and distinct Lean presentations could represent isomorphic
source pairs.  Proving source completeness and the intended identification
of presentations is an E1/U obligation.  The underlying group endomorphism,
fixed-point subgroup, and central quotient are literal.

Finite block data are not built into a source pair.  Instead,
`FullHGDefinition35Coverage` supplies a `Definition35Family` presentation for
every member of `FullHG`, together with a literal group equivalence to its
fixed points.  This total coverage field cannot select or omit members, but
matching its presentations to the source is E1/U.  Hypothesis 5.5(b) is
therefore formulated downstairs on the arbitrary fixed-point groups, without
imposing the universal-cover hypothesis needed only for final ambient
applicability.  Likewise, the strict quasi-isolation predicate and type-C
classifier are explicit U adapters.  No theorem in this file proves exact
source coverage, a classification case, a strictly quasi-isolated-block
result, Feng--Li--Zhang Theorem 5.7, BAW-goodness, or iBAW.  A future Theorem
5.7 gate must require the missing source-completeness and
predicate-correctness inputs and may not consume
`FullHGRelativeHypothesis55StrictBlocks` alone.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZFullHG

open Formalisation
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- Literal group-theoretic data underlying a source pair `(H,F')`.

The predicate that this group is algebraic and that `steinberg` is a
Steinberg endomorphism is deliberately kept in
`FLZHGSourcePredicateAdapter`.
Nevertheless, the fixed-point group below is the actual equaliser subgroup
of this supplied endomorphism, rather than an unrelated caller-supplied
group. -/
structure FLZHGAlgebraicPair (Diagram : Type u) where
  AlgebraicGroup : Type u
  [groupAlgebraicGroup : Group AlgebraicGroup]
  steinberg : AlgebraicGroup →* AlgebraicGroup
  diagram : Diagram

attribute [instance] FLZHGAlgebraicPair.groupAlgebraicGroup

/-- The literal fixed-point subgroup of the endomorphism in a source pair. -/
def FLZHGAlgebraicPair.fixedPointSubgroup
    {Diagram : Type u} (pair : FLZHGAlgebraicPair Diagram) :
    Subgroup pair.AlgebraicGroup :=
  pair.steinberg.eqLocus (MonoidHom.id pair.AlgebraicGroup)

/-- The group carried by the literal fixed-point subgroup. -/
abbrev FLZHGAlgebraicPair.FixedPointGroup
    {Diagram : Type u} (pair : FLZHGAlgebraicPair Diagram) :=
  pair.fixedPointSubgroup

/-- The unformalised algebraic and Dynkin-diagram semantics in the definition
of `H_G`.

Every predicate is indexed by a literal algebraic-group carrier,
endomorphism, and diagram.  This remains an E1/U source interface.  It is not
a selectable family of source pairs and contains no blockwise conclusion. -/
structure FLZHGSourcePredicateAdapter (pDef : ℕ) where
  Diagram : Type u
  definedOverCharacteristic : FLZHGAlgebraicPair Diagram → Prop
  simpleSimplyConnected : FLZHGAlgebraicPair Diagram → Prop
  isSteinbergEndomorphism : FLZHGAlgebraicPair Diagram → Prop
  diagramSubgraph : Diagram → Diagram → Prop
  diagramSubgraph_refl : ∀ diagram : Diagram,
    diagramSubgraph diagram diagram

/-- One algebraic pair satisfying the relative source predicates for `H_G`.

The finite fixed-point group and its central quotient are literal.  Whether
the three predicate fields express the intended algebraic notions is part of
the E1/U source interpretation, not a kernel theorem. -/
structure FLZHGCertifiedPair
    {pDef : ℕ} (semantics : FLZHGSourcePredicateAdapter pDef) where
  algebraicPair : FLZHGAlgebraicPair semantics.Diagram
  definedOverCharacteristic :
    semantics.definedOverCharacteristic algebraicPair
  simpleSimplyConnected : semantics.simpleSimplyConnected algebraicPair
  steinbergEndomorphism :
    semantics.isSteinbergEndomorphism algebraicPair
  fixedPointCentralQuotientSimple :
    IsSimpleGroup
      (algebraicPair.FixedPointGroup ⧸
        Subgroup.center algebraicPair.FixedPointGroup)

/-- A literal finite block presentation of one certified source pair.

The group equivalence is the E1/U identification of the family carrier with
the fixed-point group.  It is data, not an equality hidden by notation. -/
structure FLZHGDefinition35Presentation
    {pDef : ℕ} {semantics : FLZHGSourcePredicateAdapter pDef}
    (ell : ℕ) (pair : FLZHGCertifiedPair semantics) where
  family : Definition35Family.{u} ell
  fixedPointEquiv : family.H ≃* pair.algebraicPair.FixedPointGroup

/-- Divisibility of the represented finite group order is unchanged by the
fixed-point group identification. -/
@[simp]
theorem FLZHGDefinition35Presentation.dvd_card_fixedPointGroup_iff
    {pDef ell : ℕ}
    {semantics : FLZHGSourcePredicateAdapter pDef}
    {pair : FLZHGCertifiedPair semantics}
    (presentation : FLZHGDefinition35Presentation ell pair) :
    ell ∣ Nat.card presentation.family.H ↔
      ell ∣ Nat.card pair.algebraicPair.FixedPointGroup := by
  rw [Nat.card_congr presentation.fixedPointEquiv.toEquiv]

/-- The ambient relative source data at one defining prime and one
coefficient prime.

`distinctPrimes` states only `ell ≠ pDef`.  Interpreting this as the source
condition `ell ∤ q`, where `q` is the defining field size, remains part of
the E1/U algebraic source match because no field-size carrier is present
here.  The full universal-cover hypothesis in Feng--Li--Zhang Theorem 5.7 is
also deliberately absent from this `H_G` carrier. -/
structure FLZFullHGUniverse (pDef ell : ℕ) where
  semantics : FLZHGSourcePredicateAdapter pDef
  definingPrime : Nat.Prime pDef
  distinctPrimes : ell ≠ pDef
  ambient : FLZHGCertifiedPair semantics

/-- The nonselective `H_G` carrier relative to fixed source predicates and an
ambient pair.

Its carrier is every certified pair in the Lean universe whose Dynkin
diagram satisfies the supplied subdiagram predicate.  Exact agreement of
that predicate, and of the predicates inside `FLZHGCertifiedPair`, with the
mathematical definition of `H_G` remains E1/U. -/
def FullHG {pDef ell : ℕ} (scope : FLZFullHGUniverse pDef ell) :=
  { pair : FLZHGCertifiedPair scope.semantics //
    scope.semantics.diagramSubgraph pair.algebraicPair.diagram
      scope.ambient.algebraicPair.diagram }

/-- The ambient algebraic pair is a canonical member of the relative
carrier. -/
def FLZFullHGUniverse.ambientPair
    {pDef ell : ℕ} (scope : FLZFullHGUniverse pDef ell) :
    FullHG scope :=
  ⟨scope.ambient,
    scope.semantics.diagramSubgraph_refl
      scope.ambient.algebraicPair.diagram⟩

/-- Anti-vacuity: the relative carrier always contains its ambient pair. -/
instance fullHGNonempty
    {pDef ell : ℕ} (scope : FLZFullHGUniverse pDef ell) :
    Nonempty (FullHG scope) :=
  ⟨scope.ambientPair⟩

@[simp]
theorem FLZFullHGUniverse.ambientPair_val
    {pDef ell : ℕ} (scope : FLZFullHGUniverse pDef ell) :
    scope.ambientPair.1 = scope.ambient :=
  rfl

/-- Total finite block presentations for the relative `H_G` carrier.

Unlike the former selectable pair carrier, this adapter must present every
member of `FullHG`, including the canonical ambient member.  It is still
E1/U: Lean does not derive these finite group and block-theoretic
identifications from algebraic-group theory.  The universe stores no second
ambient presentation, so there is no unproved coherence between two choices. -/
structure FullHGDefinition35Coverage
    {pDef ell : ℕ} (scope : FLZFullHGUniverse pDef ell) where
  presentation : ∀ pair : FullHG scope,
    FLZHGDefinition35Presentation ell pair.1

/-- Fixed Definition 3.5 source semantics on every member of the relative
class.

The stabiliser adapter is an E1/U match.  The Definition 3.5
modular-character-triple relation inside `FLZSourceSemantics` remains U/E2.
All fields are total on `FullHG`; none can remove a source pair from the
class. -/
structure FullHGBlockSource
    {pDef ell : ℕ} {scope : FLZFullHGUniverse pDef ell}
    (coverage : FullHGDefinition35Coverage scope) where
  automorphisms : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block),
    Definition35AutomorphismStabilizerAdapter
      ((coverage.presentation pair).family.problem block)
  source : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block),
    FLZSourceSemantics ((coverage.presentation pair).family.problem block)
      (automorphisms pair block)

/-- The source interpretation of strict quasi-isolation for every presented
block in the relative carrier.

This is a separately named U/E1 adapter.  In particular, choosing the
predicate to be false would make the implication in Hypothesis 5.5(b)
vacuous, so no future Theorem 5.7 gate may credit this carrier as K or use it
without validating the predicate against the source definition. -/
structure FullHGStrictQuasiIsolationAdapter
    {pDef ell : ℕ} {scope : FLZFullHGUniverse pDef ell}
    (coverage : FullHGDefinition35Coverage scope) where
  predicate : ∀ (pair : FullHG scope),
    (coverage.presentation pair).family.Block → Prop

/-- The relative quantifier shape of Feng--Li--Zhang Hypothesis 5.5(b).

There is no membership premise: `pair` ranges over every member of the
nonselective relative carrier and the coverage adapter presents every such
member.  Exact agreement with the source class and with source strict
quasi-isolation remains U.  The field is the E2 strict-block input asserted
by Hypothesis 5.5(b), not a derived iBAW result. -/
structure FullHGRelativeHypothesis55StrictBlocks
    {pDef ell : ℕ} {scope : FLZFullHGUniverse pDef ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage) where
  iBAWBijection : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block),
    strictSource.predicate pair block →
      Nonempty (Definition35IBAWBijection
        ((coverage.presentation pair).family.problem block)
        (blockSource.automorphisms pair block)
        (blockSource.source pair block))

/-- A total classification of every source pair whose order is divisible by
the coefficient prime into the noncoprime structural cases used by the type
`C` proof.  This is E1/U source data.  It asserts no branch theorem and cannot
select the outside-order case or omit a divisible-order member of `FullHG`. -/
structure FullHGTypeCClassificationSource
    {pDef ell : ℕ} (scope : FLZFullHGUniverse pDef ell) where
  classify : ∀ pair : FullHG scope,
    ell ∣ Nat.card pair.1.algebraicPair.FixedPointGroup →
      EvenFieldProposition39Relative.NoncoprimeStructuralCase

namespace FullHGTypeCClassificationSource

/-- Determine the outside-order case in the kernel and consult the external
classifier only when the coefficient prime divides the represented group
order. -/
def structuralCase
    {pDef ell : ℕ}
    {scope : FLZFullHGUniverse pDef ell}
    (classification : FullHGTypeCClassificationSource scope)
    (coverage : FullHGDefinition35Coverage scope)
    (pair : FullHG scope) :
    EvenFieldProposition39Relative.StructuralCase :=
  if h : ell ∣ Nat.card (coverage.presentation pair).family.H then
    (classification.classify pair
      ((coverage.presentation pair).dvd_card_fixedPointGroup_iff.mp h)
    ).toStructuralCase
  else
    .primeOutsideOrder

@[simp]
theorem structuralCase_eq_primeOutsideOrder_iff
    {pDef ell : ℕ}
    {scope : FLZFullHGUniverse pDef ell}
    (classification : FullHGTypeCClassificationSource scope)
    (coverage : FullHGDefinition35Coverage scope)
    (pair : FullHG scope) :
    classification.structuralCase coverage pair = .primeOutsideOrder ↔
      ¬ ell ∣ Nat.card (coverage.presentation pair).family.H := by
  simp [structuralCase]

end FullHGTypeCClassificationSource

end ModularRep.PaperProofs.EvenFieldFLZFullHG


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
