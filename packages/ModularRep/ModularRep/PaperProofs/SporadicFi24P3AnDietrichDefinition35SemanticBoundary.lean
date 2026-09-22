import ModularRep.PaperProofs.SporadicFi24P3AnDietrichCharacterTripleTransport

/-!
# The semantic boundary from An--Dietrich Definition 4.4 to FLZ Definition 3.5

The retained An--Dietrich datum is source-native witness data at the exact
published matched pair, together with pointwise equality of the replacement
map and the transported published map.  The live Feng--Li--Zhang
Definition 3.5 relation is currently represented by the single unconstrained
`Prop`-valued field of `FLZSourceSemantics`.

There is consequently no noncircular semantic-realisation interface between
the two representations in the present library.  At a fixed matched pair,
an implication from the retained datum to the live relation is logically
equivalent to the live relation itself, since the retained datum has already
been constructed.  Moreover, no conversion can be uniform in
`FLZSourceSemantics`: its relation may be constantly false.

The theorems below record both obstructions.  They deliberately introduce no
interface carrying the target relation, no character-triple implication, and
no BAW or iBAW field.  A genuine bridge requires a formal definition of the
modular-character-triple relation (or equivalent projective-representation
and factor-set semantics) and a source theorem interpreting the concrete
An--Dietrich witness in that definition.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3AnDietrichDefinition35SemanticBoundary

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate.AnDietrichFi24P3SourceCertificate
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichCharacterTripleTransport

universe u

/-! ## The arbitrary live relation admits a false interpretation -/

/-- The constantly-false interpretation is a legal `FLZSourceSemantics`
because that structure currently imposes no semantic laws on its sole
relation field. -/
def falseFLZSourceSemantics
    (P : Definition35Problem.{u})
    (automorphisms : Definition35AutomorphismStabilizerAdapter P) :
    FLZSourceSemantics P automorphisms where
  definition35BlockIsomorphic := fun _ _ ↦ False

/-! ## Fi24 at three: a pointwise no-go theorem -/

variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]

variable {k K X Gamma : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable [Group Gamma] [Finite Gamma]

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
variable (block : ActualBlock (k := k) (X := X))
variable (gamma : Gamma →* MulAut X)
variable (gammaBlock_fixed : ∀ a : Gamma,
  inverseOpHom gamma a • block = block)
variable (localReduction : ∀ w : LiteralWeightFibre R.1 block,
  SelectedLocalReductionSource R.1 block w)

variable
  (AD : AnDietrichFi24P3SourceCertificate
    (SourceAction := SourceAction)
    (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight))
  (Bridge : AnDietrichFi24P3LiteralCarrierBridge
    (SourceAction := SourceAction)
    (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)

/-- Because the exact same-map source datum is already inhabited, accepting
an eliminator from that datum to the live Definition 3.5 relation is
pointwise equivalent to accepting the desired relation itself.

This is the formal reason that a field of the form "the An--Dietrich witness
implies `definition35BlockIsomorphic`" would be a circular wrapper rather
than a semantic realisation. -/
theorem retained_pair_eliminator_iff_live_relation
    (replacement : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) ≃
      Definition35Weight
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction))
    (binding : AnDietrichDefinition44SameMapBinding
      iota hinj R block gamma gammaBlock_fixed localReduction AD Bridge
      replacement)
    (automorphisms : Definition35AutomorphismStabilizerAdapter
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction))
    (semantics : FLZSourceSemantics
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction) automorphisms)
    (psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction)) :
    (((replacement psi).1 = literalEquiv iota AD Bridge psi.1 ∧
        Nonempty (binding.CharacterTripleWitness
          (Bridge.brauerIdentification psi.1)
          (AD.sourceEquiv (Bridge.brauerIdentification psi.1)))) →
      semantics.definition35BlockIsomorphic psi (replacement psi)) ↔
    semantics.definition35BlockIsomorphic psi (replacement psi) := by
  constructor
  · intro realization
    exact realization
      (replacement_retains_definition44_witness
        iota hinj R block gamma gammaBlock_fixed localReduction
        AD Bridge replacement binding psi)
  · intro target _
    exact target

/-- No conversion from the retained An--Dietrich pair can produce the live
relation uniformly for all legal `FLZSourceSemantics`.  Instantiating the
putative conversion with the constantly-false semantics gives a
contradiction.

Thus a future positive bridge must first replace the unconstrained semantic
placeholder by a concrete, fixed interpretation of modular character
triples; it cannot be parametric in the current `FLZSourceSemantics`. -/
theorem no_uniform_retained_pair_to_flz_semantics
    (replacement : Definition35Brauer
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) ≃
      Definition35Weight
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction))
    (binding : AnDietrichDefinition44SameMapBinding
      iota hinj R block gamma gammaBlock_fixed localReduction AD Bridge
      replacement)
    (automorphisms : Definition35AutomorphismStabilizerAdapter
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction))
    (psi : Definition35Brauer
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction)) :
    ¬ (∀ semantics : FLZSourceSemantics
        (fi24P3Definition35Problem iota hinj R block gamma
          gammaBlock_fixed localReduction) automorphisms,
      ((replacement psi).1 = literalEquiv iota AD Bridge psi.1 ∧
        Nonempty (binding.CharacterTripleWitness
          (Bridge.brauerIdentification psi.1)
          (AD.sourceEquiv (Bridge.brauerIdentification psi.1)))) →
      semantics.definition35BlockIsomorphic psi (replacement psi)) := by
  intro realization
  have retained := replacement_retains_definition44_witness
    iota hinj R block gamma gammaBlock_fixed localReduction
    AD Bridge replacement binding psi
  exact realization
    (falseFLZSourceSemantics
      (fi24P3Definition35Problem iota hinj R block gamma
        gammaBlock_fixed localReduction) automorphisms)
    retained

end ModularRep.PaperProofs.SporadicFi24P3AnDietrichDefinition35SemanticBoundary


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
