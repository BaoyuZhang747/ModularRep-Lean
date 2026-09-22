import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalCompleteCollapse
import ModularRep.Navarro417DefectSource

/-!
# The actual defect-group split for the J4 numerical input

The intended external noncyclic-defect counts are those of AOW Theorem 5.2;
the cyclic counts use the numerical bijection in the proof of Spath 6.2. The
split is tied to the primitive block's actual central Brauer support,
and existence of a defect representative is required. No arbitrary
predicate labels the two cases, and no inductive-condition packet is input.
The generic theorem below does not instantiate those published results on
a realized J4 carrier; the source ledger records that remaining binding.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4Numerical

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalCompleteCollapse

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

theorem exists_definition41_of_defect_counts
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (Cover : EllPrimeCoverSource p X) (hc : Subgroup.center X = ⊥)
    (allInner : AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    Nonempty (Definition41Witness iota hinj R C Cover hc D T) :=
  exists_definition41_of_numerical iota hinj R C Cover hc allInner D T
    (numericalBlockwiseAWC iota hinj R source) compatibility fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4Numerical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
