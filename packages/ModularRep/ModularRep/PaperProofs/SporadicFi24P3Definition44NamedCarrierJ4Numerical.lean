import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCompleteCollapse
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

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCompleteCollapse

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))

def actualHasDefect (b : ActualBlock (k := k) (X := X)) (D : Subgroup X) : Prop :=
  letI : Fact p.Prime := ⟨iota.prime⟩
  letI := R.1.operations.ambientBlockData.fintypeBlock
  Navarro411DefectRepresentative (p := p) R.1.operations.ambientBlockData.blocks b D

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

def blockCardEq (b : ActualBlock (k := k) (X := X)) : Prop := by
  classical
  let := R.1.operations.ambientBlockData.fintypeBlock
  exact Fintype.card {phi : IBr iota //
      brauerBlock (iota := iota) (hinj := hinj) (blocks := R.1.operations.ambientBlockData.blocks) phi = b} =
    Fintype.card {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b}

structure CyclicNoncyclicNumericalSource : Prop where
  existsDefect : ∀ b : ActualBlock (k := k) (X := X), ∃ D : Subgroup X, actualHasDefect iota R b D
  cyclicCardEq : ∀ (b : ActualBlock (k := k) (X := X)) (D : Subgroup X),
    actualHasDefect iota R b D → IsCyclic D → blockCardEq iota hinj R b
  noncyclicCardEq : ∀ (b : ActualBlock (k := k) (X := X)) (D : Subgroup X),
    actualHasDefect iota R b D → ¬ IsCyclic D → blockCardEq iota hinj R b

theorem numericalBlockwiseAWC (source : CyclicNoncyclicNumericalSource iota hinj R) :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    NumericalBlockwiseAWC (iota := iota) (hinj := hinj)
      (blocks := R.1.operations.ambientBlockData.blocks) (R := R) := by
  intro b
  obtain ⟨D, hD⟩ := source.existsDefect b
  by_cases hcyc : IsCyclic D
  · simpa only [blockCardEq, ← Nat.card_eq_fintype_card] using source.cyclicCardEq b D hD hcyc
  · simpa only [blockCardEq, ← Nat.card_eq_fintype_card] using source.noncyclicCardEq b D hD hcyc

theorem exists_definition41_of_defect_counts
    (localReduction : ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
      SelectedLocalReductionSource R.1 b w)
    (Cover : EllPrimeCoverSource p X) (hc : Subgroup.center X = ⊥)
    (allInner : AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    Nonempty (Definition41Witness iota hinj R localReduction Cover hc D T) :=
  exists_definition41_of_numerical iota hinj R localReduction Cover hc allInner D T
    (numericalBlockwiseAWC iota hinj R source) compatibility fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
