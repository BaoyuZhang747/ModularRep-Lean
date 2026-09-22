import ModularRep.NumericalBlockwiseLocalBijections
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# Numerical Lemma 5.2 construction on literal carriers

This module instantiates the source-neutral finite construction on
function-valued irreducible Brauer characters, literal weight conjugacy
classes, and literal primitive central idempotents. It accepts only numerical
equality of literal block fibres; no character-to-weight correspondence,
normalisation, defect-zero source, or inductive-condition conclusion is an
input.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicLemma52NumericalPartitionActual

open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))

noncomputable local instance actualBlockDecidableEq :
    DecidableEq (ActualBlock (k := k) (X := X)) :=
  Classical.decEq _

/-- The literal Brauer block selected from exactly R's ambient decomposition. -/
noncomputable def literalBrauerBlock (phi : IBr iota) :
    ActualBlock (k := k) (X := X) := by
  let O := R.1.operations
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  exact brauerBlock iota hinj O.ambientBlockData.blocks phi

/-- The literal target block assignment constructed by local block induction. -/
def literalWeightBlock :
    WeightClass (p := p) (K := K) (X := X) →
      ActualBlock (k := k) (X := X) :=
  R.1.weightBlock

/-- The literal radical-class assignment on weight conjugacy classes. -/
def literalWeightRadical :
    WeightClass (p := p) (K := K) (X := X) →
      RadicalClass (p := p) (X := X) :=
  weightRadical

/-- The ambient catalogue is literally indexed by its primitive idempotents.
This exposes R.2; it is a source projection, not a new block theorem. -/
theorem literalWeightBlock_idempotent
    (w : WeightClass (p := p) (K := K) (X := X)) :
    R.1.operations.ambientBlockData.blockIdempotent
        (literalWeightBlock R w) =
      (literalWeightBlock R w).1 :=
  R.2 _

/-- The literal form of the numerical blockwise AWC premise. -/
def LiteralBlockwiseCardinality [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))] : Prop :=
  NumericalBlockwiseLocalBijections.BlockwiseCardinality
    (literalBrauerBlock iota hinj R) (literalWeightBlock R)

/-- The chosen finite equivalence on one literal block fibre. -/
noncomputable def blockFibreEquiv [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    (hcard : LiteralBlockwiseCardinality iota hinj R)
    (b : ActualBlock (k := k) (X := X)) :
    {phi : IBr iota // literalBrauerBlock iota hinj R phi = b} ≃
      {w : WeightClass (p := p) (K := K) (X := X) //
        literalWeightBlock R w = b} :=
  NumericalBlockwiseLocalBijections.blockFibreEquiv
    (literalBrauerBlock iota hinj R) (literalWeightBlock R) hcard b

/-- The noncanonical global literal equivalence from the numerical premise. -/
noncomputable def globalEquiv [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    (hcard : LiteralBlockwiseCardinality iota hinj R) :
    IBr iota ≃ WeightClass (p := p) (K := K) (X := X) :=
  NumericalBlockwiseLocalBijections.globalEquiv
    (literalBrauerBlock iota hinj R) (literalWeightBlock R) hcard

/-- The constructed global equivalence preserves the literal primitive block. -/
theorem globalEquiv_block [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    (hcard : LiteralBlockwiseCardinality iota hinj R)
    (phi : IBr iota) :
    literalWeightBlock R (globalEquiv iota hinj R hcard phi) =
      literalBrauerBlock iota hinj R phi :=
  NumericalBlockwiseLocalBijections.globalEquiv_block
    (literalBrauerBlock iota hinj R) (literalWeightBlock R) hcard phi

/-- The radical class selected by the constructed global equivalence. -/
noncomputable def part [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    (hcard : LiteralBlockwiseCardinality iota hinj R) (phi : IBr iota) :
    RadicalClass (p := p) (X := X) :=
  NumericalBlockwiseLocalBijections.part
    (literalBrauerBlock iota hinj R) (literalWeightBlock R)
    (literalWeightRadical (p := p) (K := K) (X := X)) hcard phi

/-- The derived partition by literal radical conjugacy class. -/
noncomputable def partitionEquiv [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    (hcard : LiteralBlockwiseCardinality iota hinj R) :
    IBr iota ≃ Σ r : RadicalClass (p := p) (X := X),
      {phi : IBr iota // part iota hinj R hcard phi = r} :=
  NumericalBlockwiseLocalBijections.partitionEquiv
    (literalBrauerBlock iota hinj R) (literalWeightBlock R)
    (literalWeightRadical (p := p) (K := K) (X := X)) hcard

/-- The induced local equivalence on a literal block/radical fibre. -/
noncomputable def localFibreEquiv [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    (hcard : LiteralBlockwiseCardinality iota hinj R)
    (b : ActualBlock (k := k) (X := X))
    (r : RadicalClass (p := p) (X := X)) :
    {phi : IBr iota //
      literalBrauerBlock iota hinj R phi = b ∧
        part iota hinj R hcard phi = r} ≃
      {w : WeightClass (p := p) (K := K) (X := X) //
        literalWeightBlock R w = b ∧
          literalWeightRadical (p := p) (K := K) (X := X) w = r} :=
  NumericalBlockwiseLocalBijections.localFibreEquiv
    (literalBrauerBlock iota hinj R) (literalWeightBlock R)
    (literalWeightRadical (p := p) (K := K) (X := X)) hcard b r

end ModularRep.PaperProofs.SporadicLemma52NumericalPartitionActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
