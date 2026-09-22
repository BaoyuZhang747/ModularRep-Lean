import ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientSpecialisation

/-!
# A minimal one-sector source on a centreless Fischer quotient

For a centreless group the faithful central-sector carrier has a canonical
element and is a subsingleton.  Hence the base sector and the transporter
fields of `AnDietrichFaithfulSectorSource` are not external data: the base is
the trivial central character and every transporter can be chosen to be the
identity.

`CentrelessOneSectorInput` retains exactly five independent fields.  The
first is equivariance of the selected pair predicate.  The remaining four are
the one-sector An--Dietrich equivalence, its stabiliser equivariance, its
block-induction clause, and the character-triple implication.  It contains no
chosen sector, transporter, global equivalence, global fibre family,
`AnDietrichSectorInput`, Spath input, BAW-goodness, or iBAW conclusion.

This module is independent of the central-quotient `IBr` factory.  It does not
construct a quotient, carrier transport, trivial-sector source, or combined
Fischer correspondence.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24CentrelessOneSectorSourceReduction

open Formalisation
open Formalisation.IBAW
open ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Actual
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientSpecialisation

universe u

variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R :
  LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-! ## The canonical faithful sector -/

/-- On a centreless group the trivial central character is faithful. -/
def centrelessFaithfulSector
    (C0 : CentrelessQuotient (Xbar := X)) :
    FaithfulSector (k := k) (X := X) :=
  ⟨1, by
    intro z w _h
    exact (C0.center_eq_one z).trans (C0.center_eq_one w).symm⟩

/-! ## The exact five-field source -/

/-- The minimal substantive source for the unique faithful sector of a
centreless group.

The carrier types, sector maps, block maps, and actions are the existing
literal ones.  `pair_equivariant` is separate from the four selected-sector
clauses because it is an input to the general sector transport construction.  No field can
choose a base sector, a transporter, or an all-sector correspondence. -/
structure CentrelessOneSectorInput
    (C0 : CentrelessQuotient (Xbar := X))
    (Pair :
      FaithfulIBr iota hinj blocks R E1 →
        FaithfulWeight iota hinj blocks R E1 → Prop) where
  pair_equivariant :
    PairPropertyEquivariant
      (A := (MulAut X)ᵐᵒᵖ)
      (X := FaithfulIBr iota hinj blocks R E1)
      (Y := FaithfulWeight iota hinj blocks R E1)
      Pair
  baseEquiv :
    Fibre (faithfulBrauerSector iota hinj blocks R E1)
        (centrelessFaithfulSector C0) ≃
      Fibre (faithfulWeightSector iota hinj blocks R E1)
        (centrelessFaithfulSector C0)
  baseEquivariant : ∀ (a : (MulAut X)ᵐᵒᵖ)
      (ha : a • centrelessFaithfulSector C0 =
        centrelessFaithfulSector C0)
      (phi : Fibre (faithfulBrauerSector iota hinj blocks R E1)
        (centrelessFaithfulSector C0)),
    baseEquiv
        (stabilizerFibreEquiv
          (faithfulBrauerSector iota hinj blocks R E1)
          (actualReplacementContext iota hinj blocks R E1 Pair
            pair_equivariant).brauerSector_equivariant
          (centrelessFaithfulSector C0) a ha phi) =
      stabilizerFibreEquiv
        (faithfulWeightSector iota hinj blocks R E1)
        (actualReplacementContext iota hinj blocks R E1 Pair
          pair_equivariant).weightSector_equivariant
        (centrelessFaithfulSector C0) a ha (baseEquiv phi)
  baseBlockInduction : ∀ phi :
      Fibre (faithfulBrauerSector iota hinj blocks R E1)
        (centrelessFaithfulSector C0),
    faithfulWeightBlock iota hinj blocks R E1 (baseEquiv phi) =
      faithfulBrauerBlock iota hinj blocks R E1 phi
  characterTriple_of_stabilizer_eq : ∀
      (phi : FaithfulIBr iota hinj blocks R E1)
      (w : FaithfulWeight iota hinj blocks R E1),
    faithfulWeightSector iota hinj blocks R E1 w =
        faithfulBrauerSector iota hinj blocks R E1 phi →
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi.val =
        MulAction.stabilizer (MulAut X)ᵐᵒᵖ w.val →
      Pair phi w

/-! ## Construction of the source for sector transport -/

/-- Fill the redundant sector/transporter fields canonically and copy exactly
the five independent fields of `CentrelessOneSectorInput`.

The result is still a one-sector An--Dietrich source.  This constructor does
not perform sector transport and does not construct the global correspondence. -/
def anDietrichFaithfulSectorSource_ofCentreless
    (C0 : CentrelessQuotient (Xbar := X))
    (Pair :
      FaithfulIBr iota hinj blocks R E1 →
        FaithfulWeight iota hinj blocks R E1 → Prop)
    (S : CentrelessOneSectorInput iota hinj blocks E1 C0 Pair) :
    AnDietrichFaithfulSectorSource iota hinj blocks R E1 Pair
      S.pair_equivariant where
  baseSector := centrelessFaithfulSector C0
  transporter := fun _ => 1
  transporter_spec sector := by
    rw [one_smul]
    exact faithfulSector_unique C0 (centrelessFaithfulSector C0) sector
  baseEquiv := S.baseEquiv
  baseEquivariant := S.baseEquivariant
  baseBlockInduction := S.baseBlockInduction
  characterTriple_of_stabilizer_eq :=
    S.characterTriple_of_stabilizer_eq

end ModularRep.PaperProofs.SporadicFi24CentrelessOneSectorSourceReduction



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
