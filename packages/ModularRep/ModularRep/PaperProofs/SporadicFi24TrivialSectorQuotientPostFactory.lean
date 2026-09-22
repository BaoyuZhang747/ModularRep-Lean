import ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientIBrFactory
import ModularRep.PaperProofs.SporadicFi24CentrelessOneSectorSourceReduction

/-!
# The minimal post-factory Fischer trivial-sector wrapper

This experimental module performs one composition only.  It first constructs
the carrier transport through the central-quotient `IBr` factory, then packs
the separately supplied five-field centreless one-sector source into the
existing An--Dietrich source, and finally calls the existing trivial-sector
specialisation.

The wrapper accepts the factory's exact six-field residual transport and the
quotient correspondence mathematics in the exact five-field
`CentrelessOneSectorInput`.  It accepts no `CarrierTransport`,
`AnDietrichFaithfulSectorSource`, `QuotientCorrespondence`,
`TrivialSectorQuotientSource`, cover character--weight equivalence, all-sector
family, sector combination or Spath input, `Q = 1` datum, three-block census, BAW
goodness, or iBAW datum.  In particular, QAD remains explicit E2/U input; the
factory does not prove it.

The literal quotient is definitionally `X ⧸ Subgroup.center X`.  The visible
cover-center invertibility instance is the genuine central-`ell'` boundary.
The quotient-center instance is retained for compatibility with the existing
dependent carrier API; centrelessness can prove it, but cannot synthesize it
retroactively after the quotient carrier arguments have been elaborated.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientPostFactory

open Formalisation
open Formalisation.IBAW
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport
open ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Actual
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24TrivialFaithfulSectorGlue
open ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientSpecialisation
open ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientIBrFactory
open ModularRep.PaperProofs.SporadicFi24CentrelessOneSectorSourceReduction

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

noncomputable local instance coverCenterFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

noncomputable local instance quotientFintype :
    Fintype (X ⧸ Subgroup.center X) :=
  Fintype.ofFinite _

noncomputable local instance quotientCenterFintype :
    Fintype (Subgroup.center (X ⧸ Subgroup.center X)) :=
  Fintype.ofFinite _

variable (coverIota : PrimeRegularRootEmbedding p k K X)
variable (coverHinj : IrreducibleBrauerCharacterInjectivity coverIota)
variable {CoverBlockIndex : Type u} [Fintype CoverBlockIndex]
variable {coverBlockIdempotent : CoverBlockIndex → k[X]}
variable (coverBlocks : BlockIdempotentDecomposition coverBlockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (coverBlockSource : LiteralCarrierAdapter
  (p := p) (k := k) (K := K) (X := X))
variable (coverE1 : RoutineTransportInput coverIota coverHinj coverBlocks
  coverBlockSource)

variable (quotientIota : PrimeRegularRootEmbedding p k K
  (X ⧸ Subgroup.center X))
variable (quotientHinj : IrreducibleBrauerCharacterInjectivity quotientIota)
variable {QuotientBlockIndex : Type u} [Fintype QuotientBlockIndex]
variable {quotientBlockIdempotent :
  QuotientBlockIndex → k[X ⧸ Subgroup.center X]}
variable (quotientBlocks :
  BlockIdempotentDecomposition quotientBlockIdempotent)
variable [Invertible
  (Fintype.card (Subgroup.center (X ⧸ Subgroup.center X)) : k)]
variable (quotientBlockSource : LiteralCarrierAdapter
  (p := p) (k := k) (K := K) (X := X ⧸ Subgroup.center X))
variable (quotientE1 : RoutineTransportInput quotientIota quotientHinj
  quotientBlocks quotientBlockSource)

/-- Construct the exact trivial-sector source from the independently exposed
factory and centreless one-sector boundaries.

The body order is part of the source-shape contract: construct `T`, construct
`AD`, and call `trivialSectorQuotientSource` exactly once.  The quotient
correspondence and lifted equivalence remain internal to that existing final
constructor. -/
def trivialSectorQuotientSource_ofCentralIBr
    (ModularCharacterTriple :
      IBr coverIota → WeightClass (p := p) (K := K) (X := X) → Prop)
    (QuotientPair :
      QuotientBrauer quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1 →
        QuotientWeight quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1 → Prop)
    (source : QuotientRealisationSource (Subgroup.center X)
      coverIota quotientIota)
    (C0 : CentrelessQuotient
      (Xbar := X ⧸ Subgroup.center X))
    (descent : (MulAut X)ᵐᵒᵖ →*
      (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ)
    (hcomm : ∀ (a : (MulAut X)ᵐᵒᵖ) (x : X),
      QuotientGroup.mk' (Subgroup.center X) (a.unop x) =
        (descent a).unop
          (QuotientGroup.mk' (Subgroup.center X) x))
    (R : RemainingCarrierTransport coverIota coverHinj coverBlocks
      coverBlockSource coverE1 quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 source C0 descent
      ModularCharacterTriple QuotientPair)
    (QAD : CentrelessOneSectorInput
      (iota := quotientIota) (hinj := quotientHinj)
      (blocks := quotientBlocks) (R := quotientBlockSource)
      (E1 := quotientE1) C0 QuotientPair) :
    TrivialSectorQuotientSource coverIota coverHinj coverBlocks
      coverBlockSource coverE1 ModularCharacterTriple := by
  let T := carrierTransport_ofCentralIBr
    coverIota coverHinj coverBlocks coverBlockSource coverE1
    quotientIota quotientHinj quotientBlocks quotientBlockSource quotientE1
    source C0 descent hcomm ModularCharacterTriple QuotientPair R
  let AD := anDietrichFaithfulSectorSource_ofCentreless
    (iota := quotientIota) (hinj := quotientHinj)
    (blocks := quotientBlocks) (R := quotientBlockSource)
    (E1 := quotientE1) C0 QuotientPair QAD
  exact trivialSectorQuotientSource
    coverIota coverHinj coverBlocks coverBlockSource coverE1
    quotientIota quotientHinj quotientBlocks quotientBlockSource quotientE1
    descent ModularCharacterTriple QuotientPair QAD.pair_equivariant C0 AD T

end ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientPostFactory


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
