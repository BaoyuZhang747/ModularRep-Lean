import ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientPostFactory

/-!
# The post-factory Fischer cover-sector glue

This experimental module is the exact next composition after the
central-quotient `IBr` factory.  It keeps the cover-side faithful-sector
mathematics independent of the quotient package, constructs the cover's
trivial-sector source with the post-factory wrapper, and then invokes the
existing trivial/faithful-sector glue.

`CoverFaithfulGlueInput` has exactly three fields.  The coverage field is the
faithful-complement classification (E1/U).  Pair-predicate equivariance and
the one-faithful-sector An--Dietrich source are E2/U.  In particular, the
record contains no trivial-sector source, global character--weight
equivalence, all-sector fibre family, `AnDietrichSectorInput`, Spath Lemma 6.1
input, `Q = 1` datum, BAW goodness, or iBAW conclusion.

The constructor retains the post-factory wrapper's raw quotient telescope:
root realisation, centrelessness, the opposite-automorphism descent square,
the exact six-field remaining carrier transport, and the exact five-field
centreless one-sector input.  It accepts neither the wrapper's
`TrivialSectorQuotientSource` output nor its final
`AnDietrichSectorInput` output as a premise.  The combined family and block
clause are K relative to the displayed sources; its character-triple clause
remains L over their E2/U fields.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24CoverFaithfulGluePostFactory

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
open ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientPostFactory

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

/-! ## The independent cover-side faithful source -/

/-- The smallest cover-side source consumed by the existing
trivial/faithful-sector glue.

Coverage identifies the faithful complement of the trivial sector.  It does
not choose the base faithful sector or prove transport between the two
faithful sectors; those genuinely representation theoretic data remain
inside the one-sector An--Dietrich source. -/
structure CoverFaithfulGlueInput
    (ModularCharacterTriple :
      IBr coverIota → WeightClass (p := p) (K := K) (X := X) → Prop) where
  coverage : ThreeSectorCoverage (k := k) (X := X)
  pair_equivariant :
    PairPropertyEquivariant
      (A := (MulAut X)ᵐᵒᵖ)
      (X := FaithfulIBr coverIota coverHinj coverBlocks
        coverBlockSource coverE1)
      (Y := FaithfulWeight coverIota coverHinj coverBlocks
        coverBlockSource coverE1)
      (FaithfulCharacterTriple coverIota coverHinj coverBlocks
        coverBlockSource coverE1 ModularCharacterTriple)
  anDietrich : AnDietrichFaithfulSectorSource
    coverIota coverHinj coverBlocks coverBlockSource coverE1
    (FaithfulCharacterTriple coverIota coverHinj coverBlocks
      coverBlockSource coverE1 ModularCharacterTriple)
    pair_equivariant

/-! ## Composition through the post-factory trivial source -/

/-- Construct the inputs on all central sectors before combining the
Fischer sector correspondences.

The body first constructs the trivial-sector source from the raw quotient
data and then calls the existing cover glue exactly once.  It neither invokes
the sector combination nor assumes any Spath, `Q = 1`, BAW, or iBAW datum. -/
def anDietrichSectorInput_ofCentralIBr
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
      (E1 := quotientE1) C0 QuotientPair)
    (CoverAD : CoverFaithfulGlueInput
      (coverIota := coverIota) (coverHinj := coverHinj)
      (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
      (coverE1 := coverE1) ModularCharacterTriple) :
    AnDietrichSectorInput coverIota coverHinj coverBlocks coverE1
      ModularCharacterTriple := by
  let trivial := trivialSectorQuotientSource_ofCentralIBr
    coverIota coverHinj coverBlocks coverBlockSource coverE1
    quotientIota quotientHinj quotientBlocks quotientBlockSource quotientE1
    ModularCharacterTriple QuotientPair source C0 descent hcomm R QAD
  exact anDietrichSectorInput
    coverIota coverHinj coverBlocks coverBlockSource coverE1
    ModularCharacterTriple CoverAD.coverage trivial
    CoverAD.pair_equivariant CoverAD.anDietrich

end ModularRep.PaperProofs.SporadicFi24CoverFaithfulGluePostFactory


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
