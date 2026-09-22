import ModularRep.PaperProofs.CentralEllPrimeIBrFibreEquivariance
import ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientSpecialisation

/-!
# Experimental downstream Fischer adapter for central-quotient `IBr` transport

This experimental downstream adapter constructs the two Brauer fields of
`CentralEllPrimeTrivialSectorTransportAdapter.CarrierTransport` when the
quotient group is definitionally
`X ⧸ Subgroup.center X`.  It aligns the literal Fischer trivial sector with
the block-central character fibre, applies the kernel-constructed central
`ell'` quotient equivalence, and then adds the automatic faithfulness proof
on a centreless quotient.

The root/prime regular realisation source, the automorphism descent and its
literal quotient square, and centrelessness remain explicit.  A separate
six-field source retains exactly weight transport, block transport, their
remaining squares, and the pair/character-triple implication.  No Brauer
equivalence or Brauer equivariance assertion is accepted as a premise.

The visible instance
`Invertible (Fintype.card (Subgroup.center X) : k)` is the formal
central-`ell'` boundary.  For the triple cover `3.Fi'24`, whose centre has
order three, this factory can be used in characteristic two after the
concrete carrier bindings, but never in characteristic three.  It makes no
claim that an abstract quotient is a Fischer group and constructs no weight,
block-induction, selected correspondence, BAW, or iBAW conclusion.

This is not the source-neutral raw-`IBr` core: it imports the existing Fischer
specialisation in order to target its faithful quotient carrier.  The second
invertibility instance, for the centre of the quotient, is plumbing required
by that carrier API.  The first instance, for the centre of `X`, is the
mathematical central-`ell'` condition used by quotient/fibre transport.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientIBrFactory

open Formalisation
open Formalisation.IBAW
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreEquivariance
open ModularRep.PaperProofs.CentralEllPrimeTrivialSectorTransportAdapter
open ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Actual
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientSpecialisation

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

/-! ## The two carrier alignments -/

/-- The Fischer trivial Brauer sector is the literal trivial
block-central character fibre for the whole centre.  The maps are identity on
the underlying function-valued Brauer character. -/
def coverBrauerEquivTrivialCentralCharacterFibre :
    CoverBrauer coverIota coverHinj coverBlocks ≃
      TrivialCentralCharacterFibre coverIota coverBlocks coverHinj le_rfl where
  toFun phi := ⟨phi.1, by
    change brauerSector coverIota coverHinj coverBlocks phi.1 = 1
    exact phi.2⟩
  invFun phi := ⟨phi.1, by
    change blockCentralCharacter coverIota coverBlocks coverHinj le_rfl
      phi.1 = 1
    exact phi.2⟩
  left_inv phi := by
    apply Subtype.ext
    rfl
  right_inv phi := by
    apply Subtype.ext
    rfl

/-- The identity carrier alignment intertwines the existing stabiliser-fibre
action with the literal central-fibre twist action.  Both sides have the same
underlying `IBr` twist; only their membership proofs differ. -/
theorem coverBrauerEquivTrivialCentralCharacterFibre_equivariant
    (descent : (MulAut X)ᵐᵒᵖ →*
      (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ)
    (hcomm : ∀ (a : (MulAut X)ᵐᵒᵖ) (g : X),
      QuotientGroup.mk' (Subgroup.center X) (a.unop g) =
        (descent a).unop
          (QuotientGroup.mk' (Subgroup.center X) g))
    (a : (MulAut X)ᵐᵒᵖ)
    (phi : CoverBrauer coverIota coverHinj coverBlocks) :
    coverBrauerEquivTrivialCentralCharacterFibre coverIota coverHinj
        coverBlocks
        ((coverBrauerMulAction
          (coverIota := coverIota) (coverHinj := coverHinj)
          (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
          (coverE1 := coverE1)).smul a phi) =
      (trivialCentralCharacterFibreMulAction coverIota coverBlocks coverHinj
        le_rfl descent hcomm).smul a
        (coverBrauerEquivTrivialCentralCharacterFibre coverIota coverHinj
          coverBlocks phi) := by
  apply Subtype.ext
  rfl

/-- On a centreless quotient every irreducible Brauer character belongs to a
faithful central sector.  This equivalence merely adds or forgets that proof;
it does not use quotient block transport. -/
def iBrEquivFaithfulIBrOfCentreless
    (C0 : CentrelessQuotient
      (Xbar := X ⧸ Subgroup.center X)) :
    IBr quotientIota ≃
      QuotientBrauer quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 where
  toFun phi := ⟨phi, by
    intro z w _h
    exact (C0.center_eq_one z).trans (C0.center_eq_one w).symm⟩
  invFun phi := phi.val
  left_inv phi := rfl
  right_inv phi := by
    cases phi
    rfl

/-- Adding the automatic faithfulness proof commutes with the restricted
literal `IBr` action. -/
theorem iBrEquivFaithfulIBrOfCentreless_equivariant
    (C0 : CentrelessQuotient
      (Xbar := X ⧸ Subgroup.center X))
    (descent : (MulAut X)ᵐᵒᵖ →*
      (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ)
    (a : (MulAut X)ᵐᵒᵖ) (phi : IBr quotientIota) :
    iBrEquivFaithfulIBrOfCentreless
        (quotientIota := quotientIota) (quotientHinj := quotientHinj)
        (quotientBlocks := quotientBlocks)
        (quotientBlockSource := quotientBlockSource)
        (quotientE1 := quotientE1) C0
        ((quotientIBrMulAction quotientIota descent).smul a phi) =
      (quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 descent).smul a
        (iBrEquivFaithfulIBrOfCentreless
          (quotientIota := quotientIota) (quotientHinj := quotientHinj)
          (quotientBlocks := quotientBlocks)
          (quotientBlockSource := quotientBlockSource)
          (quotientE1 := quotientE1) C0 phi) := by
  rw [FaithfulIBr.mk.injEq]
  rfl

/-! ## The constructed Brauer part of carrier transport -/

/-- Cover-to-quotient Brauer transport is the composite of the two carrier
alignments with the inverse of the kernel-constructed quotient/fibre
equivalence.  No descent data is needed to define its values. -/
def centralIBrBrauer
    (source : QuotientRealisationSource (Subgroup.center X)
      coverIota quotientIota)
    (C0 : CentrelessQuotient
      (Xbar := X ⧸ Subgroup.center X)) :
    CoverBrauer coverIota coverHinj coverBlocks ≃
      QuotientBrauer quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 :=
  (coverBrauerEquivTrivialCentralCharacterFibre coverIota coverHinj
      coverBlocks).trans
    ((quotientIBrEquivTrivialCentralCharacterFibre coverIota quotientIota
      source coverBlocks coverHinj le_rfl).symm.trans
      (iBrEquivFaithfulIBrOfCentreless
        (quotientIota := quotientIota) (quotientHinj := quotientHinj)
        (quotientBlocks := quotientBlocks)
        (quotientBlockSource := quotientBlockSource)
        (quotientE1 := quotientE1) C0))

/-- The constructed cover-to-quotient Brauer equivalence is equivariant.
The proof is the composite of the cover alignment square, central quotient
inflation/deflation naturality, and the centreless-faithful alignment square. -/
theorem centralIBrBrauer_equivariant
    (source : QuotientRealisationSource (Subgroup.center X)
      coverIota quotientIota)
    (C0 : CentrelessQuotient
      (Xbar := X ⧸ Subgroup.center X))
    (descent : (MulAut X)ᵐᵒᵖ →*
      (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ)
    (hcomm : ∀ (a : (MulAut X)ᵐᵒᵖ) (g : X),
      QuotientGroup.mk' (Subgroup.center X) (a.unop g) =
        (descent a).unop
          (QuotientGroup.mk' (Subgroup.center X) g))
    (a : (MulAut X)ᵐᵒᵖ)
    (phi : CoverBrauer coverIota coverHinj coverBlocks) :
    centralIBrBrauer
        (coverIota := coverIota) (coverHinj := coverHinj)
        (coverBlocks := coverBlocks) (quotientIota := quotientIota)
        (quotientHinj := quotientHinj) (quotientBlocks := quotientBlocks)
        (quotientBlockSource := quotientBlockSource)
        (quotientE1 := quotientE1) source C0
        ((coverBrauerMulAction
          (coverIota := coverIota) (coverHinj := coverHinj)
          (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
          (coverE1 := coverE1)).smul a phi) =
      (quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 descent).smul a
        (centralIBrBrauer
          (coverIota := coverIota) (coverHinj := coverHinj)
          (coverBlocks := coverBlocks) (quotientIota := quotientIota)
          (quotientHinj := quotientHinj) (quotientBlocks := quotientBlocks)
          (quotientBlockSource := quotientBlockSource)
          (quotientE1 := quotientE1) source C0 phi) := by
  let coverAlign :=
    coverBrauerEquivTrivialCentralCharacterFibre coverIota coverHinj
      coverBlocks
  let quotientFibre :=
    quotientIBrEquivTrivialCentralCharacterFibre coverIota quotientIota
      source coverBlocks coverHinj le_rfl
  let faithfulAlign :=
    iBrEquivFaithfulIBrOfCentreless
      (quotientIota := quotientIota) (quotientHinj := quotientHinj)
      (quotientBlocks := quotientBlocks)
      (quotientBlockSource := quotientBlockSource)
      (quotientE1 := quotientE1) C0
  have hcover :=
    coverBrauerEquivTrivialCentralCharacterFibre_equivariant coverIota
      coverHinj coverBlocks coverBlockSource coverE1 descent hcomm a phi
  have hcentral :
      quotientFibre.symm
          ((trivialCentralCharacterFibreMulAction coverIota coverBlocks
            coverHinj le_rfl descent hcomm).smul a (coverAlign phi)) =
        (quotientIBrMulAction quotientIota descent).smul a
          (quotientFibre.symm (coverAlign phi)) := by
    apply quotientFibre.injective
    calc
      quotientFibre (quotientFibre.symm
          ((trivialCentralCharacterFibreMulAction coverIota coverBlocks
            coverHinj le_rfl descent hcomm).smul a (coverAlign phi))) =
        (trivialCentralCharacterFibreMulAction coverIota coverBlocks
          coverHinj le_rfl descent hcomm).smul a (coverAlign phi) :=
        quotientFibre.apply_symm_apply _
      _ = (trivialCentralCharacterFibreMulAction coverIota coverBlocks
          coverHinj le_rfl descent hcomm).smul a
          (quotientFibre (quotientFibre.symm (coverAlign phi))) :=
        congrArg
          (fun psi ↦
            (trivialCentralCharacterFibreMulAction coverIota coverBlocks
              coverHinj le_rfl descent hcomm).smul a psi)
          (quotientFibre.apply_symm_apply (coverAlign phi)).symm
      _ = quotientFibre
          ((quotientIBrMulAction quotientIota descent).smul a
            (quotientFibre.symm (coverAlign phi))) := by
        apply Subtype.ext
        change IrreducibleBrauerCharacter.twist coverIota
            (inflateIBr coverIota quotientIota source
              (quotientFibre.symm (coverAlign phi))) a.unop =
          inflateIBr coverIota quotientIota source
            (IrreducibleBrauerCharacter.twist quotientIota
              (quotientFibre.symm (coverAlign phi)) (descent a).unop)
        exact (inflateIBr_twist_of_quotientSquare coverIota quotientIota
          source a.unop (descent a).unop (hcomm a)
          (quotientFibre.symm (coverAlign phi))).symm
  have hfaithful :=
    iBrEquivFaithfulIBrOfCentreless_equivariant
      (quotientIota := quotientIota) (quotientHinj := quotientHinj)
      (quotientBlocks := quotientBlocks)
      (quotientBlockSource := quotientBlockSource)
      (quotientE1 := quotientE1) C0 descent a
      (quotientFibre.symm (coverAlign phi))
  change faithfulAlign
      (quotientFibre.symm (coverAlign
        ((coverBrauerMulAction
          (coverIota := coverIota) (coverHinj := coverHinj)
          (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
          (coverE1 := coverE1)).smul a phi))) =
    (quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 descent).smul a
      (faithfulAlign (quotientFibre.symm (coverAlign phi)))
  calc
    faithfulAlign
        (quotientFibre.symm (coverAlign
          ((coverBrauerMulAction
            (coverIota := coverIota) (coverHinj := coverHinj)
            (coverBlocks := coverBlocks)
            (coverBlockSource := coverBlockSource)
            (coverE1 := coverE1)).smul a phi))) =
      faithfulAlign
        (quotientFibre.symm
          ((trivialCentralCharacterFibreMulAction coverIota coverBlocks
            coverHinj le_rfl descent hcomm).smul a (coverAlign phi))) :=
      congrArg (fun psi ↦ faithfulAlign (quotientFibre.symm psi)) hcover
    _ = faithfulAlign
        ((quotientIBrMulAction quotientIota descent).smul a
          (quotientFibre.symm (coverAlign phi))) :=
      congrArg faithfulAlign hcentral
    _ = (quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 descent).smul a
        (faithfulAlign (quotientFibre.symm (coverAlign phi))) := hfaithful

/-! ## The exact six-field residual source -/

/-- All non-Brauer fields still required by `CarrierTransport`.

The record is indexed by the already constructed `centralIBrBrauer`, so it
cannot choose or replace that equivalence.  The first five fields are E1/U
carrier, action, and block data.  `pair_of_quotient` is the remaining E2/U
character-triple implication. -/
structure RemainingCarrierTransport
    (source : QuotientRealisationSource (Subgroup.center X)
      coverIota quotientIota)
    (C0 : CentrelessQuotient
      (Xbar := X ⧸ Subgroup.center X))
    (descent : (MulAut X)ᵐᵒᵖ →*
      (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ)
    (ModularCharacterTriple :
      IBr coverIota → WeightClass (p := p) (K := K) (X := X) → Prop)
    (QuotientPair :
      QuotientBrauer quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1 →
        QuotientWeight quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1 → Prop) where
  weight :
    CoverWeight coverBlockSource ≃
      QuotientWeight quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1
  block :
    Fibre (blockSector (k := k) (X := X))
        (1 : CentralSector (k := k) (X := X)) ≃
      _root_.ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.ActualBlock
        (k := k) (X := X ⧸ Subgroup.center X)
  weight_equivariant : ∀ (a : (MulAut X)ᵐᵒᵖ)
      (w : CoverWeight coverBlockSource),
    weight
        ((coverWeightMulAction
          (coverIota := coverIota) (coverHinj := coverHinj)
          (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
          (coverE1 := coverE1)).smul a w) =
      (quotientWeightMulAction quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 descent).smul a (weight w)
  brauer_block : ∀ phi : CoverBrauer coverIota coverHinj coverBlocks,
    block (coverBrauerBlock coverIota coverHinj coverBlocks phi) =
      quotientBrauerBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1
        (centralIBrBrauer
          (coverIota := coverIota) (coverHinj := coverHinj)
          (coverBlocks := coverBlocks) (quotientIota := quotientIota)
          (quotientHinj := quotientHinj) (quotientBlocks := quotientBlocks)
          (quotientBlockSource := quotientBlockSource)
          (quotientE1 := quotientE1) source C0 phi)
  weight_block : ∀ w : CoverWeight coverBlockSource,
    block (coverWeightBlock coverBlockSource w) =
      quotientWeightBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 (weight w)
  pair_of_quotient : ∀ (phi : CoverBrauer coverIota coverHinj coverBlocks)
      (w : CoverWeight coverBlockSource),
    QuotientPair
        (centralIBrBrauer
          (coverIota := coverIota) (coverHinj := coverHinj)
          (coverBlocks := coverBlocks) (quotientIota := quotientIota)
          (quotientHinj := quotientHinj) (quotientBlocks := quotientBlocks)
          (quotientBlockSource := quotientBlockSource)
          (quotientE1 := quotientE1) source C0 phi)
        (weight w) →
      CoverPair coverIota coverHinj coverBlocks coverBlockSource
        ModularCharacterTriple phi w

/-- Fill the two Brauer fields of `CarrierTransport` by kernel construction
and copy exactly the six independent residual fields. -/
def carrierTransport_ofCentralIBr
    (source : QuotientRealisationSource (Subgroup.center X)
      coverIota quotientIota)
    (C0 : CentrelessQuotient
      (Xbar := X ⧸ Subgroup.center X))
    (descent : (MulAut X)ᵐᵒᵖ →*
      (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ)
    (hcomm : ∀ (a : (MulAut X)ᵐᵒᵖ) (g : X),
      QuotientGroup.mk' (Subgroup.center X) (a.unop g) =
        (descent a).unop
          (QuotientGroup.mk' (Subgroup.center X) g))
    (ModularCharacterTriple :
      IBr coverIota → WeightClass (p := p) (K := K) (X := X) → Prop)
    (QuotientPair :
      QuotientBrauer quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1 →
        QuotientWeight quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1 → Prop)
    (R : RemainingCarrierTransport coverIota coverHinj coverBlocks
      coverBlockSource coverE1 quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 source C0 descent ModularCharacterTriple
      QuotientPair) :
    @CarrierTransport
      (MulAut X)ᵐᵒᵖ
      (CoverBrauer coverIota coverHinj coverBlocks)
      (CoverWeight coverBlockSource)
      (QuotientBrauer quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (QuotientWeight quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (Fibre (blockSector (k := k) (X := X))
        (1 : CentralSector (k := k) (X := X)))
      (_root_.ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.ActualBlock
        (k := k) (X := X ⧸ Subgroup.center X))
      (inferInstance : Monoid (MulAut X)ᵐᵒᵖ)
      (coverBrauerMulAction
        (coverIota := coverIota) (coverHinj := coverHinj)
        (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
        (coverE1 := coverE1))
      (coverWeightMulAction
        (coverIota := coverIota) (coverHinj := coverHinj)
        (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
        (coverE1 := coverE1))
      (quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 descent)
      (quotientWeightMulAction quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 descent)
      (coverBrauerBlock coverIota coverHinj coverBlocks)
      (coverWeightBlock coverBlockSource)
      (quotientBrauerBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (quotientWeightBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (CoverPair coverIota coverHinj coverBlocks coverBlockSource
        ModularCharacterTriple)
      QuotientPair := by
  letI : MulAction (MulAut X)ᵐᵒᵖ
      (CoverBrauer coverIota coverHinj coverBlocks) :=
    coverBrauerMulAction
      (coverIota := coverIota) (coverHinj := coverHinj)
      (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
      (coverE1 := coverE1)
  letI : MulAction (MulAut X)ᵐᵒᵖ (CoverWeight coverBlockSource) :=
    coverWeightMulAction
      (coverIota := coverIota) (coverHinj := coverHinj)
      (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
      (coverE1 := coverE1)
  letI : MulAction (MulAut X)ᵐᵒᵖ
      (QuotientBrauer quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1) :=
    quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 descent
  letI : MulAction (MulAut X)ᵐᵒᵖ
      (QuotientWeight quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1) :=
    quotientWeightMulAction quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 descent
  exact
    { brauer := centralIBrBrauer
        (coverIota := coverIota) (coverHinj := coverHinj)
        (coverBlocks := coverBlocks) (quotientIota := quotientIota)
        (quotientHinj := quotientHinj) (quotientBlocks := quotientBlocks)
        (quotientBlockSource := quotientBlockSource)
        (quotientE1 := quotientE1) source C0
      weight := R.weight
      block := R.block
      brauer_equivariant := centralIBrBrauer_equivariant
        (coverIota := coverIota) (coverHinj := coverHinj)
        (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
        (coverE1 := coverE1) (quotientIota := quotientIota)
        (quotientHinj := quotientHinj) (quotientBlocks := quotientBlocks)
        (quotientBlockSource := quotientBlockSource)
        (quotientE1 := quotientE1) source C0 descent hcomm
      weight_equivariant := R.weight_equivariant
      brauer_block := R.brauer_block
      weight_block := R.weight_block
      pair_of_quotient := R.pair_of_quotient }

end ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientIBrFactory


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
