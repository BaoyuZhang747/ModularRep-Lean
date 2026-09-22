import Mathlib

/-!
# Transporting a one-sector correspondence through carrier equivalences

This source-neutral module isolates the formal diagram used when a
correspondence on a central quotient is transported to the trivial central
sector of a cover.  It does not construct any quotient, character, weight, or
block object.  In particular, it contains no family of central sectors and no
global correspondence conclusion.

The quotient-side correspondence and the carrier transport are deliberately
separate.  Thus a cover-side character--weight equivalence is an output, not a
field of the transport source.  Equivariance, block compatibility, and the
chosen pair property are then consequences of commuting diagrams.
-/

noncomputable section

namespace ModularRep.PaperProofs.CentralEllPrimeTrivialSectorTransportAdapter

universe u

variable {A CoverBrauer CoverWeight QuotientBrauer QuotientWeight : Type u}
variable {CoverBlock QuotientBlock : Type u}
variable [Monoid A]
variable [MulAction A CoverBrauer] [MulAction A CoverWeight]
variable [MulAction A QuotientBrauer] [MulAction A QuotientWeight]

variable (coverBrauerBlock : CoverBrauer → CoverBlock)
variable (coverWeightBlock : CoverWeight → CoverBlock)
variable (quotientBrauerBlock : QuotientBrauer → QuotientBlock)
variable (quotientWeightBlock : QuotientWeight → QuotientBlock)
variable (CoverPair : CoverBrauer → CoverWeight → Prop)
variable (QuotientPair : QuotientBrauer → QuotientWeight → Prop)

/-- Carrier-level central-quotient transport.

The two carrier equivalences, their action squares, and the two block-label
squares are E1/U and independent of any character--weight correspondence.
The final E2/U field transports only the pair predicate, for an arbitrary
pair; it does not state that any selected pair satisfies that predicate. -/
structure CarrierTransport where
  brauer : CoverBrauer ≃ QuotientBrauer
  weight : CoverWeight ≃ QuotientWeight
  block : CoverBlock ≃ QuotientBlock
  brauer_equivariant : ∀ (a : A) (phi : CoverBrauer),
    brauer (a • phi) = a • brauer phi
  weight_equivariant : ∀ (a : A) (w : CoverWeight),
    weight (a • w) = a • weight w
  brauer_block : ∀ phi : CoverBrauer,
    block (coverBrauerBlock phi) = quotientBrauerBlock (brauer phi)
  weight_block : ∀ w : CoverWeight,
    block (coverWeightBlock w) = quotientWeightBlock (weight w)
  pair_of_quotient : ∀ (phi : CoverBrauer) (w : CoverWeight),
    QuotientPair (brauer phi) (weight w) → CoverPair phi w

/-- A selected correspondence already constructed on the quotient carrier.
It has no cover-side field and therefore cannot assume the desired transported
equivalence. -/
structure QuotientCorrespondence where
  equiv : QuotientBrauer ≃ QuotientWeight
  equivariant : ∀ (a : A) (phi : QuotientBrauer),
    equiv (a • phi) = a • equiv phi
  block_compatible : ∀ phi : QuotientBrauer,
    quotientWeightBlock (equiv phi) = quotientBrauerBlock phi
  pair : ∀ phi : QuotientBrauer,
    QuotientPair phi (equiv phi)

variable
  (T : CarrierTransport (A := A) coverBrauerBlock coverWeightBlock
    quotientBrauerBlock quotientWeightBlock CoverPair QuotientPair)
  (S : QuotientCorrespondence (A := A) quotientBrauerBlock
    quotientWeightBlock QuotientPair)

/-- The cover-side equivalence is the quotient correspondence conjugated by
the two carrier equivalences. -/
def liftedEquiv : CoverBrauer ≃ CoverWeight :=
  T.brauer.trans (S.equiv.trans T.weight.symm)

@[simp]
theorem weight_liftedEquiv (phi : CoverBrauer) :
    T.weight
        (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
          quotientWeightBlock CoverPair QuotientPair T S phi) =
      S.equiv (T.brauer phi) := by
  exact T.weight.apply_symm_apply (S.equiv (T.brauer phi))

/-- Equivariance of the lifted map is a commuting-square consequence. -/
theorem liftedEquiv_equivariant (a : A) (phi : CoverBrauer) :
    liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
        quotientWeightBlock CoverPair QuotientPair T S (a • phi) =
      a • liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
        quotientWeightBlock CoverPair QuotientPair T S phi := by
  apply T.weight.injective
  calc
    T.weight
        (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
          quotientWeightBlock CoverPair QuotientPair T S (a • phi)) =
        S.equiv (T.brauer (a • phi)) :=
      weight_liftedEquiv coverBrauerBlock coverWeightBlock
        quotientBrauerBlock quotientWeightBlock CoverPair QuotientPair T S
        (a • phi)
    _ = S.equiv (a • T.brauer phi) := by
      rw [T.brauer_equivariant]
    _ = a • S.equiv (T.brauer phi) := S.equivariant a (T.brauer phi)
    _ = a • T.weight
        (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
          quotientWeightBlock CoverPair QuotientPair T S phi) := by
      rw [weight_liftedEquiv coverBrauerBlock coverWeightBlock
        quotientBrauerBlock quotientWeightBlock CoverPair QuotientPair]
    _ = T.weight
        (a • liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
          quotientWeightBlock CoverPair QuotientPair T S phi) := by
      rw [T.weight_equivariant]

/-- Cover-side block compatibility follows by applying the injective block
transport and chasing the two block-label squares. -/
theorem liftedEquiv_block_compatible (phi : CoverBrauer) :
    coverWeightBlock
        (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
          quotientWeightBlock CoverPair QuotientPair T S phi) =
      coverBrauerBlock phi := by
  apply T.block.injective
  calc
    T.block (coverWeightBlock
        (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
          quotientWeightBlock CoverPair QuotientPair T S phi)) =
        quotientWeightBlock (T.weight
          (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
            quotientWeightBlock CoverPair QuotientPair T S phi)) :=
      T.weight_block
        (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
          quotientWeightBlock CoverPair QuotientPair T S phi)
    _ = quotientWeightBlock (S.equiv (T.brauer phi)) := by
      rw [weight_liftedEquiv coverBrauerBlock coverWeightBlock
        quotientBrauerBlock quotientWeightBlock CoverPair QuotientPair]
    _ = quotientBrauerBlock (T.brauer phi) :=
      S.block_compatible (T.brauer phi)
    _ = T.block (coverBrauerBlock phi) := (T.brauer_block phi).symm

/-- The quotient pair property transports to every pair selected by the
lifted correspondence. -/
theorem liftedEquiv_pair (phi : CoverBrauer) :
    CoverPair phi
      (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
        quotientWeightBlock CoverPair QuotientPair T S phi) := by
  apply T.pair_of_quotient phi
    (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
      quotientWeightBlock CoverPair QuotientPair T S phi)
  rw [weight_liftedEquiv coverBrauerBlock coverWeightBlock
    quotientBrauerBlock quotientWeightBlock CoverPair QuotientPair]
  exact S.pair (T.brauer phi)

/-- The three clauses consumed together with the lifted equivalence.  This is
an output record: it is constructed from `CarrierTransport` and
`QuotientCorrespondence`, never accepted as a source. -/
structure LiftedClauses (equiv : CoverBrauer ≃ CoverWeight) : Prop where
  equivariant : ∀ (a : A) (phi : CoverBrauer),
    equiv (a • phi) = a • equiv phi
  block_compatible : ∀ phi : CoverBrauer,
    coverWeightBlock (equiv phi) = coverBrauerBlock phi
  pair : ∀ phi : CoverBrauer,
    CoverPair phi (equiv phi)

/-- Package the kernel-derived cover clauses without introducing any new
source hypothesis. -/
theorem liftedClauses :
    LiftedClauses (A := A) coverBrauerBlock coverWeightBlock CoverPair
      (liftedEquiv coverBrauerBlock coverWeightBlock quotientBrauerBlock
        quotientWeightBlock CoverPair QuotientPair T S) where
  equivariant := liftedEquiv_equivariant coverBrauerBlock coverWeightBlock
    quotientBrauerBlock quotientWeightBlock CoverPair QuotientPair T S
  block_compatible := liftedEquiv_block_compatible coverBrauerBlock
    coverWeightBlock quotientBrauerBlock quotientWeightBlock CoverPair
    QuotientPair T S
  pair := liftedEquiv_pair coverBrauerBlock coverWeightBlock
    quotientBrauerBlock quotientWeightBlock CoverPair QuotientPair T S

end ModularRep.PaperProofs.CentralEllPrimeTrivialSectorTransportAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
