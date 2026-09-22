import ModularRep.PaperProofs.CentralEllPrimeTrivialSectorTransportAdapter
import ModularRep.PaperProofs.SporadicFi24TrivialFaithfulSectorGlue

/-!
# Specialising central-quotient transport to the Fischer trivial sector

This module derives the trivial-sector source consumed by the Fischer sector
glue.  Its inputs are kept in three independent layers:

* a one-faithful-sector source on a centreless quotient;
* a descent homomorphism for the automorphism action; and
* E1/U carrier-level Brauer, weight, action, and block diagrams, together with
  the E2/U pair bridge and character-triple data.

The quotient correspondence is constructed by `lemma_5_5_actual`.  The cover
correspondence is then constructed by conjugating it through the carrier
equivalences.  In particular, no cover-side character--weight equivalence or
selected cover-side block/pair conclusion is an input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientSpecialisation

open Formalisation
open Formalisation.IBAW
open ModularRep.PaperProofs.CentralEllPrimeTrivialSectorTransportAdapter
open ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Actual
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24TrivialFaithfulSectorGlue

universe u

variable {p : ℕ} {k K X Xbar : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Group Xbar] [Fintype Xbar]

noncomputable local instance coverCenterFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

noncomputable local instance quotientCenterFintype :
    Fintype (Subgroup.center Xbar) :=
  Fintype.ofFinite _

variable (coverIota : PrimeRegularRootEmbedding p k K X)
variable (coverHinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity coverIota)
variable {CoverBlockIndex : Type u} [Fintype CoverBlockIndex]
variable {coverBlockIdempotent : CoverBlockIndex → k[X]}
variable (coverBlocks : BlockIdempotentDecomposition coverBlockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (coverBlockSource : LiteralCarrierAdapter
  (p := p) (k := k) (K := K) (X := X))
variable (coverE1 : RoutineTransportInput coverIota coverHinj coverBlocks
  coverBlockSource)

variable (quotientIota : PrimeRegularRootEmbedding p k K Xbar)
variable (quotientHinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity quotientIota)
variable {QuotientBlockIndex : Type u} [Fintype QuotientBlockIndex]
variable {quotientBlockIdempotent : QuotientBlockIndex → k[Xbar]}
variable (quotientBlocks :
  BlockIdempotentDecomposition quotientBlockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center Xbar) : k)]
variable (quotientBlockSource : LiteralCarrierAdapter
  (p := p) (k := k) (K := K) (X := Xbar))
variable (quotientE1 : RoutineTransportInput quotientIota quotientHinj
  quotientBlocks quotientBlockSource)

/-- The literal trivial Brauer fibre on the covering group. -/
abbrev CoverBrauer :=
  Fibre (brauerSector coverIota coverHinj coverBlocks)
    (1 : CentralSector (k := k) (X := X))

/-- The literal trivial weight fibre on the covering group. -/
abbrev CoverWeight :=
  Fibre (weightSector (R := coverBlockSource))
    (1 : CentralSector (k := k) (X := X))

/-- The primitive blocks of the covering group in the trivial central
sector.  Only these blocks descend to the central quotient. -/
abbrev CoverTrivialBlock :=
  Fibre (blockSector (k := k) (X := X))
    (1 : CentralSector (k := k) (X := X))

/-- The faithful Brauer carrier on the quotient.  Centrelessness makes this
the quotient's unique central sector. -/
abbrev QuotientBrauer :=
  FaithfulIBr quotientIota quotientHinj quotientBlocks quotientBlockSource
    quotientE1

/-- The faithful set of weights on the quotient. -/
abbrev QuotientWeight :=
  FaithfulWeight quotientIota quotientHinj quotientBlocks quotientBlockSource
    quotientE1

/-- Cover-side Brauer block label restricted to the trivial fibre. -/
def coverBrauerBlock
    (phi : CoverBrauer coverIota coverHinj coverBlocks) :
    CoverTrivialBlock (k := k) (X := X) :=
  ⟨brauerBlock coverIota coverHinj coverBlocks phi.1, by
    change brauerSector coverIota coverHinj coverBlocks phi.1 = 1
    exact phi.2⟩

/-- Cover-side induced weight block restricted to the trivial fibre. -/
def coverWeightBlock
    (w : CoverWeight coverBlockSource) :
    CoverTrivialBlock (k := k) (X := X) :=
  ⟨coverBlockSource.1.weightBlock w.1, by
    change weightSector (R := coverBlockSource) w.1 = 1
    exact w.2⟩

/-- Quotient-side Brauer block label on the faithful carrier. -/
def quotientBrauerBlock
    (phi : QuotientBrauer quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1) :
    ActualBlock (k := k) (X := Xbar) :=
  faithfulBrauerBlock quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1 phi

/-- Quotient-side induced weight block on the faithful carrier. -/
def quotientWeightBlock
    (w : QuotientWeight quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1) :
    ActualBlock (k := k) (X := Xbar) :=
  faithfulWeightBlock quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1 w

/-- Restrict the intended cover pair predicate to the trivial fibres. -/
abbrev CoverPair
    (ModularCharacterTriple :
      IBr coverIota → WeightClass (p := p) (K := K) (X := X) → Prop)
    (phi : CoverBrauer coverIota coverHinj coverBlocks)
    (w : CoverWeight coverBlockSource) : Prop :=
  ModularCharacterTriple phi.1 w.1

/-- A source-neutral witness that the chosen quotient carrier is centreless. -/
structure CentrelessQuotient : Prop where
  center_eq_one : ∀ z : Subgroup.center Xbar, z = 1

omit [IsAlgClosed k]
  [Invertible (Fintype.card (Subgroup.center Xbar) : k)] [Fintype Xbar] in
/-- A centreless quotient has only one faithful central-sector label. -/
theorem faithfulSector_unique (C : CentrelessQuotient (Xbar := Xbar))
    (mu nu : FaithfulSector (k := k) (X := Xbar)) :
    mu = nu := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro z
  simp [C.center_eq_one z]

/-- On a centreless quotient the transporter between central sectors can be
chosen canonically to be the identity.  This rebuilds the one-sector source
while discarding any externally chosen transporter. -/
def centrelessOneSectorSource
    (C0 : CentrelessQuotient (Xbar := Xbar))
    (QuotientPair :
      QuotientBrauer quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1 →
        QuotientWeight quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1 → Prop)
    (quotientPair_equivariant :
      PairPropertyEquivariant
        (A := (MulAut Xbar)ᵐᵒᵖ)
        (X := QuotientBrauer quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1)
        (Y := QuotientWeight quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1) QuotientPair)
    (AD : AnDietrichFaithfulSectorSource quotientIota quotientHinj
      quotientBlocks quotientBlockSource quotientE1 QuotientPair
      quotientPair_equivariant) :
    AnDietrichFaithfulSectorSource quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 QuotientPair
      quotientPair_equivariant where
  baseSector := AD.baseSector
  transporter := fun _ => 1
  transporter_spec sector := by
    rw [one_smul]
    exact faithfulSector_unique C0 AD.baseSector sector
  baseEquiv := AD.baseEquiv
  baseEquivariant := AD.baseEquivariant
  baseBlockInduction := AD.baseBlockInduction
  characterTriple_of_stabilizer_eq := AD.characterTriple_of_stabilizer_eq

/-- The action on the cover's trivial Brauer fibre, written with exactly the
`stabilizerFibreEquiv` operation used by `TrivialSectorQuotientSource`. -/
@[instance_reducible]
def coverBrauerMulAction :
    MulAction (MulAut X)ᵐᵒᵖ
      (CoverBrauer coverIota coverHinj coverBlocks) where
  smul a phi :=
    stabilizerFibreEquiv
      (brauerSector coverIota coverHinj coverBlocks)
      (brauerSector_equivariant coverIota coverHinj coverBlocks coverE1)
      (1 : CentralSector (k := k) (X := X)) a
      (smul_trivialSector (k := k) (X := X) a) phi
  one_smul phi := by
    apply Subtype.ext
    exact one_smul _ phi.1
  mul_smul a b phi := by
    apply Subtype.ext
    exact mul_smul a b phi.1

/-- The analogous action on the cover's trivial weight fibre. -/
@[instance_reducible]
def coverWeightMulAction :
    MulAction (MulAut X)ᵐᵒᵖ (CoverWeight coverBlockSource) where
  smul a w :=
    stabilizerFibreEquiv
      (weightSector (R := coverBlockSource))
      (weightSector_equivariant_actual
        (iota := coverIota) (hinj := coverHinj) (blocks := coverBlocks)
        (R := coverBlockSource) coverE1)
      (1 : CentralSector (k := k) (X := X)) a
      (smul_trivialSector (k := k) (X := X) a) w
  one_smul w := by
    apply Subtype.ext
    exact one_smul _ w.1
  mul_smul a b w := by
    apply Subtype.ext
    exact mul_smul a b w.1

/-- Restrict the quotient Brauer action along the automorphism-descent
homomorphism. -/
@[instance_reducible]
def quotientBrauerMulAction
    (autDescent : (MulAut X)ᵐᵒᵖ →* (MulAut Xbar)ᵐᵒᵖ) :
    MulAction (MulAut X)ᵐᵒᵖ
      (QuotientBrauer quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1) :=
  MulAction.compHom _ autDescent

/-- Restrict the quotient weight action along the same descent
homomorphism. -/
@[instance_reducible]
def quotientWeightMulAction
    (autDescent : (MulAut X)ᵐᵒᵖ →* (MulAut Xbar)ᵐᵒᵖ) :
    MulAction (MulAut X)ᵐᵒᵖ
      (QuotientWeight quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1) :=
  MulAction.compHom _ autDescent

section Specialisation

variable (autDescent : (MulAut X)ᵐᵒᵖ →* (MulAut Xbar)ᵐᵒᵖ)

variable (ModularCharacterTriple :
  IBr coverIota → WeightClass (p := p) (K := K) (X := X) → Prop)
variable (QuotientPair :
  QuotientBrauer quotientIota quotientHinj quotientBlocks quotientBlockSource
      quotientE1 →
    QuotientWeight quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 → Prop)
variable (quotientPair_equivariant :
  PairPropertyEquivariant
    (A := (MulAut Xbar)ᵐᵒᵖ)
    (X := QuotientBrauer quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1)
    (Y := QuotientWeight quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1) QuotientPair)

variable (C0 : CentrelessQuotient (Xbar := Xbar))
variable (AD : AnDietrichFaithfulSectorSource quotientIota quotientHinj
  quotientBlocks quotientBlockSource quotientE1 QuotientPair
  quotientPair_equivariant)

/-- The quotient-side correspondence is an output of the centreless
sector transport construction, restricted along automorphism descent. -/
def quotientCorrespondence :
    @QuotientCorrespondence
      (MulAut X)ᵐᵒᵖ
      (QuotientBrauer quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (QuotientWeight quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (ActualBlock (k := k) (X := Xbar))
      (inferInstance : Monoid (MulAut X)ᵐᵒᵖ)
      (quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 autDescent)
      (quotientWeightMulAction quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1 autDescent)
      (quotientBrauerBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (quotientWeightBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      QuotientPair := by
  letI : MulAction (MulAut X)ᵐᵒᵖ
      (QuotientBrauer quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1) :=
    quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 autDescent
  letI : MulAction (MulAut X)ᵐᵒᵖ
      (QuotientWeight quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1) :=
    quotientWeightMulAction quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 autDescent
  let AD0 := centrelessOneSectorSource quotientIota quotientHinj
    quotientBlocks quotientBlockSource quotientE1 C0 QuotientPair
    quotientPair_equivariant AD
  let L := lemma_5_5_actual quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1 QuotientPair quotientPair_equivariant AD0
  refine
    { equiv := L.equiv
      equivariant := ?_
      block_compatible := L.blockPreservation
      pair := L.characterTriple }
  intro a phi
  change L.equiv (autDescent a • phi) = autDescent a • L.equiv phi
  exact L.automorphismTransport (autDescent a) phi

variable (T : @CarrierTransport
  (MulAut X)ᵐᵒᵖ
  (CoverBrauer coverIota coverHinj coverBlocks)
  (CoverWeight coverBlockSource)
  (QuotientBrauer quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1)
  (QuotientWeight quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1)
  (CoverTrivialBlock (k := k) (X := X))
  (ActualBlock (k := k) (X := Xbar))
  (inferInstance : Monoid (MulAut X)ᵐᵒᵖ)
  (coverBrauerMulAction (coverIota := coverIota) (coverHinj := coverHinj)
    (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
    (coverE1 := coverE1))
  (coverWeightMulAction (coverIota := coverIota) (coverHinj := coverHinj)
    (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
    (coverE1 := coverE1))
  (quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1 autDescent)
  (quotientWeightMulAction quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1 autDescent)
  (coverBrauerBlock coverIota coverHinj coverBlocks)
  (coverWeightBlock coverBlockSource)
  (quotientBrauerBlock quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1)
  (quotientWeightBlock quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1)
  (CoverPair coverIota coverHinj coverBlocks coverBlockSource
    ModularCharacterTriple)
  QuotientPair)

/-- Construct the exact trivial-sector source consumed by the Fischer glue.
The equivalence and all three selected-map clauses are outputs. -/
def trivialSectorQuotientSource :
    TrivialSectorQuotientSource coverIota coverHinj coverBlocks
      coverBlockSource coverE1 ModularCharacterTriple := by
  letI : MulAction (MulAut X)ᵐᵒᵖ
      (CoverBrauer coverIota coverHinj coverBlocks) :=
    coverBrauerMulAction (coverIota := coverIota) (coverHinj := coverHinj)
      (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
      (coverE1 := coverE1)
  letI : MulAction (MulAut X)ᵐᵒᵖ (CoverWeight coverBlockSource) :=
    coverWeightMulAction (coverIota := coverIota) (coverHinj := coverHinj)
      (coverBlocks := coverBlocks) (coverBlockSource := coverBlockSource)
      (coverE1 := coverE1)
  letI : MulAction (MulAut X)ᵐᵒᵖ
      (QuotientBrauer quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1) :=
    quotientBrauerMulAction quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 autDescent
  letI : MulAction (MulAut X)ᵐᵒᵖ
      (QuotientWeight quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1) :=
    quotientWeightMulAction quotientIota quotientHinj quotientBlocks
      quotientBlockSource quotientE1 autDescent
  let S := quotientCorrespondence quotientIota quotientHinj quotientBlocks
    quotientBlockSource quotientE1 autDescent QuotientPair
    quotientPair_equivariant C0 AD
  refine
    { equiv := liftedEquiv
        (coverBrauerBlock coverIota coverHinj coverBlocks)
        (coverWeightBlock coverBlockSource)
        (quotientBrauerBlock quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1)
        (quotientWeightBlock quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1)
        (CoverPair coverIota coverHinj coverBlocks coverBlockSource
          ModularCharacterTriple)
        QuotientPair T S
      equivariant := ?_
      blockInduction := ?_
      characterTriple := ?_ }
  · exact liftedEquiv_equivariant
      (coverBrauerBlock coverIota coverHinj coverBlocks)
      (coverWeightBlock coverBlockSource)
      (quotientBrauerBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (quotientWeightBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (CoverPair coverIota coverHinj coverBlocks coverBlockSource
        ModularCharacterTriple)
      QuotientPair T S
  · intro phi
    exact congrArg Subtype.val
      (liftedEquiv_block_compatible
        (coverBrauerBlock coverIota coverHinj coverBlocks)
        (coverWeightBlock coverBlockSource)
        (quotientBrauerBlock quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1)
        (quotientWeightBlock quotientIota quotientHinj quotientBlocks
          quotientBlockSource quotientE1)
        (CoverPair coverIota coverHinj coverBlocks coverBlockSource
          ModularCharacterTriple)
        QuotientPair T S phi)
  · exact liftedEquiv_pair
      (coverBrauerBlock coverIota coverHinj coverBlocks)
      (coverWeightBlock coverBlockSource)
      (quotientBrauerBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (quotientWeightBlock quotientIota quotientHinj quotientBlocks
        quotientBlockSource quotientE1)
      (CoverPair coverIota coverHinj coverBlocks coverBlockSource
        ModularCharacterTriple)
      QuotientPair T S

end Specialisation

end ModularRep.PaperProofs.SporadicFi24TrivialSectorQuotientSpecialisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
