import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4Numerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

/-! Structural specialization of the centreless numerical criterion.
The actual universal covering map has kernel of order one, and the literal
outer quotient has order one. These equations do not identify an arbitrary
carrier with J4; the exact source binding remains in the ledger. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4FullCover

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

variable {p : ℕ} {k K U X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group U] [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

theorem exists_definition41_of_full_cover_and_defect_counts
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 1)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    let Cover := identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian
    let hc := center_eq_bot_of_nonabelian_simple hsimple hnonabelian
    Nonempty (Definition41Witness iota hinj R C Cover hc D T) := by
  exact SporadicFi24P3Definition44NamedCarrierCanonicalJ4Numerical.exists_definition41_of_defect_counts iota hinj R C
    (identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian)
    (center_eq_bot_of_nonabelian_simple hsimple hnonabelian)
    (allAutomorphismsInner_of_outer_card_one hOuter) D T source compatibility fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4FullCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
