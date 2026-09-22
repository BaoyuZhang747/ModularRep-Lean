import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefectCounts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphisms

/-! Conditional Baby-odd join retaining the actual universal double cover.
The intended numerical sources are An--Wilson 5.3 and the cyclic numerical
consequence of Spath 6.2. No named carrier or published count is instantiated. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyOddFullCover

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefectCounts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphisms

universe u
variable {p : ℕ} {k K X S : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Group S] [Fintype S]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

theorem exists_definition41_of_full_cover_and_baby_odd_sources
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (hpne : p ≠ 2)
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hkernel : Nat.card q.ker = 2)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hOuter : Nat.card ((MulAut S)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := S)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_two iota.prime hpne q hq hs hna hkernel))
    (fieldSource : SpathCoefficientField p k iota.prime) :
    let Cover := ellPrimeCover_of_fullCover_kernel_two iota.prime hpne q hq hs hna hkernel
    Nonempty (Definition41Witness iota hinj R C Cover D T) := by
  exact SporadicFi24P3Definition44NamedCarrierOriginalDefectCounts.exists_definition41_of_defect_counts
    iota hinj R C (ellPrimeCover_of_fullCover_kernel_two iota.prime hpne q hq hs hna hkernel)
    (allInner_of_fullCover_of_outer_card_one q hq hs hna hOuter) D T source
    compatibility lower fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyOddFullCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
