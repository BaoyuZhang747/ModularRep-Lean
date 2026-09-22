import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

/-! Structural specialization of the centreless numerical criterion.
The actual universal covering map has kernel of order one, and the literal
outer quotient has order one. These equations do not identify an arbitrary
carrier with J4; the exact source binding remains in the ledger. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

universe u

private theorem innerInverseOpRange_normal
    {X : Type u} [Group X] :
    (RepresentationWeight.innerInverseOpHom (G := X)).range.Normal := by
  constructor
  intro beta hbeta alpha
  rcases hbeta with ⟨x, rfl⟩
  refine ⟨(alpha.unop⁻¹) x, ?_⟩
  apply MulOpposite.unop_injective
  ext y
  simp [RepresentationWeight.innerInverseOpHom, mul_assoc]

theorem allAutomorphismsInner_of_outer_card_one
    {X : Type u} [Group X]
    (hOuter :
      Nat.card ((MulAut X)ᵐᵒᵖ ⧸
        (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1) :
    AllAutomorphismsInner (X := X) := by
  let N := (RepresentationWeight.innerInverseOpHom (G := X)).range
  let : N.Normal := innerInverseOpRange_normal
  let : Subsingleton ((MulAut X)ᵐᵒᵖ ⧸ N) :=
    (Nat.card_eq_one_iff_unique.mp hOuter).1
  refine ⟨?_⟩
  intro alpha
  have hmem : MulOpposite.op alpha ∈ N := by
    apply (QuotientGroup.eq_one_iff (MulOpposite.op alpha)).mp
    exact Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x⁻¹, (congrArg MulOpposite.unop hx).symm⟩

def identityEllPrimeCover_of_fullCover_kernel_card_one
    {p : ℕ} (hp : p.Prime)
    {U X : Type u} [Group U] [Group X] [Fintype X]
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 1)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X) :
    EllPrimeCoverSource p X :=
  identityEllPrimeCover_of_fullCover_pKernel hp cover hcover
    (IsPGroup.of_card (n := 0) (by simpa using hkernel)) hsimple hnonabelian

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
    (localReduction : ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
      SelectedLocalReductionSource R.1 b w)
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 1)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    let Cover := identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian
    let hc := center_eq_bot_of_nonabelian_simple hsimple hnonabelian
    Nonempty (Definition41Witness iota hinj R localReduction Cover hc D T) := by
  exact exists_definition41_of_defect_counts iota hinj R localReduction
    (identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian)
    (center_eq_bot_of_nonabelian_simple hsimple hnonabelian)
    (allAutomorphismsInner_of_outer_card_one hOuter) D T source compatibility fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
