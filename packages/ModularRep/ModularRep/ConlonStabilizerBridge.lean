import ModularRep.IntegralBasicSetBridge
import ModularRep.PaperProofs.ConlonBasicSet
import Mathlib.Tactic

/-!
# Small stabilisers and the Conlon basic set bridge

This file formalises the final abstract inference used in manuscript Lemma
4.2 and Proposition 3.11.  A finite group with a normal subgroup of order at
most two whose quotient embeds in a cyclic group is `2`-hypoelementary.  The
integral basic set argument can therefore be applied to that group using the
separate Conlon mark detection and Burnside mark injectivity inputs.

The file does not construct the block stabiliser, its small normal subgroup,
the quotient embedding, the integral basic set, or either cited mark theorem.
-/

namespace ModularRep.ManuscriptVerification.ConlonStabilizerBridge

open ModularRep.IntegralBasicSetBridge
open ModularRep.PaperProofs.ConlonBasicSet

universe u

variable {A X Y : Type u} [Group A] [MulAction A X] [MulAction A Y]

/-- A normal subgroup of order at most two whose quotient embeds in a cyclic
group makes the ambient finite group `2`-hypoelementary. -/
theorem isTwoHypoelementary_of_small_normal_quotient_embedding
    [Finite A]
    (D : Subgroup A) [D.Normal]
    (hcard : Nat.card D <= 2)
    {C : Type*} [Group C] [IsCyclic C]
    (quotientEmbedding : A ⧸ D →* C)
    (quotientEmbedding_injective : Function.Injective quotientEmbedding) :
    IsPHypoelementary 2 A := by
  have hcard_pos : 0 < Nat.card D := Nat.card_pos
  have hcard_cases : Nat.card D = 1 ∨ Nat.card D = 2 := by
    omega
  have hD : IsPGroup 2 D := by
    rcases hcard_cases with hcard_one | hcard_two
    · exact IsPGroup.of_card (n := 0) (by simpa using hcard_one)
    · exact IsPGroup.of_card (n := 1) (by simpa using hcard_two)
  have hDcore : D <= ModularRep.pCore 2 A :=
    ModularRep.normal_pSubgroup_le_pCore 2 D hD
  let _ : IsCyclic (A ⧸ D) :=
    isCyclic_of_injective quotientEmbedding quotientEmbedding_injective
  let quotientMap : A ⧸ D →* A ⧸ ModularRep.pCore 2 A :=
    QuotientGroup.map D (ModularRep.pCore 2 A) (MonoidHom.id A) (by
      simpa using hDcore)
  exact isCyclic_of_surjective quotientMap (by
    apply QuotientGroup.map_surjective_of_surjective
    simpa using QuotientGroup.mk'_surjective (ModularRep.pCore 2 A))

/-- The complete abstract inference used after the stabiliser calculation:
the small normal subgroup proves the `2`-hypoelementary hypothesis, and the
source-shaped Conlon and Burnside inputs turn the equivariant integral basic
set into an equivariant bijection of its indexing sets. -/
theorem equivariantSetEquiv_of_small_normal_quotient_embedding
    [Finite A] [Finite X] [Finite Y]
    (D : Subgroup A) [D.Normal]
    (hcard : Nat.card D <= 2)
    {C : Type*} [Group C] [IsCyclic C]
    (quotientEmbedding : A ⧸ D →* C)
    (quotientEmbedding_injective : Function.Injective quotientEmbedding)
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (hd : MatrixEquivariant (A := A) d.toLinearMap)
    (conlon : PadicConlonMarkDetection.{u, u} (p := 2) (A := A))
    (burnside : PublishedBurnsideMarkInjectivity.{u, u} (A := A)) :
    ∃ e : X ≃ Y, IsEquivariantSetEquiv (A := A) e := by
  let integralLatticeEquiv := permutationLatticeEquiv d hd
  exact corollary_2_4_conlonMark
    (isTwoHypoelementary_of_small_normal_quotient_embedding
      D hcard quotientEmbedding quotientEmbedding_injective)
    ⟨permutationLatticeEquivBaseChange
      (S := ℤ_[2]) integralLatticeEquiv⟩ conlon burnside

end ModularRep.ManuscriptVerification.ConlonStabilizerBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
