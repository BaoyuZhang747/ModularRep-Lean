import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrderThreeCharacters
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3RadicalSupportGeometry
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3RadicalSupportBlocks

/-! Every role-one weight is supported on the retained order-nine radical.
Its raw subgroup has order one, three or nine. Canonical bottom-weight blocks
exclude one; independent actual quotient degree data exclude three. -/

noncomputable section
set_option maxHeartbeats 4000000
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DerivedRadicalSupport
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData
open SporadicFi24P3Definition44NamedCarrierP3OrderThreeData
open SporadicFi24P3Definition44NamedCarrierP3OrderThreeCharacters
open SporadicFi24P3Definition44NamedCarrierP3RadicalSupportGeometry
open SporadicFi24P3Definition44NamedCarrierP3RadicalSupportBlocks
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierSameMapQOne
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource)

universe u
variable {k K G : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem weight_support_from_order_three_degree_cover
    (iota : PrimeRegularRootEmbedding 3 k K G)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))
    (roles : Fin 3 ≃ ActualBlock (k := k) (X := G))
    (Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ActualOrdinaryDecomposition iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R.1.operations.ambientBlockData.blocks)
    (C : FullOrdinaryDegreeTable K G)
    (allocation : let _ := R.1.operations.ambientBlockData.fintypeBlock
      ∀ r, Dordinary.ordinaryBlock (C.character r) = roles (blockLabels r))
    (Dzero : DefectZeroReductionSource iota)
    (Tzero : TrivialWeightSource (p := 3) (X := G))
    (availability : LocalCanonicalAvailability iota)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (Q : RadicalSubgroup (p := 3) (G := G)) (hQcard : Nat.card Q.1 = 9)
    (h411 : letI := R.1.operations.ambientBlockData.fintypeBlock
      Navarro411CentralBrauerSource R.1.operations.ambientBlockData.blocks (roles 1) Q.1)
    (U : RadicalSubgroup (p := 3) (G := G))
    (orderThreeClassification : ∀ P : RadicalSubgroup (p := 3) (G := G),
      P.1.IsSubconjugate Q.1 → Nat.card P.1 = 3 → P.1.AreConjugate U.1)
    (quotientOrder : Nat.card (NormalizerQuotient U.1) = 29713078886400)
    (quotientDegreeCover : ∀ chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient U.1),
      ∃ r : Fin 125, chi 1 = (quotientDegrees r : K)) :
    ∀ w : ConjugacyClass (p := 3) (K := K) (G := G),
      R.1.weightBlock w = roles 1 → radicalClass w =
        (Quotient.mk'' Q : RadicalConjugacyClass (p := 3) (G := G)) := by
  have hEmpty := local_defectZero_isEmpty U quotientOrder quotientDegreeCover
  intro w
  refine Quotient.inductionOn w ?_
  intro w
  refine Quotient.inductionOn w ?_
  intro W hW
  change R.1.operations.rawWeightBlock W = roles 1 at hW
  let P : RadicalSubgroup (p := 3) (G := G) := ⟨W.subgroup, W.radical⟩
  have hsub : P.1.IsSubconjugate Q.1 :=
    rawWeight_isSubconjugate iota R compatibility (roles 1) Q.1 h411 W
      (rawReductionOfAvailability iota availability W) hW
  rcases card_one_or_three_or_nine hsub hQcard with h1 | h3 | h9
  · have hbot : W.subgroup = ⊥ := Subgroup.card_eq_one.mp h1
    have htwo := rawWeightBlock_eq_role_two_of_bot iota R roles Dordinary C allocation
      Dzero Tzero availability compatibility W hbot
    have hne : (1 : Fin 3) ≠ 2 := by decide
    exact (hne (roles.injective (hW.symm.trans htwo))).elim
  · have hclass := radicalClass_eq_of_areConjugate P U (orderThreeClassification P hsub h3)
    let wRaw : ConjugacyClass (p := 3) (K := K) (G := G) :=
      Quotient.mk'' (Quotient.mk'' W)
    have hclass' : radicalClass wRaw =
        (Quotient.mk'' U : RadicalConjugacyClass (p := 3) (G := G)) := hclass
    exact (radicalClass_ne_of_empty_local U hEmpty wRaw hclass').elim
  · exact radicalClass_eq_of_subconjugate_of_card_eq P Q hsub (h9.trans hQcard.symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3DerivedRadicalSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
