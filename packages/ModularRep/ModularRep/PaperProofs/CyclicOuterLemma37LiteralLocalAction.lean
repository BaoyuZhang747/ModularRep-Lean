import ModularRep.BrauerCharacterHomPullback
import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

/-!
# The literal local action in Lemma 2.10

This file identifies conjugation by the quotient pair stabiliser with the
automorphism transport already contained in stabilisation of the selected
character weight.  It then derives fixedness of the transported ordinary and
Brauer characters and applies the cyclic extension principle.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (phi : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

/-- Transport between subgroup normalisers along an equality of the
underlying subgroups. -/
def castNormalizer {Q R : Subgroup H} (h : Q = R) :
    Subgroup.normalizer (Q : Set H) ≃*
      Subgroup.normalizer (R : Set H) :=
  MulEquiv.cast
    (M := fun S : Subgroup H ↦ Subgroup.normalizer (S : Set H)) h

@[simp]
theorem castNormalizer_coe {Q R : Subgroup H} (h : Q = R)
    (n : Subgroup.normalizer (Q : Set H)) :
    ((castNormalizer h n : Subgroup.normalizer (R : Set H)) : H) = n := by
  subst R
  rfl

@[simp]
theorem quotientCast_mk {Q R : Subgroup H} (h : Q = R)
    (n : Subgroup.normalizer (Q : Set H)) :
    MulEquiv.cast (M := fun S : Subgroup H ↦ NormalizerQuotient S) h
        (QuotientGroup.mk n) =
      QuotientGroup.mk (castNormalizer h n) := by
  subst R
  rfl

@[simp]
theorem quotientCast_symm_mk {Q R : Subgroup H} (h : Q = R)
    (n : Subgroup.normalizer (R : Set H)) :
    (MulEquiv.cast (M := fun S : Subgroup H ↦ NormalizerQuotient S) h).symm
        (QuotientGroup.mk n) =
      QuotientGroup.mk (castNormalizer h.symm n) := by
  subst R
  rfl

@[simp]
theorem normalizerToPairStabilizer_coe
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (n : Subgroup.normalizer
      (SelectedRadical blockSource block w : Set H)) :
    ((normalizerToPairStabilizer
        phi blockSource block quotientInput w n :
      PairStabilizer phi blockSource block w) : H ⋊[phi] E) =
      SemidirectProduct.inl n.1 :=
  rfl

@[simp]
theorem normalizerQuotientEquivLocalBase_mk
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (n : Subgroup.normalizer
      (SelectedRadical blockSource block w : Set H)) :
    letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w
    normalizerQuotientEquivLocalBase
        phi blockSource block quotientInput w (QuotientGroup.mk n) =
      normalizerToLocalBase phi blockSource block quotientInput w n := by
  rfl

/-- The character equality contained in an isomorphism between an
automorphism transport of a character weight and the original weight. -/
theorem localCharacter_fixed_of_rightTwist_isomorphic
    (W : CharacterWeight p K H) (alpha : MulAut H)
    (hIso : CharacterWeight.Isomorphic (W.rightTwist alpha) W)
    (x : NormalizerQuotient W.subgroup) :
    let hQ := hIso.choose
    W.localCharacter
        (rightNormalizerQuotientEquiv alpha W.subgroup
          ((MulEquiv.cast
            (M := fun R : Subgroup H ↦ NormalizerQuotient R) hQ).symm x)) =
      W.localCharacter x := by
  dsimp only
  rcases hIso with ⟨hQ, hchi⟩
  have hvalue := congrArg
    (fun chi : OrdinaryIrreducibleCharacter.Irr K
      (NormalizerQuotient W.subgroup) ↦ chi x) hchi
  rw [castLocalCharacter_apply] at hvalue
  exact hvalue

/-- Conjugation by a raw pair stabiliser representative agrees, after the
normaliser quotient identification, with direct transport by the induced
automorphism of the ambient group.  The subgroup equality is the one supplied
by stabilisation of the character weight under the inverse representative. -/
theorem local_conjugation_argument
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (d0 : PairStabilizer phi blockSource block w)
    (x : LocalBase phi blockSource block quotientInput w) :
    letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w
    let hIso := selectedPairStabilizer_supplies_isomorphic
      (phi := phi) (blockSource := blockSource) (block := block) w d0⁻¹
    let hQ := hIso.choose
    (normalizerQuotientEquivLocalBase
        phi blockSource block quotientInput w).symm
        (MulAut.conjNormal
          (QuotientGroup.mk'
            (EmbeddedRadical phi blockSource block quotientInput w) d0) x) =
      rightNormalizerQuotientEquiv
        (semidirectToMulAut phi ((d0⁻¹ :
          PairStabilizer phi blockSource block w) : H ⋊[phi] E)⁻¹)
        (SelectedRadical blockSource block w)
        ((MulEquiv.cast
          (M := fun R : Subgroup H ↦ NormalizerQuotient R) hQ).symm
          ((normalizerQuotientEquivLocalBase
            phi blockSource block quotientInput w).symm x)) := by
  dsimp only
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  let hIso := selectedPairStabilizer_supplies_isomorphic
    (phi := phi) (blockSource := blockSource) (block := block) w d0⁻¹
  let hQ := hIso.choose
  change (SelectedRadical blockSource block w).comap
      (semidirectToMulAut phi ((d0⁻¹ :
        PairStabilizer phi blockSource block w) : H ⋊[phi] E)⁻¹).toMonoidHom =
    SelectedRadical blockSource block w at hQ
  change _ = rightNormalizerQuotientEquiv _ _
    ((MulEquiv.cast hQ).symm _)
  obtain ⟨n, rfl⟩ := normalizerToLocalBase_surjective
    (phi := phi) (blockSource := blockSource) (block := block)
    quotientInput w x
  apply (normalizerQuotientEquivLocalBase
    phi blockSource block quotientInput w).injective
  rw [MulEquiv.apply_symm_apply]
  rw [← normalizerQuotientEquivLocalBase_mk
    (phi := phi) (blockSource := blockSource) (block := block)
    quotientInput w n]
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  rw [quotientCast_symm_mk]
  rw [rightNormalizerQuotientEquiv_mk]
  simp only [normalizerQuotientEquivLocalBase_mk,
    normalizerToLocalBase_val]
  change QuotientGroup.mk'
      (EmbeddedRadical phi blockSource block quotientInput w)
        (d0 * normalizerToPairStabilizer
          phi blockSource block quotientInput w n * d0⁻¹) =
    QuotientGroup.mk'
      (EmbeddedRadical phi blockSource block quotientInput w)
        (normalizerToPairStabilizer phi blockSource block quotientInput w
          (rightNormalizerEquiv
            (semidirectToMulAut phi ((d0⁻¹ :
              PairStabilizer phi blockSource block w) : H ⋊[phi] E)⁻¹)
            (SelectedRadical blockSource block w)
            (castNormalizer hQ.symm n)))
  apply congrArg
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [normalizerToPairStabilizer_coe,
    normalizerToPairStabilizer_coe]
  rw [rightNormalizerEquiv_coe, castNormalizer_coe]
  change d0.1 * SemidirectProduct.inl n.1 * d0.1⁻¹ =
    SemidirectProduct.inl
      (semidirectToMulAut phi
        ((d0⁻¹ : PairStabilizer phi blockSource block w) :
          H ⋊[phi] E)⁻¹ n.1)
  simpa using conjugate_inl_eq_inl_semidirectToMulAut
    (phi := phi) d0.1 n.1

/-- The transported ordinary local character is fixed by conjugation from
the complete quotient pair stabiliser.  The equality is derived from raw-pair
stabilisation and the preceding quotient square. -/
theorem transportedLocalOrdinary_fixed
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w
    ∀ d : PairStabilizer phi blockSource block w ⧸
        EmbeddedRadical phi blockSource block quotientInput w,
      OrdinaryIrreducibleCharacter.twist K _
        (transportedLocalOrdinary
          phi blockSource block quotientInput w)
        (MulAut.conjNormal d) =
      transportedLocalOrdinary
        phi blockSource block quotientInput w := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  intro d
  obtain ⟨d0, rfl⟩ := QuotientGroup.mk'_surjective
    (EmbeddedRadical phi blockSource block quotientInput w) d
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  change (selectedCharacterWeight blockSource block w).localCharacter
      ((normalizerQuotientEquivLocalBase
        phi blockSource block quotientInput w).symm
        (MulAut.conjNormal
          (QuotientGroup.mk'
            (EmbeddedRadical phi blockSource block quotientInput w) d0) x)) =
    (selectedCharacterWeight blockSource block w).localCharacter
      ((normalizerQuotientEquivLocalBase
        phi blockSource block quotientInput w).symm x)
  let hIso := selectedPairStabilizer_supplies_isomorphic
    (phi := phi) (blockSource := blockSource) (block := block) w d0⁻¹
  rw [local_conjugation_argument
    (phi := phi) (blockSource := blockSource) (block := block)
    quotientInput w d0 x]
  exact localCharacter_fixed_of_rightTwist_isomorphic
    (selectedCharacterWeight blockSource block w)
    (semidirectToMulAut phi ((d0⁻¹ :
      PairStabilizer phi blockSource block w) : H ⋊[phi] E)⁻¹)
    hIso
    ((normalizerQuotientEquivLocalBase
      phi blockSource block quotientInput w).symm x)

/-- Naturality of Brauer reduction transfers the derived ordinary fixedness
to the actual transported Brauer character. -/
theorem transportedLocalBrauer_fixed
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w) :
    letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w
    ∀ d : PairStabilizer phi blockSource block w ⧸
        EmbeddedRadical phi blockSource block quotientInput w,
      IrreducibleBrauerCharacter.twist
        (transportedLocalRootEmbedding
          phi blockSource block quotientInput w source)
        (transportedLocalBrauer
          phi blockSource block quotientInput w source)
        (MulAut.conjNormal d) =
      transportedLocalBrauer
        phi blockSource block quotientInput w source := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  intro d
  exact brauerReduction_fixed_of_ordinary_fixed
    (transportedLocalRootEmbedding
      phi blockSource block quotientInput w source)
    (transportedLocalOrdinary
      phi blockSource block quotientInput w)
    (transportedLocalBrauer
      phi blockSource block quotientInput w source)
    (transportedLocalBrauer_reduction
      phi blockSource block quotientInput w source)
    (MulAut.conjNormal d)
    (transportedLocalOrdinary_fixed
      phi blockSource block quotientInput w d)

/-- The local extension required in Lemma 2.10 for the selected literal
character-weight representative.  No character fixedness or extension is an
input: ordinary fixedness comes from raw-pair stabilisation, Brauer fixedness
from reduction, and the extension from the cited cyclic extension principle. -/
theorem selectedLiteralLocalExtension
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w) :
    letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w
    ∃ W : FDRep k (LocalBase phi blockSource block quotientInput w),
      Representation.IsIrreducible W.ρ ∧
      (transportedLocalBrauer
        phi blockSource block quotientInput w source).1 =
        Representation.brauerCharacterOfRootEmbedding W.ρ
          (transportedLocalRootEmbedding
            phi blockSource block quotientInput w source) ∧
      ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
        (transportedLocalRootEmbedding
          phi blockSource block quotientInput w source)
        (transportedLocalOrdinary
          phi blockSource block quotientInput w)
        (transportedLocalBrauer
          phi blockSource block quotientInput w source) ∧
      Nonempty (Representation.Extension
        (LocalBase phi blockSource block quotientInput w) W.ρ) := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  exact local_extension_actual quotientInput phi principle
    (selectedRawWeight blockSource block w)
    (EmbeddedRadical phi blockSource block quotientInput w)
    (embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w)
    (embeddedRadical_le_embeddedHStabilizer
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w)
    (transportedLocalRootEmbedding
      phi blockSource block quotientInput w source)
    (transportedLocalOrdinary
      phi blockSource block quotientInput w)
    (transportedLocalOrdinary_defectZero
      phi blockSource block quotientInput w)
    (transportedLocalBrauer
      phi blockSource block quotientInput w source)
    (transportedLocalBrauer_reduction
      phi blockSource block quotientInput w source)
    (transportedLocalOrdinary_fixed
      phi blockSource block quotientInput w)

/-- Package the preceding cyclic-extension output as the literal ambient
Brauer-character extension witness required by the inductive condition.
Existence of a compatible ambient root embedding remains explicit. -/
noncomputable def selectedLiteralLocalExtensionWitness
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w) :
    letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w
    (ambientRoot : PrimeRegularRootEmbedding p k K
      (PairStabilizer phi blockSource block w ⧸
        EmbeddedRadical phi blockSource block quotientInput w)) →
    (hlift :
      (transportedLocalRootEmbedding
        phi blockSource block quotientInput w source).lift =
          ambientRoot.lift) →
    Representation.Extension.BrauerCharacterExtensionWitness
      ambientRoot
      (transportedLocalRootEmbedding
        phi blockSource block quotientInput w source)
      (transportedLocalBrauer
        phi blockSource block quotientInput w source) := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  intro ambientRoot hlift
  have hexists : ∃ W : FDRep k
      (LocalBase phi blockSource block quotientInput w),
      Representation.IsIrreducible W.ρ ∧
      (transportedLocalBrauer
        phi blockSource block quotientInput w source).1 =
        Representation.brauerCharacterOfRootEmbedding W.ρ
          (transportedLocalRootEmbedding
            phi blockSource block quotientInput w source) ∧
      Nonempty (Representation.Extension
        (LocalBase phi blockSource block quotientInput w) W.ρ) := by
    rcases selectedLiteralLocalExtension
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput principle w source with
      ⟨W, hirr, haffords, _reduction, extension⟩
    exact ⟨W, hirr, haffords, extension⟩
  exact
    Representation.Extension.brauerCharacterExtensionWitnessOfExistsExtension
      ambientRoot
      (transportedLocalRootEmbedding
        phi blockSource block quotientInput w source)
      (transportedLocalBrauer
        phi blockSource block quotientInput w source)
      hexists hlift

end ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
