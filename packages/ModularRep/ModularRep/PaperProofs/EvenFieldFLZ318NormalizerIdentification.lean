import ModularRep.PaperProofs.EvenFieldFLZ318InflatedLocalCharacterExtension

/-!
# Identifying the local stabiliser with the subgroup normaliser

For the literal pair selected in the formalisation of Lemma 2.10, this file
identifies its restricted `H` stabiliser with the normaliser of its selected
radical subgroup.  It then transports this equality to the copy of that
stabiliser embedded in the full pair stabiliser.

The construction uses the canonical normaliser quotient calculation already
proved for actual character weights.  It introduces no source theorem.  Its
`CyclicEndgameData` input contains a quotient level representation extension
that was derived upstream from the cyclic extension principle.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZ318NormalizerIdentification

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldFLZ318InflatedLocalCharacterExtension

universe u

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (field : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)

/-- For the selected literal pair, the stabiliser inside `H` is exactly the
normaliser in `H` of the selected radical subgroup.  This is the typed form of
the manuscript identity `D ∩ H = N_H(Q)` before embedding the left hand side
in the full pair stabiliser. -/
theorem pairHStabilizer_eq_normalizer
    (w : LiteralWeightFibre blockSource block) :
    PairHStabilizer field blockSource block w =
      Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) := by
  simpa only [rawSubgroup_selectedRawWeight] using
    (actual_rawWeight_embeddedStabilizer_eq_normalizer
      (canonicalRawNormalizerQuotientInput (p := p) (K := K) (H := H))
      field (selectedRawWeight blockSource block w))

/-- The equality of subgroups gives the canonical multiplicative equivalence
between their underlying groups. -/
def pairHStabilizerEquivNormalizer
    (w : LiteralWeightFibre blockSource block) :
    PairHStabilizer field blockSource block w ≃*
      Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) :=
  MulEquiv.subgroupCongr
    (pairHStabilizer_eq_normalizer field blockSource block w)

@[simp]
theorem pairHStabilizerEquivNormalizer_coe
    (w : LiteralWeightFibre blockSource block)
    (h : PairHStabilizer field blockSource block w) :
    ((pairHStabilizerEquivNormalizer field blockSource block w h :
      Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H)) : H) = h := by
  exact MulEquiv.subgroupCongr_apply
    (pairHStabilizer_eq_normalizer field blockSource block w) h

/-- The canonical inclusion of the restricted stabiliser identifies it with
its range inside the full pair stabiliser. -/
def pairHStabilizerEquivEmbedded
    (w : LiteralWeightFibre blockSource block) :
    PairHStabilizer field blockSource block w ≃*
      EmbeddedPairHStabilizer field blockSource block w := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction field
  letI : MulAction (H ⋊[field] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction field
  exact MulEquiv.ofBijective
    (inlStabilizerHom
      (phi := field) (selectedRawWeight blockSource block w)).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (inlStabilizerHom_injective
          (phi := field) (selectedRawWeight blockSource block w)),
      (inlStabilizerHom
        (phi := field)
        (selectedRawWeight blockSource block w)).rangeRestrict_surjective⟩

@[simp]
theorem pairHStabilizerEquivEmbedded_coe
    (w : LiteralWeightFibre blockSource block)
    (h : PairHStabilizer field blockSource block w) :
    (((pairHStabilizerEquivEmbedded field blockSource block w h :
      EmbeddedPairHStabilizer field blockSource block w) :
        PairStabilizer field blockSource block w) : H ⋊[field] E) =
      SemidirectProduct.inl h.1 := by
  rfl

/-- The copy of `D ∩ H` inside the full pair stabiliser is canonically
equivalent to `N_H(Q)`. -/
def embeddedPairHStabilizerEquivNormalizer
    (w : LiteralWeightFibre blockSource block) :
    EmbeddedPairHStabilizer field blockSource block w ≃*
      Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) :=
  (pairHStabilizerEquivEmbedded field blockSource block w).symm.trans
    (pairHStabilizerEquivNormalizer field blockSource block w)

@[simp]
theorem embeddedPairHStabilizerEquivNormalizer_coe
    (w : LiteralWeightFibre blockSource block)
    (h : EmbeddedPairHStabilizer field blockSource block w) :
    ((embeddedPairHStabilizerEquivNormalizer
      field blockSource block w h :
        Subgroup.normalizer
          (SelectedRadical blockSource block w : Set H)) : H) =
      ((h : PairStabilizer field blockSource block w) : H ⋊[field] E).left := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction field
  letI : MulAction (H ⋊[field] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction field
  rcases h with ⟨_, ⟨x, rfl⟩⟩
  have hx :
      (⟨inlStabilizerHom
          (phi := field) (selectedRawWeight blockSource block w) x,
        ⟨x, rfl⟩⟩ : EmbeddedPairHStabilizer field blockSource block w) =
        pairHStabilizerEquivEmbedded field blockSource block w x := by
    apply Subtype.ext
    rfl
  rw [hx]
  simp [embeddedPairHStabilizerEquivNormalizer]

/-- The equivalence with the actual normaliser commutes with the two quotient
maps.  On an element of `N_H(Q)`, both paths are represented by the same
element of the full pair stabiliser. -/
theorem subgroupToQuotientImage_embeddedEquiv_symm
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        quotientInput w
    ∀ n : Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H),
      subgroupToQuotientImage
          (EmbeddedRadical field blockSource block quotientInput w)
          (EmbeddedPairHStabilizer field blockSource block w)
          ((embeddedPairHStabilizerEquivNormalizer
            field blockSource block w).symm n) =
        normalizerQuotientEquivLocalBase
          field blockSource block quotientInput w (QuotientGroup.mk n) := by
  letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := field) (blockSource := blockSource) (block := block)
      quotientInput w
  intro n
  rw [CyclicOuterLemma37LiteralLocalAction.normalizerQuotientEquivLocalBase_mk]
  apply Subtype.ext
  change QuotientGroup.mk'
      (EmbeddedRadical field blockSource block quotientInput w)
      (((embeddedPairHStabilizerEquivNormalizer
          field blockSource block w).symm n :
            EmbeddedPairHStabilizer field blockSource block w) :
        PairStabilizer field blockSource block w) =
    QuotientGroup.mk'
      (EmbeddedRadical field blockSource block quotientInput w)
      (normalizerToPairStabilizer
        field blockSource block quotientInput w n)
  apply congrArg
  apply Subtype.ext
  apply SemidirectProduct.ext
  · simpa using
      (embeddedPairHStabilizerEquivNormalizer_coe
        field blockSource block w
          ((embeddedPairHStabilizerEquivNormalizer
            field blockSource block w).symm n)).symm
  · rcases ((embeddedPairHStabilizerEquivNormalizer
        field blockSource block w).symm n).2 with ⟨h, hh⟩
    have hright := congrArg
      (fun z : PairStabilizer field blockSource block w ↦
        ((z : H ⋊[field] E).right)) hh
    simpa [inlStabilizerHom] using hright.symm

/-- The quotient map `N_H(Q) → N_H(Q) / Q` for the selected radical
subgroup. -/
def selectedNormalizerQuotientHom
    (w : LiteralWeightFibre blockSource block) :
    Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) →*
      NormalizerQuotient (SelectedRadical blockSource block w) :=
  QuotientGroup.mk'
    ((SelectedRadical blockSource block w).subgroupOf
      (Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H)))

section CharacterInflation

variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (T : FibreTransportSource iota hinj blocks field block)
variable (quotientInput : RawNormalizerQuotientInput
  (p := p) (K := K) (H := H))
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)

/-- The local character extension produced by the cyclic endgame restricts,
after the canonical identification `D ∩ H ≃ N_H(Q)`, to the inflation of
the selected Brauer reduction from `N_H(Q) / Q` to `N_H(Q)`.

The three compatibility hypotheses are exactly those used by the preceding
character inflation theorem to compare root lifts under restriction and
inflation.  No full pair stabiliser Brauer character extension or inflation
equality is supplied as an input.  The quotient level representation extension
is contained in `endgame` and is derived upstream from the cyclic extension
principle. -/
theorem localBrauerCharacterExtension_on_normalizer_of_cyclicEndgame
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := field)
      (blockSource := blockSource) (block := block) T
      quotientInput localReduction)
    (psi : BrauerFibre iota hinj blocks block) :
    let w := endgame.omega.toEquiv psi
    letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := field) (blockSource := blockSource) (block := block)
        quotientInput w
    ∀ (iotaQuotient : PrimeRegularRootEmbedding p k K
        (PairStabilizer field blockSource block w ⧸
          EmbeddedRadical field blockSource block quotientInput w))
      (iotaPair : PrimeRegularRootEmbedding p k K
        (PairStabilizer field blockSource block w))
      (iotaEmbeddedLocal : PrimeRegularRootEmbedding p k K
        (EmbeddedPairHStabilizer field blockSource block w)),
      (∀ (W : FDRep k (LocalBase field blockSource block quotientInput w))
        (extension : Representation.Extension
          (LocalBase field blockSource block quotientInput w) W.ρ),
        Representation.BrauerRootLiftCompatibleAlong
          extension.representation iotaQuotient
          (transportedLocalRootEmbedding
            field blockSource block quotientInput w (localReduction w))
          (LocalBase field blockSource block quotientInput w).subtype) →
      (∀ (W : FDRep k (LocalBase field blockSource block quotientInput w))
        (extension : Representation.Extension
          (LocalBase field blockSource block quotientInput w) W.ρ),
        Representation.BrauerRootLiftCompatibleAlong
          extension.representation iotaQuotient iotaPair
          (QuotientGroup.mk'
            (EmbeddedRadical field blockSource block quotientInput w))) →
      (∀ W : FDRep k (LocalBase field blockSource block quotientInput w),
        Representation.BrauerRootLiftCompatibleAlong W.ρ
          (transportedLocalRootEmbedding
            field blockSource block quotientInput w (localReduction w))
          iotaEmbeddedLocal
          (subgroupToQuotientImage
            (EmbeddedRadical field blockSource block quotientInput w)
            (EmbeddedPairHStabilizer field blockSource block w))) →
      ∃ quotientWitness :
          Representation.Extension.BrauerCharacterExtensionWitness
            iotaQuotient
            (transportedLocalRootEmbedding
              field blockSource block quotientInput w (localReduction w))
            (transportedLocalBrauer
              field blockSource block quotientInput w (localReduction w)),
        ∃ inflatedLocal : IBr iotaEmbeddedLocal,
          ∃ pairWitness :
              Representation.Extension.BrauerCharacterExtensionWitness
                iotaPair iotaEmbeddedLocal inflatedLocal,
            (IrreducibleBrauerCharacter.alongMulEquiv
                iotaEmbeddedLocal
                (embeddedPairHStabilizerEquivNormalizer
                  field blockSource block w)
                inflatedLocal).1 =
              PrimeRegularClassFunction.pullback
                (selectedNormalizerQuotientHom blockSource block w)
                (localReduction w).brauer.1 ∧
            pairWitness.1.1 =
              PrimeRegularClassFunction.pullback
                (QuotientGroup.mk'
                  (EmbeddedRadical
                    field blockSource block quotientInput w))
                quotientWitness.1.1 := by
  dsimp only
  let w := endgame.omega.toEquiv psi
  letI : (EmbeddedRadical field blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := field) (blockSource := blockSource) (block := block)
      quotientInput w
  intro iotaQuotient iotaPair iotaEmbeddedLocal
    quotientCompatible pairInflationCompatible localInflationCompatible
  rcases localBrauerCharacterExtension_inflate_of_cyclicEndgame
      iota hinj blocks field blockSource block T quotientInput localReduction
      endgame psi iotaQuotient iotaPair iotaEmbeddedLocal
      quotientCompatible pairInflationCompatible localInflationCompatible with
    ⟨quotientWitness, inflatedLocal, hinflated, pairWitness, hpair⟩
  refine ⟨quotientWitness, inflatedLocal, pairWitness, ?_, hpair⟩
  rw [IrreducibleBrauerCharacter.alongMulEquiv_val, hinflated]
  apply PrimeRegularClassFunction.ext
  intro n
  change (localReduction w).brauer.1
      (PrimeRegularElement.map
        (normalizerQuotientEquivLocalBase
          field blockSource block quotientInput w).symm.toMonoidHom
        (PrimeRegularElement.map
          (subgroupToQuotientImage
            (EmbeddedRadical field blockSource block quotientInput w)
            (EmbeddedPairHStabilizer field blockSource block w))
          (PrimeRegularElement.map
            (embeddedPairHStabilizerEquivNormalizer
              field blockSource block w).symm.toMonoidHom n))) =
    (localReduction w).brauer.1
      (PrimeRegularElement.map
        (selectedNormalizerQuotientHom blockSource block w) n)
  apply congrArg (localReduction w).brauer.1
  apply Subtype.ext
  change (normalizerQuotientEquivLocalBase
      field blockSource block quotientInput w).symm
      (subgroupToQuotientImage
        (EmbeddedRadical field blockSource block quotientInput w)
        (EmbeddedPairHStabilizer field blockSource block w)
        ((embeddedPairHStabilizerEquivNormalizer
          field blockSource block w).symm n.1)) =
    QuotientGroup.mk n.1
  have hsquare := subgroupToQuotientImage_embeddedEquiv_symm
    field blockSource block quotientInput w n.1
  calc
    _ = (normalizerQuotientEquivLocalBase
          field blockSource block quotientInput w).symm
        (normalizerQuotientEquivLocalBase
          field blockSource block quotientInput w (QuotientGroup.mk n.1)) :=
      congrArg
        (normalizerQuotientEquivLocalBase
          field blockSource block quotientInput w).symm hsquare
    _ = QuotientGroup.mk n.1 :=
      (normalizerQuotientEquivLocalBase
        field blockSource block quotientInput w).symm_apply_apply
          (QuotientGroup.mk n.1)

end CharacterInflation

end ModularRep.PaperProofs.EvenFieldFLZ318NormalizerIdentification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
