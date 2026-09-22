import ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres

/-!
# The literal local extension in Lemma 2.10

An element of the manuscript's weight set is an ambient conjugacy class of
character weights.  The local extension condition is instead stated for a
representative `(Q, theta)` and its stabiliser.  This file makes that passage
on the actual set of weights defined by characters.

The representative is selected using the two quotient maps defining
`CharacterWeight.ConjugacyClass`.  From it we construct the literal copy of
`Q` in the stabiliser of the raw pair, prove its normality, identify the
embedded normaliser quotient with `N_H(Q) / Q`, and transport the ordinary
local character and its Brauer reduction across this equivalence.

The Brauer reduction itself is isolated as a source-shaped character input.
After that input, the remaining local action bridge is the equality saying
that the transported ordinary character is fixed by conjugation from the
quotient pair stabiliser.  This is the precise carrier-identification boundary
between the manuscript's notation `D = (H semidirect E)_{Q,theta}` and the
formal right transport of a dependent local character.  Cyclicity is derived
in the kernel.  The extension theorem is not invoked until this remaining
action equality has been established.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres

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

abbrev LiteralWeightFibre :=
  WeightFibre blockSource block

/-- A literal character-weight representative of a weight conjugacy class.
Surjectivity is the composite of the two quotient maps: first by equality of
the transported local character and then by ambient conjugation. -/
def selectedCharacterWeight
    (w : LiteralWeightFibre blockSource block) : CharacterWeight p K H :=
  Classical.choose
    ((Quotient.mk_surjective.comp Quotient.mk_surjective) w.1)

/-- The selected raw pair represents the given element of the weight fibre. -/
theorem selectedCharacterWeight_spec
    (w : LiteralWeightFibre blockSource block) :
    (Quotient.mk'' (Quotient.mk''
      (selectedCharacterWeight blockSource block w)) :
        CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H)) = w.1 :=
  Classical.choose_spec
    ((Quotient.mk_surjective.comp Quotient.mk_surjective) w.1)

/-- The raw isomorphism class of the selected representative. -/
abbrev selectedRawWeight
    (w : LiteralWeightFibre blockSource block) :
    RawWeightClass (p := p) (K := K) (H := H) :=
  Quotient.mk'' (selectedCharacterWeight blockSource block w)

/-- Local block induction assigns the selected representative to the block
defining the literal fibre. -/
theorem selectedCharacterWeight_block
    (w : LiteralWeightFibre blockSource block) :
    blockSource.operations.rawWeightBlock
        (selectedCharacterWeight blockSource block w) = block := by
  have hw := w.2
  rw [← selectedCharacterWeight_spec
    (blockSource := blockSource) (block := block) w] at hw
  exact hw

/-- The local block of the selected representative induces to the block
which defines its weight fibre. -/
theorem selectedCharacterWeight_blockInducesTo
    (w : LiteralWeightFibre blockSource block) :
    let W := selectedCharacterWeight blockSource block w
    let O := blockSource.operations
    let localData := O.inflatedNormalizerBlockData W.subgroup
    letI : Fintype ι := O.ambientBlockData.fintypeBlock
    letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
      localData.fintypeBlock
    ModularRep.BlockInducesTo
      (Subgroup.normalizer (W.subgroup : Set H))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero))
      block := by
  let W := selectedCharacterWeight blockSource block w
  let O := blockSource.operations
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI : Fintype ι := O.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    localData.fintypeBlock
  have inducedBlock_eq : O.induceToAmbient W = block := by
    calc
      O.induceToAmbient W = O.rawWeightBlock W := rfl
      _ = block :=
        selectedCharacterWeight_block blockSource block w
  change ModularRep.BlockInducesTo
    (Subgroup.normalizer (W.subgroup : Set H))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock
        W.subgroup W.localCharacter W.defectZero))
    block
  rw [← inducedBlock_eq]
  exact ModularRep.inducedBlock_spec
    (Subgroup.normalizer (W.subgroup : Set H))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock
        W.subgroup W.localCharacter W.defectZero))
    (O.blockInductionDefined W)

section SelectedRawPair

/-- The canonical inner action on raw character-weight classes. -/
abbrev canonicalRawHAction :
    MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
  rightAutomorphismAction
    (X := RawWeightClass (p := p) (K := K) (H := H))
    (MulAut.conj : H →* MulAut H)

/-- The canonical outer action on raw character-weight classes. -/
abbrev canonicalRawEAction (phi : E →* MulAut H) :
    MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
  rightAutomorphismAction
    (X := RawWeightClass (p := p) (K := K) (H := H)) phi

/-- The canonical semidirect action on raw character-weight classes. -/
abbrev canonicalRawSemidirectAction (phi : E →* MulAut H) :
    MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  exact semidirectMulAction phi
    (rightAutomorphismSemidirectCompatible
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi)

/-- The stabiliser of the selected raw pair `(Q, theta)`. -/
abbrev PairStabilizer
    (w : LiteralWeightFibre blockSource block) :=
  let _ : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  semidirectStabilizer (phi := phi)
    (selectedRawWeight blockSource block w)

/-- The restricted `H`-stabiliser associated with the same literal action. -/
abbrev PairHStabilizer
    (w : LiteralWeightFibre blockSource block) :=
  let _ : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  hStabilizer (phi := phi) (selectedRawWeight blockSource block w)

/-- The canonical copy of the restricted `H`-stabiliser in the pair
stabiliser. -/
abbrev EmbeddedPairHStabilizer
    (w : LiteralWeightFibre blockSource block) :=
  let _ : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  embeddedHStabilizer (phi := phi) (selectedRawWeight blockSource block w)

/-- The selected radical subgroup. -/
abbrev SelectedRadical
    (w : LiteralWeightFibre blockSource block) : Subgroup H :=
  (selectedCharacterWeight blockSource block w).subgroup

/-- The selected radical is definitionally the subgroup component of the
selected raw pair. -/
@[simp]
theorem rawSubgroup_selectedRawWeight
    (w : LiteralWeightFibre blockSource block) :
    rawSubgroup (selectedRawWeight blockSource block w) =
      SelectedRadical blockSource block w :=
  rfl

/-- The literal embedding of `N_H(Q)` in the stabiliser of the selected raw
pair.  Membership in the stabiliser is proved from invariance of the actual
character weight under its subgroup normaliser. -/
def normalizerToPairStabilizer
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) →*
      PairStabilizer phi blockSource block w := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  refine
    { toFun := fun n ↦ ⟨SemidirectProduct.inl n.1, ?_⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        simp }
  change (SemidirectProduct.inl n.1 : H ⋊[phi] E) •
      selectedRawWeight blockSource block w =
        selectedRawWeight blockSource block w
  rw [semidirect_inl_smul]
  exact normalizer_fixes_rawWeight quotientInput n.1
    (selectedRawWeight blockSource block w) n.2

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

/-- The literal embedding of `Q` in the raw-pair stabiliser. -/
def radicalToPairStabilizer
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    SelectedRadical blockSource block w →*
      PairStabilizer phi blockSource block w :=
  (normalizerToPairStabilizer phi blockSource block quotientInput w).comp
    (Subgroup.inclusion
      (SelectedRadical blockSource block w).le_normalizer)

/-- The actual copy of `Q` inside the stabiliser of `(Q, theta)`. -/
def EmbeddedRadical
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    Subgroup (PairStabilizer phi blockSource block w) :=
  (radicalToPairStabilizer phi blockSource block quotientInput w).range

/-- The embedded radical lies in the canonical copy of the restricted
`H`-stabiliser. -/
theorem embeddedRadical_le_embeddedHStabilizer
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    EmbeddedRadical phi blockSource block quotientInput w ≤
      EmbeddedPairHStabilizer phi blockSource block w := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  rintro x ⟨q, rfl⟩
  let hq : PairHStabilizer phi blockSource block w := ⟨q.1, by
    change (SemidirectProduct.inl q.1 : H ⋊[phi] E) •
      selectedRawWeight blockSource block w =
        selectedRawWeight blockSource block w
    rw [semidirect_inl_smul]
    exact normalizer_fixes_rawWeight quotientInput q.1
      (selectedRawWeight blockSource block w)
      ((SelectedRadical blockSource block w).le_normalizer q.2)⟩
  refine ⟨hq, ?_⟩
  apply Subtype.ext
  rfl

/-- A semidirect-product element conjugates the normal factor according to
the automorphism represented by that element. -/
theorem conjugate_inl_eq_inl_semidirectToMulAut
    (g : H ⋊[phi] E) (h : H) :
    g * SemidirectProduct.inl h * g⁻¹ =
      SemidirectProduct.inl (semidirectToMulAut phi g h) := by
  have hmap : semidirectToMulAut phi g =
      MulAut.conj g.left * phi g.right := by
    calc
      semidirectToMulAut phi g =
          semidirectToMulAut phi
            (SemidirectProduct.inl g.left *
              SemidirectProduct.inr g.right) :=
        congrArg (semidirectToMulAut phi)
          (SemidirectProduct.inl_left_mul_inr_right g).symm
      _ = MulAut.conj g.left * phi g.right := by
        rw [map_mul, semidirectToMulAut_inl, semidirectToMulAut_inr]
  apply SemidirectProduct.ext
  · rw [hmap]
    simp [MulAut.conj_apply, mul_assoc]
  · simp

/-- Stabilisation of the selected raw pair preserves its radical subgroup. -/
theorem pairStabilizer_preserves_radical
    (w : LiteralWeightFibre blockSource block)
    (d : PairStabilizer phi blockSource block w) :
    (SelectedRadical blockSource block w).map
        (semidirectToMulAut phi d.1).toMonoidHom =
      SelectedRadical blockSource block w := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  calc
    (SelectedRadical blockSource block w).map
          (semidirectToMulAut phi d.1).toMonoidHom =
        rawSubgroup (d.1 • selectedRawWeight blockSource block w) := by
      change (rawSubgroup (selectedRawWeight blockSource block w)).map
          (semidirectToMulAut phi d.1).toMonoidHom = _
      exact (rawSubgroup_semidirect
        phi d.1 (selectedRawWeight blockSource block w)).symm
    _ = rawSubgroup (selectedRawWeight blockSource block w) :=
      congrArg rawSubgroup d.2
    _ = SelectedRadical blockSource block w := rfl

/-- Raw-pair stabilisation supplies the dependent isomorphism of the selected
character weight under the corresponding automorphism.  Turning this
isomorphism into equality of the transported local character under
conjugation in `D / Q` is the remaining action-coherence bridge. -/
theorem selectedPairStabilizer_supplies_isomorphic
    (w : LiteralWeightFibre blockSource block)
    (d : PairStabilizer phi blockSource block w) :
    CharacterWeight.Isomorphic
      ((selectedCharacterWeight blockSource block w).rightTwist
        (semidirectToMulAut phi (d : H ⋊[phi] E)⁻¹))
      (selectedCharacterWeight blockSource block w) := by
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  exact stabilizer_supplies_rawWeight_isomorphic phi
    (selectedCharacterWeight blockSource block w) d

/-- The literal copy of `Q` is normal in the stabiliser of the selected raw
pair. -/
theorem embeddedRadical_normal
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    (EmbeddedRadical phi blockSource block quotientInput w).Normal := by
  constructor
  intro x hx d
  rcases hx with ⟨q, rfl⟩
  let alpha := semidirectToMulAut phi d.1
  have hq : alpha q.1 ∈ SelectedRadical blockSource block w := by
    have hmem : alpha q.1 ∈
        (SelectedRadical blockSource block w).map alpha.toMonoidHom :=
      Subgroup.mem_map_of_mem alpha.toMonoidHom q.2
    rw [pairStabilizer_preserves_radical
      (phi := phi) (blockSource := blockSource) (block := block) w d] at hmem
    exact hmem
  let q' : SelectedRadical blockSource block w := ⟨alpha q.1, hq⟩
  refine ⟨q', ?_⟩
  apply Subtype.ext
  exact (conjugate_inl_eq_inl_semidirectToMulAut
    (phi := phi) d.1 q.1).symm

/-- The literal local subgroup in the quotient pair stabiliser. -/
abbrev LocalBase
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :=
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  (EmbeddedPairHStabilizer phi blockSource block w).map
    (QuotientGroup.mk'
      (EmbeddedRadical phi blockSource block quotientInput w))

/-- The normaliser maps onto the literal local subgroup after quotienting by
the embedded radical. -/
def normalizerToLocalBase
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    Subgroup.normalizer
        (SelectedRadical blockSource block w : Set H) →*
      LocalBase phi blockSource block quotientInput w := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  let f := normalizerToPairStabilizer
    phi blockSource block quotientInput w
  refine
    { toFun := fun n ↦
        ⟨QuotientGroup.mk'
            (EmbeddedRadical phi blockSource block quotientInput w) (f n), ?_⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        simp }
  change QuotientGroup.mk'
      (EmbeddedRadical phi blockSource block quotientInput w) (f n) ∈
    (EmbeddedPairHStabilizer phi blockSource block w).map
        (QuotientGroup.mk'
          (EmbeddedRadical phi blockSource block quotientInput w))
  apply Subgroup.mem_map.mpr
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawHAction
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawEAction phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  let h : PairHStabilizer phi blockSource block w := ⟨n.1, by
    change (SemidirectProduct.inl n.1 : H ⋊[phi] E) •
      selectedRawWeight blockSource block w =
        selectedRawWeight blockSource block w
    rw [semidirect_inl_smul]
    exact normalizer_fixes_rawWeight quotientInput n.1
      (selectedRawWeight blockSource block w) n.2⟩
  refine ⟨f n, ⟨h, ?_⟩, rfl⟩
  apply Subtype.ext
  rfl

@[simp]
theorem normalizerToLocalBase_val
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (n : Subgroup.normalizer
      (SelectedRadical blockSource block w : Set H)) :
    letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w
    ((normalizerToLocalBase
        phi blockSource block quotientInput w n :
      LocalBase phi blockSource block quotientInput w) :
        PairStabilizer phi blockSource block w ⧸
          EmbeddedRadical phi blockSource block quotientInput w) =
    QuotientGroup.mk'
        (EmbeddedRadical phi blockSource block quotientInput w)
        (normalizerToPairStabilizer
          phi blockSource block quotientInput w n) :=
  by
    rfl

/-- The preceding map is onto the displayed local subgroup. -/
theorem normalizerToLocalBase_surjective
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    Function.Surjective
      (normalizerToLocalBase phi blockSource block quotientInput w) := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  intro y
  have hy : y.1 ∈
      (EmbeddedPairHStabilizer phi blockSource block w).map
        (QuotientGroup.mk'
          (EmbeddedRadical phi blockSource block quotientInput w)) := y.2
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
  rcases hx with ⟨h, rfl⟩
  have hnormal : h.1 ∈ Subgroup.normalizer
      (SelectedRadical blockSource block w : Set H) := by
    letI : MulAction H
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      canonicalRawHAction
    letI : MulAction E
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      canonicalRawEAction phi
    letI : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      canonicalRawSemidirectAction phi
    have hfix : h.1 • selectedRawWeight blockSource block w =
        selectedRawWeight blockSource block w := by
      have hh := h.2
      change (SemidirectProduct.inl h.1 : H ⋊[phi] E) •
          selectedRawWeight blockSource block w =
        selectedRawWeight blockSource block w at hh
      rw [semidirect_inl_smul] at hh
      exact hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hsubgroup :
        rawSubgroup (h.1 • selectedRawWeight blockSource block w) =
          (rawSubgroup (selectedRawWeight blockSource block w)).map
            (MulAut.conj h.1).toMonoidHom :=
      rawSubgroup_conjugate h.1
        (selectedRawWeight blockSource block w)
    rw [hfix] at hsubgroup
    change (rawSubgroup (selectedRawWeight blockSource block w)).map
        (MulAut.conj h.1).toMonoidHom =
      rawSubgroup (selectedRawWeight blockSource block w)
    exact hsubgroup.symm
  refine ⟨⟨h.1, hnormal⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- The kernel of the normaliser map is exactly the selected radical. -/
theorem normalizerToLocalBase_ker
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    (SelectedRadical blockSource block w).subgroupOf
        (Subgroup.normalizer
          (SelectedRadical blockSource block w : Set H)) =
      (normalizerToLocalBase
        phi blockSource block quotientInput w).ker := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  ext n
  constructor
  · intro hn
    change normalizerToLocalBase
        phi blockSource block quotientInput w n = 1
    apply Subtype.ext
    rw [normalizerToLocalBase_val]
    apply (QuotientGroup.eq_one_iff
      (normalizerToPairStabilizer
        phi blockSource block quotientInput w n)).2
    let q : SelectedRadical blockSource block w := ⟨n.1, hn⟩
    exact ⟨q, rfl⟩
  · intro hn
    change normalizerToLocalBase
        phi blockSource block quotientInput w n = 1 at hn
    have hval := congrArg
      (fun z : LocalBase phi blockSource block quotientInput w ↦ z.1) hn
    rw [normalizerToLocalBase_val] at hval
    have hvalMem := (QuotientGroup.eq_one_iff
      (normalizerToPairStabilizer
        phi blockSource block quotientInput w n)).1 hval
    rcases hvalMem with ⟨q, hq⟩
    have hinl : (SemidirectProduct.inl n.1 : H ⋊[phi] E) =
        SemidirectProduct.inl q.1 := by
      exact congrArg
        (fun z : PairStabilizer phi blockSource block w ↦ z.1) hq.symm
    have hnq : n.1 = q.1 :=
      SemidirectProduct.inl_injective hinl
    change n.1 ∈ SelectedRadical blockSource block w
    exact hnq ▸ q.2

/-- Canonical identification of `N_H(Q) / Q` with the local normal subgroup
inside the quotient pair stabiliser. -/
def normalizerQuotientEquivLocalBase
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    NormalizerQuotient (SelectedRadical blockSource block w) ≃*
      LocalBase phi blockSource block quotientInput w := by
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (normalizerToLocalBase_ker
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w)).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (normalizerToLocalBase phi blockSource block quotientInput w)
        (normalizerToLocalBase_surjective
          (phi := phi) (blockSource := blockSource) (block := block)
          quotientInput w))

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

/-- The local ordinary character carried by the selected representative,
transported from `N_H(Q) / Q` to the literal local subgroup in `D / Q`. -/
def transportedLocalOrdinary
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    OrdinaryIrreducibleCharacter.Irr K
      (LocalBase phi blockSource block quotientInput w) :=
  OrdinaryIrreducibleCharacter.mapEquiv
    (selectedCharacterWeight blockSource block w).localCharacter
    (normalizerQuotientEquivLocalBase
      phi blockSource block quotientInput w)

/-- Transport preserves the defect-zero property of the selected local
ordinary character. -/
theorem transportedLocalOrdinary_defectZero
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    IsDefectZeroOrdinaryCharacter p
      (transportedLocalOrdinary
        phi blockSource block quotientInput w) :=
  (selectedCharacterWeight blockSource block w).defectZero.mapEquiv
    (normalizerQuotientEquivLocalBase
      phi blockSource block quotientInput w)

/-- The source datum asserting that the selected defect-zero ordinary
character has the stated literal Brauer reduction.  This is the precise
character-theoretic input, separate from the group-theoretic quotient bridge. -/
structure SelectedLocalReductionSource
    (w : LiteralWeightFibre blockSource block) where
  iota : PrimeRegularRootEmbedding p k K
    (NormalizerQuotient (SelectedRadical blockSource block w))
  brauer : IBr iota
  reduction :
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      iota (selectedCharacterWeight blockSource block w).localCharacter brauer

/-- Transport the selected root embedding to the literal local subgroup. -/
def transportedLocalRootEmbedding
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w) :
    PrimeRegularRootEmbedding p k K
      (LocalBase phi blockSource block quotientInput w) :=
  source.iota.alongMulEquiv
    (normalizerQuotientEquivLocalBase
      phi blockSource block quotientInput w)

/-- Transport the literal Brauer reduction to the same local subgroup. -/
def transportedLocalBrauer
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w) :
    IBr (transportedLocalRootEmbedding
      phi blockSource block quotientInput w source) :=
  IrreducibleBrauerCharacter.alongMulEquiv source.iota
    (normalizerQuotientEquivLocalBase
      phi blockSource block quotientInput w) source.brauer

/-- Brauer reduction commutes with the literal normaliser-quotient
identification. -/
theorem transportedLocalBrauer_reduction
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block)
    (source : SelectedLocalReductionSource blockSource block w) :
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      (transportedLocalRootEmbedding
        phi blockSource block quotientInput w source)
      (transportedLocalOrdinary
        phi blockSource block quotientInput w)
      (transportedLocalBrauer
        phi blockSource block quotientInput w source) := by
  intro g
  exact source.reduction
    (PrimeRegularElement.map
      (normalizerQuotientEquivLocalBase
        phi blockSource block quotientInput w).symm.toMonoidHom g)

/-- The quotient of the pair stabiliser by its local normal subgroup is
cyclic.  This is the literal group-theoretic input used in the local extension
step of Lemma 2.10. -/
theorem pairQuotient_over_localBase_cyclic
    (quotientInput : RawNormalizerQuotientInput
      (p := p) (K := K) (H := H))
    (w : LiteralWeightFibre blockSource block) :
    letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := phi) (blockSource := blockSource) (block := block)
        quotientInput w
    IsCyclic
      ((PairStabilizer phi blockSource block w ⧸
          EmbeddedRadical phi blockSource block quotientInput w) ⧸
        LocalBase phi blockSource block quotientInput w) := by
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    canonicalRawSemidirectAction phi
  letI : (EmbeddedRadical phi blockSource block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w
  exact isCyclic_quotient_tower_of_embedding
    (EmbeddedRadical phi blockSource block quotientInput w)
    (EmbeddedPairHStabilizer phi blockSource block w)
    (embeddedRadical_le_embeddedHStabilizer
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput w)
    (stabilizerQuotientEmbedding (phi := phi)
      (selectedRawWeight blockSource block w))
    (stabilizerQuotientEmbedding_injective (phi := phi)
      (selectedRawWeight blockSource block w))

end SelectedRawPair

end ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
