import ModularRep.PaperProofs.EvenFieldLemma35Conclusion
import ModularRep.PaperProofs.EvenFieldSourceShaped
import Mathlib.Data.Fintype.EquivFin

/-!
# The finite set core of the even-field unipotent correspondence

This file separates the finite set composition in manuscript Lemma 3.7 from
the published parametrisations.  The target-side map is constructed from the
exact cardinality identity stated in Feng--Malle--Zhang, Section 7.1, rather
than from an assumed equivalence obtained from orbit representatives.  The resulting bijection is
an existence statement and is intentionally noncanonical.
-/

namespace ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence

open ModularRep.ManuscriptVerification.EvenFieldFixed
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35Conclusion
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters
open ModularRep.PaperProofs.EvenFieldSourceShaped

/-! ## Generic finite set kernel -/

/-- Three composable equivalences. -/
structure EquivalenceChain (Source Middle₁ Middle₂ Target : Type*) where
  first : Source ≃ Middle₁
  second : Middle₁ ≃ Middle₂
  third : Middle₂ ≃ Target

/-- The composite of three supplied equivalences, in source-to-target order. -/
def EquivalenceChain.correspondence
    {Source Middle₁ Middle₂ Target : Type*}
    (D : EquivalenceChain Source Middle₁ Middle₂ Target) :
    Source ≃ Target :=
  D.first.trans (D.second.trans D.third)

@[simp]
theorem EquivalenceChain.correspondence_apply
    {Source Middle₁ Middle₂ Target : Type*}
    (D : EquivalenceChain Source Middle₁ Middle₂ Target) (x : Source) :
    D.correspondence x = D.third (D.second (D.first x)) :=
  rfl

/-- A bijection together with equivariance for two supplied actions. -/
structure EquivariantEquiv
    (Automorphism Source Target : Type*)
    (sourceAction : Automorphism → Source → Source)
    (targetAction : Automorphism → Target → Target) where
  toEquiv : Source ≃ Target
  equivariant : ∀ a x,
    toEquiv (sourceAction a x) = targetAction a (toEquiv x)

/-- Pointwise fixation of the endpoints makes every map between them
equivariant. -/
theorem equivariant_of_pointwise_fixed
    {Automorphism Source Middle₁ Middle₂ Target : Type*}
    {sourceAction : Automorphism → Source → Source}
    {targetAction : Automorphism → Target → Target}
    (D : EquivalenceChain Source Middle₁ Middle₂ Target)
    (sourceFixed :
      EvenFieldFixed.PointwiseFixed sourceAction Set.univ)
    (targetFixed :
      EvenFieldFixed.PointwiseFixed targetAction Set.univ) :
    ∀ a x,
      D.correspondence (sourceAction a x) =
        targetAction a (D.correspondence x) := by
  intro a x
  rw [sourceFixed a x (Set.mem_univ x),
    targetFixed a (D.correspondence x) (Set.mem_univ _)]

/-! ## Published and preceding-lemma inputs -/

/-- The classes occurring in the coproduct in Feng--Malle--Zhang,
Theorem 7.5 and equation (7.2). -/
abbrev RestrictedPairClass
    (PairClass : Type*)
    (IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC :
      PairClass → Prop) :=
  {p : PairClass //
    IsEJGCClass p ∧ LocalCharacterInEllPrimeSeries p ∧ InducesBlockC p}

/-- The actual defect-zero-character family in Feng--Malle--Zhang,
equation (7.2).  The relative Weyl group may depend on the restricted
conjugacy class of the pair. -/
abbrev DefectZeroUnion
    {PairClass : Type}
    {IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC :
      PairClass → Prop}
    (RelativeWeylGroup :
      RestrictedPairClass PairClass IsEJGCClass
        LocalCharacterInEllPrimeSeries InducesBlockC → Type)
    [∀ p, Group (RelativeWeylGroup p)]
    (IsDefectZero : ∀ p, Irr ℂ (RelativeWeylGroup p) → Prop) :=
  Σ p, {chi : Irr ℂ (RelativeWeylGroup p) // IsDefectZero p chi}

/-- A group isomorphism induces an equivalence between the sets of ordinary
irreducible characters. Applying this construction to the finite
normaliser isomorphism gives the required equivalence without an
additional assumption. -/
noncomputable def irrEquivOfMulEquiv {G K : Type} [Group G] [Group K]
    (e : G ≃* K) : Irr ℂ G ≃ Irr ℂ K where
  toFun := transportIrr e
  invFun := transportIrr e.symm
  left_inv chi := by
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    simp [transportIrr_apply]
  right_inv chi := by
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    simp [transportIrr_apply]

/-- Source-shaped inputs for the existence argument in Lemma 3.7.

The source and target are now the literal semantic carriers `X_C` and
`W(C)`.  Cabanes--Enguehard, Theorem 4.4(i), is stored as the set equality it
states.  Cabanes--Späth, Theorem 2.8, is stored in its published orientation,
and Remark 3.5 supplies a group isomorphism, not a free character-set
equivalence.  Feng--Malle--Zhang, Theorem 7.5 and equation (7.2), supply the
remaining cited bijection.  The final field is the cardinality identity in
Section 7.1 immediately before Question 7.1.  No map from the defect-zero
union to `W(C)` is supplied. -/
structure CitedData
    (H A Block Dual : Type)
    [Group H] [Group Dual] [MulAction (MulAut H) A]
    (ell : ℕ) (InBlock : Irr ℂ H → Prop)
    (Series : Irr ℂ H → Dual → Prop)
    (genericDefinitions : Definitions ℂ H A Block)
    (innerCoherence : InnerCoherence genericDefinitions) (C : Block)
    (GeneralisedSeries : Set (Irr ℂ H))
    (CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass : Type)
    [Group CitedRelativeWeylGroup] [Group ManuscriptRelativeWeylGroup]
    (IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC :
      PairClass → Prop)
    (RelativeWeylGroup :
      RestrictedPairClass PairClass IsEJGCClass
        LocalCharacterInEllPrimeSeries InducesBlockC → Type)
    [∀ p, Group (RelativeWeylGroup p)]
    (IsDefectZero : ∀ p, Irr ℂ (RelativeWeylGroup p) → Prop)
    [Fintype (W genericDefinitions innerCoherence C)]
    [Fintype (DefectZeroUnion RelativeWeylGroup IsDefectZero)] where
  /-- Cabanes--Enguehard, Theorem 4.4(i), restricted to the block `C`. -/
  cabanesEnguehardTheorem44 :
    unipotentBlockPart InBlock Series = GeneralisedSeries
  /-- Cabanes--Späth, Theorem 2.8, in its published orientation. -/
  cabanesSpathTheorem28 :
    Irr ℂ CitedRelativeWeylGroup ≃ ↑GeneralisedSeries
  /-- The fixed-point relative Weyl group in Cabanes--Späth, Remark 3.5,
  identified with the finite normaliser quotient used in the manuscript. -/
  finiteRelativeWeylIdentification :
    ManuscriptRelativeWeylGroup ≃* CitedRelativeWeylGroup
  /-- Feng--Malle--Zhang, Theorem 7.5 and equation (7.2). -/
  fmzTheorem75 :
    Irr ℂ ManuscriptRelativeWeylGroup ≃
      DefectZeroUnion RelativeWeylGroup IsDefectZero
  /-- Feng--Malle--Zhang, Section 7.1 immediately before Question 7.1,
  after Assumption 3.19 and its type-C verification in Proposition 3.20 have
  been instantiated. -/
  fmzWeightCardinality :
    Fintype.card (W genericDefinitions innerCoherence C) =
      Fintype.card (DefectZeroUnion RelativeWeylGroup IsDefectZero)

variable
    {H A Block Dual E CitedRelativeWeylGroup
      ManuscriptRelativeWeylGroup PairClass : Type}
    [Group H] [Group Dual] [MulAction (MulAut H) A] [Group E]
    [Group CitedRelativeWeylGroup] [Group ManuscriptRelativeWeylGroup]
    {ell : ℕ} {InBlock : Irr ℂ H → Prop}
    {Series : Irr ℂ H → Dual → Prop}
    {genericDefinitions : Definitions ℂ H A Block}
    {innerCoherence : InnerCoherence genericDefinitions} {C : Block}
    {GeneralisedSeries : Set (Irr ℂ H)}
    {IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC :
      PairClass → Prop}
    {RelativeWeylGroup :
      RestrictedPairClass PairClass IsEJGCClass
        LocalCharacterInEllPrimeSeries InducesBlockC → Type}
    [∀ p, Group (RelativeWeylGroup p)]
    {IsDefectZero : ∀ p, Irr ℂ (RelativeWeylGroup p) → Prop}
    [Fintype (W genericDefinitions innerCoherence C)]
    [Fintype (DefectZeroUnion RelativeWeylGroup IsDefectZero)]
    {fieldAction : E →* MulAut H}

/-- The first manuscript arrow.  Its first step is derived from E1 and E2 in
Lemma 3.6, and the character equivalence attached to the finite relative
Weyl group is derived from the cited group isomorphism. -/
noncomputable def CitedData.characterToRelativeWeyl
    (D : CitedData H A Block Dual ell InBlock Series
      genericDefinitions innerCoherence C GeneralisedSeries
      CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass
      IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
      RelativeWeylGroup IsDefectZero)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series) :
    ↑(XC ell InBlock Series) ≃ Irr ℂ ManuscriptRelativeWeylGroup :=
  (Equiv.setCongr
      (XC_eq_unipotentBlockPart ell InBlock Series
        blockSeries seriesDisjoint)).trans
    ((Equiv.setCongr D.cabanesEnguehardTheorem44).trans
      (D.cabanesSpathTheorem28.symm.trans
        (irrEquivOfMulEquiv D.finiteRelativeWeylIdentification).symm))

/-- The noncanonical target-side equivalence constructed from the published
cardinality identity; no weight-construction from orbit representatives map is assumed. -/
noncomputable def CitedData.weightToDefectZeroUnion
    (D : CitedData H A Block Dual ell InBlock Series
      genericDefinitions innerCoherence C GeneralisedSeries
      CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass
      IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
      RelativeWeylGroup IsDefectZero) :
    W genericDefinitions innerCoherence C ≃
      DefectZeroUnion RelativeWeylGroup IsDefectZero :=
  Fintype.equivOfCardEq D.fmzWeightCardinality

/-- The three equivalences in the orientation used by manuscript Lemma 3.7. -/
noncomputable def CitedData.equivalenceChain
    (D : CitedData H A Block Dual ell InBlock Series
      genericDefinitions innerCoherence C GeneralisedSeries
      CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass
      IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
      RelativeWeylGroup IsDefectZero)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series) :
    EquivalenceChain (↑(XC ell InBlock Series))
      (Irr ℂ ManuscriptRelativeWeylGroup)
      (DefectZeroUnion RelativeWeylGroup IsDefectZero)
      (W genericDefinitions innerCoherence C) where
  first := D.characterToRelativeWeyl blockSeries seriesDisjoint
  second := D.fmzTheorem75
  third := D.weightToDefectZeroUnion.symm

/-! ## The actual right actions on the two endpoint carriers -/

/-- Right transport of a character in `X_C`.  Membership follows from the
ordinary-character half of Lemma 3.6, not from a separately supplied action
on an arbitrary type. -/
noncomputable def characterRightTransport
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction)
    (sigma : E) (chi : ↑(XC ell InBlock Series)) :
  ↑(XC ell InBlock Series) :=
  ⟨twist ℂ H chi.1 (fieldAction sigma), by
    have hfixed := fixation.1 sigma chi.1 chi.2
    simpa only [hfixed] using chi.2⟩

omit [Fintype (W genericDefinitions innerCoherence C)] in
@[simp]
theorem characterRightTransport_eq_self
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction)
    (sigma : E) (chi : ↑(XC ell InBlock Series)) :
    characterRightTransport fixation sigma chi = chi := by
  apply Subtype.ext
  exact fixation.1 sigma chi.1 chi.2

/-- Right transport of a valid generic pair.  Its validity witness is the
one produced by the generic-weight half of Lemma 3.6. -/
noncomputable def validPairRightTransport
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction)
    (sigma : E) (v : GenericPair genericDefinitions innerCoherence C) :
    GenericPair genericDefinitions innerCoherence C :=
  ⟨rightTransportPair v.1 (fieldAction sigma),
    Classical.choose (fixation.2 sigma v)⟩

omit [Fintype (W genericDefinitions innerCoherence C)] in
/-- Right transport intertwines inner conjugation with the inverse field
automorphism, so it descends to conjugacy classes. -/
theorem validPairRightTransport_inner
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction)
    (sigma : E) (h : H)
    (v : GenericPair genericDefinitions innerCoherence C) :
    validPairRightTransport fixation sigma (h • v) =
      (fieldAction sigma).symm h •
        validPairRightTransport fixation sigma v := by
  apply Subtype.ext
  change (fieldAction sigma).symm • ((MulAut.conj h) • v.1) =
    (MulAut.conj ((fieldAction sigma).symm h)) •
      ((fieldAction sigma).symm • v.1)
  rw [← mul_smul, ← mul_smul]
  congr 1
  ext x
  simp

omit [Fintype (W genericDefinitions innerCoherence C)] in
/-- The representative-level equality supplied by the generic-weight half
of Lemma 3.6, with exactly the validity witness selected above. -/
theorem validPairRightTransport_class_eq
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction)
    (sigma : E) (v : GenericPair genericDefinitions innerCoherence C) :
    validConjugacyClass (innerStablePredicate genericDefinitions
        innerCoherence C) (validPairRightTransport fixation sigma v) =
      validConjugacyClass (innerStablePredicate genericDefinitions
        innerCoherence C) v := by
  simpa [validPairRightTransport] using
    (Classical.choose_spec (fixation.2 sigma v))

/-- The right transport of generic pairs descends to the literal orbit
quotient defining `W(C)`. -/
noncomputable def genericWeightRightTransport
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction)
    (sigma : E) :
    W genericDefinitions innerCoherence C →
      W genericDefinitions innerCoherence C :=
  inducedOrbitMap (fieldAction sigma).symm.toMonoidHom
    (validPairRightTransport fixation sigma)
    (validPairRightTransport_inner fixation sigma)

omit [Fintype (W genericDefinitions innerCoherence C)] in
@[simp]
theorem genericWeightRightTransport_mk
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction)
    (sigma : E) (v : GenericPair genericDefinitions innerCoherence C) :
    genericWeightRightTransport fixation sigma
        (validConjugacyClass (innerStablePredicate genericDefinitions
          innerCoherence C) v) =
      validConjugacyClass (innerStablePredicate genericDefinitions
        innerCoherence C) (validPairRightTransport fixation sigma v) :=
  rfl

omit [Fintype (W genericDefinitions innerCoherence C)] in
/-- The descended action is pointwise trivial by the exact
generic-weight conclusion of Lemma 3.6. -/
theorem genericWeightRightTransport_eq_self
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction)
    (sigma : E) (omega : W genericDefinitions innerCoherence C) :
    genericWeightRightTransport fixation sigma omega = omega := by
  refine Quotient.inductionOn omega ?_
  intro v
  change validConjugacyClass (innerStablePredicate genericDefinitions
      innerCoherence C) (validPairRightTransport fixation sigma v) =
    validConjugacyClass (innerStablePredicate genericDefinitions
      innerCoherence C) v
  exact validPairRightTransport_class_eq fixation sigma v

/-- The manuscript's right action on `X_C`, represented as a left action of
the opposite field-automorphism group. -/
@[instance_reducible]
noncomputable def characterOppositeMulAction
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction) :
    MulAction Eᵐᵒᵖ (↑(XC ell InBlock Series)) where
  smul sigma chi := characterRightTransport fixation sigma.unop chi
  one_smul chi := by
    change characterRightTransport fixation 1 chi = chi
    exact characterRightTransport_eq_self fixation 1 chi
  mul_smul sigma tau chi := by
    change characterRightTransport fixation (sigma * tau).unop chi =
      characterRightTransport fixation sigma.unop
        (characterRightTransport fixation tau.unop chi)
    rw [characterRightTransport_eq_self,
      characterRightTransport_eq_self,
      characterRightTransport_eq_self]

/-- The manuscript's right action on `W(C)`, represented as a left action of
the opposite field-automorphism group. -/
@[instance_reducible]
noncomputable def genericWeightOppositeMulAction
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction) :
    MulAction Eᵐᵒᵖ (W genericDefinitions innerCoherence C) where
  smul sigma omega := genericWeightRightTransport fixation sigma.unop omega
  one_smul omega := by
    change genericWeightRightTransport fixation 1 omega = omega
    exact genericWeightRightTransport_eq_self fixation 1 omega
  mul_smul sigma tau omega := by
    change genericWeightRightTransport fixation (sigma * tau).unop omega =
      genericWeightRightTransport fixation sigma.unop
        (genericWeightRightTransport fixation tau.unop omega)
    rw [genericWeightRightTransport_eq_self,
      genericWeightRightTransport_eq_self,
      genericWeightRightTransport_eq_self]

/-- Lemma 3.7 as a project-relative existence statement on the literal
semantic carriers.  The only endpoint fixation input is the exact conclusion
of Lemma 3.6.  The equivariance is with respect to the actual right transports
on `X_C` and `W(C)`, encoded as left actions of `Eᵐᵒᵖ`. -/
noncomputable def equivariantCorrespondence
    (D : CitedData H A Block Dual ell InBlock Series
      genericDefinitions innerCoherence C GeneralisedSeries
      CitedRelativeWeylGroup ManuscriptRelativeWeylGroup PairClass
      IsEJGCClass LocalCharacterInEllPrimeSeries InducesBlockC
      RelativeWeylGroup IsDefectZero)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series)
    (fixation : FixationConclusion ell InBlock Series genericDefinitions
      innerCoherence C fieldAction) :
    EquivariantEquiv Eᵐᵒᵖ (↑(XC ell InBlock Series))
      (W genericDefinitions innerCoherence C)
      (characterOppositeMulAction fixation).smul
      (genericWeightOppositeMulAction fixation).smul where
  toEquiv := D.equivalenceChain blockSeries seriesDisjoint |>.correspondence
  equivariant := by
    intro sigma chi
    change (D.equivalenceChain blockSeries seriesDisjoint).correspondence
        (characterRightTransport fixation sigma.unop chi) =
      genericWeightRightTransport fixation sigma.unop
        ((D.equivalenceChain blockSeries seriesDisjoint).correspondence chi)
    rw [characterRightTransport_eq_self,
      genericWeightRightTransport_eq_self]

end ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
