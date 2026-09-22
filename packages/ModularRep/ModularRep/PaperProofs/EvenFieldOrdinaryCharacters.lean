import ModularRep.EvenFieldFixed
import ModularRep.OrdinaryIrreducibleCharacter

/-!
# Ordinary-character half of manuscript Lemma 3.6

The set of characters is the semantic function-valued `Irr(H)`, and the field
action is pullback along an actual group automorphism.  The Deligne--Lusztig
inputs remain exact predicates about rational-series labels.
-/

namespace ModularRep.PaperProofs.EvenFieldOrdinaryCharacters

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.ManuscriptVerification.EvenFieldFixed

universe u

variable {k H Dual : Type u} [Field k] [CharZero k]
  [Group H] [Group Dual]

/-- **E1 (published input).**  The exact part of
Cabanes--Enguehard, Theorem 4.4(iii), used here: every character in the
selected unipotent block has a rational-series label annihilated by an
`ell`-power.  `Series` is deliberately an abstract relation; this definition
does not claim to construct Lusztig series in Lean. -/
abbrev E1BlockEllSeriesInput (ell : ℕ) (InBlock : Irr k H → Prop)
    (Series : Irr k H → Dual → Prop) : Prop :=
  ∀ chi : Irr k H, InBlock chi →
    ∃ t : Dual, Series chi t ∧ ∃ a : ℕ, t ^ (ell ^ a) = 1

/-- **E2 (published input).**  The overlap consequence of the rational
Lusztig-series partition in Cabanes--Späth, Theorem 2.7: two labels of the
same irreducible character are conjugate.  It is global in the character and
both labels, rather than specialised to a character selected by the target. -/
abbrev E2CommonSeriesLabelsConjugateInput
    (Series : Irr k H → Dual → Prop) : Prop :=
  ∀ {chi : Irr k H} {s t : Dual}, Series chi s → Series chi t →
    ∃ x : Dual, t = x * s * x⁻¹

/-- The manuscript set `X_C`: characters in the selected block that also lie
in a rational series with a semisimple `ell'` label. -/
def XC (ell : ℕ) (InBlock : Irr k H → Prop)
    (Series : Irr k H → Dual → Prop) : Set (Irr k H) :=
  {chi | InBlock chi ∧ ∃ s : Dual, Series chi s ∧ IsPrimeRegular ell s}

/-- The characters in the selected block and the identity rational series.
For the intended instantiation, this is `Irr(C) ∩ E(H, 1)`. -/
def unipotentBlockPart (InBlock : Irr k H → Prop)
    (Series : Irr k H → Dual → Prop) : Set (Irr k H) :=
  {chi | InBlock chi ∧ Series chi 1}

omit [CharZero k] in
/-- Manuscript lines 303--310: E1 and E2 collapse the `ell`-element and
`ell'`-element labels to the identity.  The reverse inclusion uses that the
identity label is `ell`-regular. -/
theorem XC_eq_unipotentBlockPart
    (ell : ℕ) (InBlock : Irr k H → Prop)
    (Series : Irr k H → Dual → Prop)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series) :
    XC ell InBlock Series = unipotentBlockPart InBlock Series := by
  ext chi
  constructor
  · rintro ⟨hblock, s, hsSeries, hsRegular⟩
    obtain ⟨t, htSeries, htPower⟩ := blockSeries chi hblock
    exact ⟨hblock,
      common_series_primePower_primeRegular_is_unipotent
        Series seriesDisjoint hsSeries htSeries hsRegular htPower⟩
  · rintro ⟨hblock, hUnipotent⟩
    exact ⟨hblock, 1, hUnipotent, isPrimeRegular_one⟩

/-- **E3 (published input).**  The general statement used from the proof of
Cabanes--Späth, Theorem 3.4: every standard field automorphism fixes every
unipotent character.  Both quantifiers are explicit; in particular this
interface cannot carry fixedness of a character preselected by the target. -/
abbrev E3StandardFieldFixesUnipotentInput
    {FieldAutomorphism : Type u} [Group FieldAutomorphism]
    (Series : Irr k H → Dual → Prop)
    (fieldAutomorphism : FieldAutomorphism →* MulAut H) : Prop :=
  ∀ sigma chi, Series chi 1 →
    twist k H chi (fieldAutomorphism sigma) = chi

omit [CharZero k] in
/-- Ordinary-character endpoint of manuscript Lemma 3.6: every element of
the typed standard-field-automorphism group fixes `X_C` pointwise.  The only
fixedness input is E3, universally quantified over all field automorphisms and
all characters in the identity series. -/
theorem XC_pointwise_fixed
    {FieldAutomorphism : Type u} [Group FieldAutomorphism]
    (ell : ℕ) (InBlock : Irr k H → Prop)
    (Series : Irr k H → Dual → Prop)
    (fieldAutomorphism : FieldAutomorphism →* MulAut H)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series)
    (fieldFixesUnipotent :
      E3StandardFieldFixesUnipotentInput Series fieldAutomorphism) :
    PointwiseFixed
      (fun sigma chi ↦ twist k H chi (fieldAutomorphism sigma))
      (XC ell InBlock Series) := by
  intro sigma chi hchi
  apply fieldFixesUnipotent sigma chi
  have hUnipotent : chi ∈ unipotentBlockPart InBlock Series := by
    rw [← XC_eq_unipotentBlockPart ell InBlock Series
      blockSeries seriesDisjoint]
    exact hchi
  exact hUnipotent.2

omit [CharZero k] in
/-- The two ordinary-character conclusions used later in the manuscript,
exported together: the exact identity-series description of `X_C` and its
pointwise fixation by the full typed field-automorphism group. -/
theorem XC_eq_unipotentBlockPart_and_pointwise_fixed
    {FieldAutomorphism : Type u} [Group FieldAutomorphism]
    (ell : ℕ) (InBlock : Irr k H → Prop)
    (Series : Irr k H → Dual → Prop)
    (fieldAutomorphism : FieldAutomorphism →* MulAut H)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series)
    (fieldFixesUnipotent :
      E3StandardFieldFixesUnipotentInput Series fieldAutomorphism) :
    XC ell InBlock Series = unipotentBlockPart InBlock Series ∧
      PointwiseFixed
        (fun sigma chi ↦ twist k H chi (fieldAutomorphism sigma))
        (XC ell InBlock Series) :=
  ⟨XC_eq_unipotentBlockPart ell InBlock Series blockSeries seriesDisjoint,
    XC_pointwise_fixed ell InBlock Series fieldAutomorphism
      blockSeries seriesDisjoint fieldFixesUnipotent⟩

omit [CharZero k] in
/-- Single-automorphism corollary retained for downstream callers.  The
full-group endpoint is `XC_pointwise_fixed`. -/
theorem XC_fixed
    (ell : ℕ) (InBlock : Irr k H → Prop)
    (Series : Irr k H → Dual → Prop)
    (alpha : MulAut H)
    (blockSeries : E1BlockEllSeriesInput ell InBlock Series)
    (seriesDisjoint : E2CommonSeriesLabelsConjugateInput Series)
    (fieldFixesUnipotent : ∀ chi : Irr k H,
      Series chi 1 → twist k H chi alpha = chi) :
    ∀ chi : Irr k H, chi ∈ XC ell InBlock Series →
      twist k H chi alpha = chi := by
  intro chi hchi
  obtain ⟨hblock, s, hsSeries, hsRegular⟩ := hchi
  obtain ⟨t, htSeries, htPower⟩ := blockSeries chi hblock
  exact common_series_character_fixed Series (twist k H · alpha)
    seriesDisjoint fieldFixesUnipotent hsSeries htSeries hsRegular htPower

end ModularRep.PaperProofs.EvenFieldOrdinaryCharacters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
