import ModularRep.PaperProofs.EvenFieldLemma35Relative

/-!
# Source-faithful E1--E4 providers for Lemma 3.6

This module exposes the ordinary-character and rational-series inputs used in
the relative proof of Lemma 3.6.  The coefficient field is `ℂ`, as in the
ordinary-character statements in the cited literature.

The source boundary is deliberately more rigid than the abstract deduction:

* a block is represented by the fibre of a block-labelling map on the actual
  function-valued carrier `Irr ℂ H`;
* `Dual` is a finite group and semisimple labels form a distinguished subset
  of that full group;
* a finite dual Levi is a literal subgroup of `Dual`, so its labels enter the
  ambient dual group through the subgroup inclusion rather than by an
  untyped identification;
* the field group acts homomorphically on the finite fixed-point group, while
  its algebraic lifts are only a pointwise family of automorphisms.

No structure below contains the equality describing `X_C`, fixation of
`X_C`, fixation of a selected Levi character, fixation of a generic-weight
orbit, or either conclusion of Lemma 3.6.  Deligne--Lusztig theory and block
theory remain external inputs; this module only states their exact interfaces
and checks their transport into `GlobalInputs`.

The source map is: E1, Cabanes--Enguehard, proof of Theorem 4.4(iii),
p. 164; E2, Cabanes--Späth, Theorem 2.7, pp. 696--697; E3,
Cabanes--Späth, proof of Theorem 3.4, p. 700; and E4,
Feng--Malle--Zhang, proof of Lemma 3.27, first paragraph, pp. 14--15.
-/

namespace ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers

open ModularRep.ManuscriptVerification.EvenFieldFixed
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldGenericLeviSeries
open ModularRep.PaperProofs.EvenFieldLemma35Relative
open ModularRep.PaperProofs.EvenFieldLeviTorus
open ModularRep.PaperProofs.EvenFieldSourceShaped

/-- A block labelling on the set of ordinary characters.

For an actual finite group this map is `χ ↦ bl(χ)`.  The characters in a
block are its fibre, rather than an arbitrary predicate selected after the
target set is known. -/
structure OrdinaryBlockCarrier
    (H Block : Type) [Group H] where
  blockOf : Irr ℂ H → Block

/-- The ordinary irreducible characters in the block `C`. -/
def OrdinaryBlockCarrier.characters
    {H Block : Type} [Group H]
    (B : OrdinaryBlockCarrier H Block) (C : Block) : Set (Irr ℂ H) :=
  {chi | B.blockOf chi = C}

/-- Source data for rational Lusztig series indexed by elements of the full
finite dual group.

`semisimple` is only a subset of `Dual`; it is not used as the carrier of the
dual group.  The final three fields are the element-indexed form of the
partition by rational series: every irreducible character has a semisimple
label, conjugate labels give the same series, and two labels of one character
are conjugate. -/
structure RationalSeriesSource
    (H Dual : Type) [Group H] [Group Dual] [Fintype Dual] where
  groupFintype : Fintype H
  semisimple : Set Dual
  one_semisimple : (1 : Dual) ∈ semisimple
  series : Irr ℂ H → Dual → Prop
  series_label_semisimple :
    ∀ {chi : Irr ℂ H} {s : Dual}, series chi s → s ∈ semisimple
  series_conjugate : ∀ (chi : Irr ℂ H) (s x : Dual),
    series chi (x * s * x⁻¹) ↔ series chi s
  series_label_exists : ∀ chi : Irr ℂ H,
    ∃ s : Dual, s ∈ semisimple ∧ series chi s
  common_series_labels_conjugate :
    ∀ {chi : Irr ℂ H} {s t : Dual}, series chi s → series chi t →
      ∃ x : Dual, t = x * s * x⁻¹

/-- E2 in the smaller form consumed by the checked deduction.  It is derived
from the full rational-series source rather than supplied independently. -/
theorem RationalSeriesSource.toE2Input
    {H Dual : Type} [Group H] [Group Dual] [Fintype Dual]
    (R : RationalSeriesSource H Dual) :
    EvenFieldOrdinaryCharacters.E2CommonSeriesLabelsConjugateInput R.series :=
  R.common_series_labels_conjugate

/-- Rational-series data for the dual Levi attached to each admissible torus
label.  Each `dualLevi T` is a subgroup of the full finite dual group, so the
coercion in `embeddedSeries` is the required local-to-global label map. -/
structure LocalLeviSeriesSource
    {H A Block Dual : Type} [Group H] [Group Dual] [Fintype Dual]
    [MulAction (MulAut H) A]
    (D : Definitions ℂ H A Block)
    (globalSeries : RationalSeriesSource H Dual) where
  dualLevi : A → Subgroup Dual
  series : (T : A) → Irr ℂ (D.levi T) → dualLevi T → Prop
  series_label_semisimple : ∀ (T : A) (chi : Irr ℂ (D.levi T))
      (s : dualLevi T), series T chi s →
        (s : Dual) ∈ globalSeries.semisimple

/-- The local rational series viewed in the full dual group through the
literal dual-Levi inclusion. -/
def LocalLeviSeriesSource.embeddedSeries
    {H A Block Dual : Type} [Group H] [Group Dual] [Fintype Dual]
    [MulAction (MulAut H) A]
    {D : Definitions ℂ H A Block}
    {globalSeries : RationalSeriesSource H Dual}
    (L : LocalLeviSeriesSource D globalSeries) :
    (T : A) → Irr ℂ (D.levi T) → Dual → Prop :=
  fun T chi s ↦ ∃ t : L.dualLevi T, L.series T chi t ∧ (t : Dual) = s

/-- E3 for a finite rational Levi, with its own dual Levi retained as a
subgroup of the ambient finite dual group. -/
structure StandardLeviE3Source
    (L E Dual : Type) [Group L] [Group E] [Group Dual] [Fintype Dual] where
  groupFintype : Fintype L
  fieldGroupFintype : Fintype E
  dualLevi : Subgroup Dual
  series : Irr ℂ L → dualLevi → Prop
  fieldAction : E →* MulAut L
  fieldFixesUnipotent : ∀ (sigma : E) (chi : Irr ℂ L),
    series chi 1 → twist ℂ L chi (fieldAction sigma) = chi

/-- The standard-Levi series embedded into the ambient dual group. -/
def StandardLeviE3Source.embeddedSeries
    {L E Dual : Type} [Group L] [Group E] [Group Dual] [Fintype Dual]
    (S : StandardLeviE3Source L E Dual) : Irr ℂ L → Dual → Prop :=
  fun chi s ↦ ∃ t : S.dualLevi, S.series chi t ∧ (t : Dual) = s

/-- Convert the exact standard-Levi E3 statement to the global-label form
used by `PairGeometrySource`.  Injectivity of the subgroup inclusion shows
that a local label mapping to the global identity is the local identity. -/
theorem StandardLeviE3Source.toE3Input
    {L E Dual : Type} [Group L] [Group E] [Group Dual] [Fintype Dual]
    (S : StandardLeviE3Source L E Dual) :
    EvenFieldOrdinaryCharacters.E3StandardFieldFixesUnipotentInput
      S.embeddedSeries S.fieldAction := by
  intro sigma chi hseries
  obtain ⟨s, hs, hsOne⟩ := hseries
  have hLocal : s = 1 := by
    apply Subtype.ext
    simpa using hsOne
  subst s
  exact S.fieldFixesUnipotent sigma chi hs

variable {Gbar A Block E Dual : Type}
    [Group Gbar] [Group E] [Group Dual] [Fintype Dual]

variable (F : Gbar →* Gbar) (algebraicLift : E → MulAut Gbar)

abbrev H := frobeniusFixedSubgroup F

/-- Exact E1--E4 source package for one unipotent block.

E1 is the `ell`-series containment for the fibre of `blocks.blockOf` over
`C`.  E2 is part of `globalSeries`.  E3 is universally quantified over the
finite field group.  E4 compares the local dual-Levi label of every literal
FMZ witness with the selected block label after inclusion in the full dual
group.  No field states a consequence obtained by combining these inputs. -/
structure ExactE1E4Provider
    [MulAction (MulAut (H F)) A]
    (ell : ℕ) (D : Definitions ℂ (H F) A Block) (C : Block) where
  ellPrime : Nat.Prime ell
  fieldGroupFintype : Fintype E
  blocks : OrdinaryBlockCarrier (H F) Block
  globalSeries : RationalSeriesSource (H F) Dual
  algebraicLift_commutes : ∀ (sigma : E) (x : Gbar),
    F (algebraicLift sigma x) = algebraicLift sigma (F x)
  fieldAction : E →* MulAut (H F)
  fieldAction_coe : ∀ (sigma : E) (x : H F),
    ((fieldAction sigma x : H F) : Gbar) = algebraicLift sigma (x : Gbar)
  e1BlockSeries : ∀ chi : Irr ℂ (H F), blocks.blockOf chi = C →
    ∃ t : Dual, globalSeries.series chi t ∧
      ∃ a : ℕ, t ^ (ell ^ a) = 1
  e3FieldFixesUnipotent : ∀ (sigma : E) (chi : Irr ℂ (H F)),
    globalSeries.series chi 1 →
      twist ℂ (H F) chi (fieldAction sigma) = chi
  blockLabel : Dual
  blockLabel_eq_one : blockLabel = 1
  localSeries : LocalLeviSeriesSource D globalSeries
  e4LocalLabelComparison :
    ∀ (P : LocalPair ℂ (H F) A) (generic : GenericWitness D C P),
      ∃ (s : localSeries.dualLevi P.1) (x : Dual),
        localSeries.series P.1 generic.lambda s ∧
          (s : Dual) = x * blockLabel * x⁻¹

/-- The actual block predicate supplied to the abstract deduction. -/
def ExactE1E4Provider.inBlock
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {D : Definitions ℂ (H F) A Block} {C : Block}
    (S : ExactE1E4Provider (Dual := Dual) F algebraicLift ell D C) :
    Irr ℂ (H F) → Prop :=
  fun chi ↦ S.blocks.blockOf chi = C

/-- E1 in the exact smaller form consumed by `GlobalInputs`. -/
theorem ExactE1E4Provider.toE1Input
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {D : Definitions ℂ (H F) A Block} {C : Block}
    (S : ExactE1E4Provider (Dual := Dual) F algebraicLift ell D C) :
    EvenFieldOrdinaryCharacters.E1BlockEllSeriesInput
      ell S.inBlock S.globalSeries.series :=
  S.e1BlockSeries

/-- E3 in the exact smaller form consumed by `GlobalInputs`. -/
theorem ExactE1E4Provider.toE3Input
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {D : Definitions ℂ (H F) A Block} {C : Block}
    (S : ExactE1E4Provider (Dual := Dual) F algebraicLift ell D C) :
    EvenFieldOrdinaryCharacters.E3StandardFieldFixesUnipotentInput
      S.globalSeries.series S.fieldAction :=
  S.e3FieldFixesUnipotent

/-- E4 after inserting the literal dual-Levi inclusions.  The block-label
function is constant only because the abstract downstream interface asks for
a function on all blocks while this provider concerns one fixed block.  No
claim about the labels of other blocks is made or used. -/
theorem ExactE1E4Provider.toE4Input
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {D : Definitions ℂ (H F) A Block} {C : Block}
    (S : ExactE1E4Provider (Dual := Dual) F algebraicLift ell D C) :
    E4GenericLabelComparisonInput D C (fun _ ↦ S.blockLabel)
      S.localSeries.embeddedSeries := by
  intro P generic
  obtain ⟨s, x, hs, hsLabel⟩ := S.e4LocalLabelComparison P generic
  exact ⟨(s : Dual), x, ⟨s, hs, rfl⟩, hsLabel⟩

/-- Combine only the E1--E4 fields of `GlobalInputs`, together with the
independently supplied characteristic-torus realisation.  This is an adapter,
not a proof of either conclusion of Lemma 3.6. -/
def ExactE1E4Provider.toGlobalInputs
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {D : Definitions ℂ (H F) A Block} {C : Block}
    (S : ExactE1E4Provider (Dual := Dual) F algebraicLift ell D C)
    (centralSylow : Subgroup Gbar → Subgroup Gbar)
    (centralSylow_natural : CharacteristicTorusNatural centralSylow)
    (realise : A → Subgroup Gbar)
    (realise_injective : Function.Injective realise) :
    GlobalInputs F algebraicLift ell S.inBlock S.globalSeries.series D C where
  fieldAction := S.fieldAction
  fieldAction_coe := S.fieldAction_coe
  blockSeries := S.toE1Input
  seriesDisjoint := S.globalSeries.toE2Input
  fieldFixesIdentitySeries := S.toE3Input
  blockLabel := fun _ ↦ S.blockLabel
  blockLabel_eq_one := S.blockLabel_eq_one
  selectedSeries := S.localSeries.embeddedSeries
  labelComparison := S.toE4Input
  centralSylow := centralSylow
  centralSylow_natural := centralSylow_natural
  realise := realise
  realise_injective := realise_injective

end ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
