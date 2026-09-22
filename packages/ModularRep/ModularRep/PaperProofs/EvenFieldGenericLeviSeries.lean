import ModularRep.PaperProofs.EvenFieldFMZGenericPair
import ModularRep.PaperProofs.EvenFieldLeviCharacterFixation
import ModularRep.PaperProofs.EvenFieldOrdinaryCharacters
import ModularRep.PaperProofs.EvenFieldRationalLeviProvenance

/-!
# The E3--E4 interface for the selected generic Levi character

For a unipotent block, the label comparison in the proof of
Feng--Malle--Zhang, Lemma 3.27, says uniformly that the semisimple label of
the Levi character in every generic pair is conjugate to the identity.  This
module keeps that statement separate from the universal theorem that every
standard field automorphism fixes every identity-series character.

The series on the standard rational Levi and the series on the selected
finite Levi are separate source notions.  Their compatibility under the
actual finite-Levi equivalence is an explicit input.  Lean then derives
fixation of the literal FMZ witness character.  Neither selected-character
fixedness nor an arbitrary predicate chosen after that character is known is
an input.
-/

namespace ModularRep.PaperProofs.EvenFieldGenericLeviSeries

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLeviCharacterFixation
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters
open ModularRep.PaperProofs.EvenFieldRationalLeviProvenance

universe u

variable {k Gbar H A Block StandardLevi Dual FieldAutomorphism : Type u}
    [Field k] [CharZero k] [Group Gbar] [Group H]
    [MulAction (MulAut H) A] [Group StandardLevi] [Group Dual]
    [Group FieldAutomorphism]

/-- **E4 (published input).**  For every generic pair belonging to the fixed
block, the semisimple label of its literal FMZ Levi character is conjugate to
the semisimple label of the block.  This is global in the pair and its witness
and contains no automorphism or fixedness claim. -/
abbrev E4GenericLabelComparisonInput
    (D : Definitions k H A Block) (C : Block)
    (BlockLabel : Block → Dual)
    (LeviSeries : (T : A) → Irr k (D.levi T) → Dual → Prop) : Prop :=
  ∀ (P : LocalPair k H A) (generic : GenericWitness D C P),
    ∃ s x : Dual,
      LeviSeries P.1 generic.lambda s ∧
        s = x * BlockLabel C * x⁻¹

/-- **E3--E4 transport input.**  The canonical rational-series
parametrisations on the standard and selected finite Levis agree under the
specified rational-Levi equivalence.  The two predicates are intentionally
independent source notions rather than one being defined from the selected
character. -/
abbrev SeriesTransportAlongInput
    {D : Definitions k H A Block} {P : LocalPair k H A}
    (leviEquiv : StandardLevi ≃* D.levi P.1)
    (SelectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k StandardLevi → Dual → Prop) : Prop :=
  ∀ (chi : Irr k StandardLevi) (s : Dual),
    StandardSeries chi s ↔
      SelectedSeries P.1 (transportIrr leviEquiv chi) s

/-- Backwards-compatible form of `SeriesTransportAlongInput` for the older
rational-Levi package. -/
abbrev SeriesTransportInput
    {D : Definitions k H A Block} {P : LocalPair k H A}
    {sigmaBar : MulAut Gbar} {tauH : MulAut H}
    (R : Data (StandardLevi := StandardLevi) D P sigmaBar tauH)
    (SelectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k StandardLevi → Dual → Prop) : Prop :=
  SeriesTransportAlongInput R.leviEquiv SelectedSeries StandardSeries

/-- E4 implies that the pullback of the selected FMZ Levi character belongs
to the identity series of the standard finite Levi.  This formulation takes
only the actual group equivalence and can therefore be used with the unified
rational-Levi witness. -/
theorem pulledLambda_in_identitySeries_along
    {D : Definitions k H A Block} {C : Block} {P : LocalPair k H A}
    (generic : GenericWitness D C P)
    (leviEquiv : StandardLevi ≃* D.levi P.1)
    (BlockLabel : Block → Dual)
    (SelectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k StandardLevi → Dual → Prop)
    (seriesTransport :
      SeriesTransportAlongInput leviEquiv SelectedSeries StandardSeries)
    (blockLabel_eq_one : BlockLabel C = 1)
    (labelComparison :
      E4GenericLabelComparisonInput D C BlockLabel SelectedSeries) :
    StandardSeries (transportIrr leviEquiv.symm generic.lambda) 1 := by
  obtain ⟨s, x, hseries, hs⟩ := labelComparison P generic
  have hsOne : s = 1 := by
    calc
      s = x * BlockLabel C * x⁻¹ := hs
      _ = 1 := by simp [blockLabel_eq_one]
  rw [hsOne] at hseries
  apply (seriesTransport _ 1).2
  simpa only [transportIrr_symm_cancel] using hseries

/-- Universal E3 fixation, together with E4 and transport along the supplied
group equivalence, fixes the selected FMZ Levi character. -/
theorem selectedLambda_fixed_from_E3_E4_along
    {D : Definitions k H A Block} {C : Block} {P : LocalPair k H A}
    (generic : GenericWitness D C P)
    (leviEquiv : StandardLevi ≃* D.levi P.1)
    (BlockLabel : Block → Dual)
    (SelectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k StandardLevi → Dual → Prop)
    (seriesTransport :
      SeriesTransportAlongInput leviEquiv SelectedSeries StandardSeries)
    (blockLabel_eq_one : BlockLabel C = 1)
    (labelComparison :
      E4GenericLabelComparisonInput D C BlockLabel SelectedSeries)
    (sigmaLevi : MulAut StandardLevi)
    (fieldAction : FieldAutomorphism →* MulAut StandardLevi)
    (fieldElement : FieldAutomorphism)
    (sigmaLevi_eq : sigmaLevi = fieldAction fieldElement)
    (fieldFixesIdentitySeries :
      E3StandardFieldFixesUnipotentInput StandardSeries fieldAction)
    (tauFiniteLevi : MulAut (D.levi P.1))
    (intertwines : ∀ x : StandardLevi,
      leviEquiv (sigmaLevi x) = tauFiniteLevi (leviEquiv x)) :
    twist k (D.levi P.1) generic.lambda tauFiniteLevi = generic.lambda := by
  apply selectedLeviCharacter_fixed leviEquiv sigmaLevi tauFiniteLevi
    intertwines generic.lambda
    (fun chi => StandardSeries chi 1)
    (pulledLambda_in_identitySeries_along generic leviEquiv BlockLabel
      SelectedSeries StandardSeries seriesTransport blockLabel_eq_one
      labelComparison)
  intro chi hchi
  rw [sigmaLevi_eq]
  exact fieldFixesIdentitySeries fieldElement chi hchi

/-- E4 implies that the pullback of the selected FMZ Levi character belongs
to the identity series of the standard finite Levi. -/
theorem pulledLambda_in_identitySeries
    {D : Definitions k H A Block} {C : Block} {P : LocalPair k H A}
    (generic : GenericWitness D C P)
    {sigmaBar : MulAut Gbar} {tauH : MulAut H}
    (R : Data (StandardLevi := StandardLevi) D P sigmaBar tauH)
    (BlockLabel : Block → Dual)
    (SelectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k StandardLevi → Dual → Prop)
    (seriesTransport :
      SeriesTransportInput R SelectedSeries StandardSeries)
    (blockLabel_eq_one : BlockLabel C = 1)
    (labelComparison :
      E4GenericLabelComparisonInput D C BlockLabel SelectedSeries) :
    StandardSeries (transportIrr R.leviEquiv.symm generic.lambda) 1 := by
  exact pulledLambda_in_identitySeries_along generic R.leviEquiv BlockLabel
    SelectedSeries StandardSeries seriesTransport blockLabel_eq_one
    labelComparison

/-- Universal E3 fixation, together with E4 and the actual rational-Levi
transport, fixes the selected FMZ Levi character. -/
theorem selectedLambda_fixed_from_E3_E4
    {D : Definitions k H A Block} {C : Block} {P : LocalPair k H A}
    (generic : GenericWitness D C P)
    {sigmaBar : MulAut Gbar} {tauH : MulAut H}
    (R : Data (StandardLevi := StandardLevi) D P sigmaBar tauH)
    (BlockLabel : Block → Dual)
    (SelectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k StandardLevi → Dual → Prop)
    (seriesTransport :
      SeriesTransportInput R SelectedSeries StandardSeries)
    (blockLabel_eq_one : BlockLabel C = 1)
    (labelComparison :
      E4GenericLabelComparisonInput D C BlockLabel SelectedSeries)
    (fieldAction : FieldAutomorphism →* MulAut StandardLevi)
    (fieldElement : FieldAutomorphism)
    (sigmaLevi_eq : R.sigmaLevi = fieldAction fieldElement)
    (fieldFixesIdentitySeries :
      E3StandardFieldFixesUnipotentInput
        StandardSeries fieldAction)
    (tauFiniteLevi : MulAut (D.levi P.1))
    (intertwines : ∀ x : StandardLevi,
      R.leviEquiv (R.sigmaLevi x) = tauFiniteLevi (R.leviEquiv x)) :
    twist k (D.levi P.1) generic.lambda tauFiniteLevi = generic.lambda := by
  exact selectedLambda_fixed_from_E3_E4_along generic R.leviEquiv BlockLabel
    SelectedSeries StandardSeries seriesTransport blockLabel_eq_one
    labelComparison R.sigmaLevi fieldAction fieldElement sigmaLevi_eq
    fieldFixesIdentitySeries tauFiniteLevi intertwines

end ModularRep.PaperProofs.EvenFieldGenericLeviSeries


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
