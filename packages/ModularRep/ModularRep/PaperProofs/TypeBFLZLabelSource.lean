import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.PaperProofs.TypeBConformalDualCarriers
import ModularRep.PaperProofs.TypeBBlockLabelConjugacy
import ModularRep.PaperProofs.TypeBRationalSeriesSource
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.PrimitiveBlockAutomorphism
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.OrderOfElement

/-!
# FLZ character and block labels on the fixed Type B carriers

The first coordinate of every label is an actual element of the fixed-form
CSp dual.  A character's second coordinate is an actual ordinary irreducible
character of its centralizer, restricted by the source unipotent predicate.
The unipotent predicate and the combinatorial core family remain explicit
source definitions (U); this file does not reconstruct Deligne--Lusztig
theory or the partitions and symbols in FLZ Section 3.4.

The source certificates are separated. Equation (3.4) and its following
paragraph (FLZ, J. Algebra 604 (2022), p. 545) classify ALL ordinary
characters by semisimple/unipotent-character labels. The rational-series
membership identity binds the same labels to the same rational series.
Lean restricts this classification to ell-prime parameters and proves raw
label surjectivity. Theorem 6.3(1), p. 567, classifies blocks by core-pair
orbits; part (2), at t=1, gives the core membership equation. The latter
certificate does not supply ordinary-character surjectivity.

No same-block conjugacy, scalar-square conclusion, blockwise Brauer
bijection, BAW-goodness, or iBAW predicate is an input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBFLZLabelSource

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers

universe u

variable (F K : Type u) [Field F] [Field K] [CharZero K]
variable (p ell n : ℕ)

/-- Literal rational semisimple parameters in the finite CSp dual. -/
abbrev SemisimpleParameter :=
  {s : CSp F n // p.Coprime (orderOf s)}

/-- The ell-prime semisimple parameters used in Theorem 6.3. -/
abbrev AdmissibleParameter :=
  {s : CSp F n // p.Coprime (orderOf s) ∧ ell.Coprime (orderOf s)}

/-- Rational-series indices are conjugacy classes of actual admissible
dual elements. Both order restrictions are retained in the carrier. -/
abbrev SourceIndex :=
  {s : ConjClasses (CSp F n) //
    ∃ g : CSp F n, ConjClasses.mk g = s ∧
      p.Coprime (orderOf g) ∧ ell.Coprime (orderOf g)}

/-- The rational conjugacy class index of a literal source parameter. -/
def parameterIndex (s : AdmissibleParameter F p ell n) : SourceIndex F p ell n :=
  ⟨ConjClasses.mk s.1, s.1, rfl, s.2⟩

theorem parameterIndex_eq_iff (s t : AdmissibleParameter F p ell n) :
    parameterIndex F p ell n s = parameterIndex F p ell n t ↔ IsConj s.1 t.1 := by
  constructor
  · intro h
    exact ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr h)

theorem parameterIndex_surjective :
    Function.Surjective (parameterIndex F p ell n) := by
  intro i
  obtain ⟨g, hg, hp, he⟩ := i.2
  exact ⟨⟨g, hp, he⟩, Subtype.ext hg⟩

/-- Forget the ell-prime restriction, retaining the very same dual element. -/
def admissibleToSemisimple (s : AdmissibleParameter F p ell n) :
    SemisimpleParameter F p n := ⟨s.1, s.2.1⟩

/-- The actual centralizer of a semisimple element in the fixed finite dual. -/
def parameterCentralizer (s : SemisimpleParameter F p n) : Subgroup (CSp F n) :=
  Subgroup.centralizer ({s.1} : Set (CSp F n))

/-- The unipotent predicate remains a named source definition on actual
ordinary centralizer characters, rather than an arbitrary label type. -/
abbrev UnipotentPredicate :=
  ∀ s : SemisimpleParameter F p n, Irr K (parameterCentralizer F p n s) → Prop

/-- Equation (3.4)'s full semisimple/unipotent-character pairs. -/
abbrev FullCharacterPair (unipotent : UnipotentPredicate F K p n) :=
  Σ s : SemisimpleParameter F p n,
    {chi : Irr K (parameterCentralizer F p n s) // unipotent s chi}

/-- The ell-prime restriction of those same pairs. -/
abbrev CharacterPair (unipotent : UnipotentPredicate F K p n) :=
  Σ s : AdmissibleParameter F p ell n,
    {chi : Irr K (parameterCentralizer F p n (admissibleToSemisimple F p ell n s)) //
      unipotent (admissibleToSemisimple F p ell n s) chi}

def characterPairToFull (unipotent : UnipotentPredicate F K p n)
    (l : CharacterPair F K p ell n unipotent) : FullCharacterPair F K p n unipotent :=
  ⟨admissibleToSemisimple F p ell n l.1, l.2⟩

/-- Core pairs retain their actual admissible first coordinate. The core
family is the externally defined FLZ `C(s)` and remains explicit. -/
abbrev BlockPair (Core : AdmissibleParameter F p ell n → Type u) :=
  Σ s : AdmissibleParameter F p ell n, Core s

/-- The hypotheses of the odd-prime source specialization. Algebraic-group
and finite-field realizations are identified at the application boundary. -/
structure Applicability : Prop where
  defining_prime : Nat.Prime p
  defining_odd : Odd p
  modular_prime : Nat.Prime ell
  modular_odd : Odd ell
  nondefining : ell ≠ p
  rank : 3 ≤ n

section Equation34

variable {F K p ell n}
variable [Finite F] [CharP F p] [IsAlgClosed K]
variable [Finite (Clifford n F)]
variable (unipotent : UnipotentPredicate F K p n)
variable [MulAction (CSp F n) (FullCharacterPair F K p n unipotent)]

/-- E2: FLZ equation (3.4) on the full ordinary carrier, with its
rational-series membership identity. This source has no modular target.
The orbit action must have literal first-coordinate conjugation. -/
structure Equation34Source where
  hypotheses : Applicability p ell n
  field_finite : Finite F
  field_characteristic : CharP F p
  ordinary_splitting : IsAlgClosed K
  clifford_finite : Finite (Clifford n F)
  rationalSeries : SemisimpleParameter F p n → Irr K (SpecialClifford n F) → Prop
  parameter_conjugation : ∀ (g : CSp F n) (l : FullCharacterPair F K p n unipotent),
    (g • l).1.1 = g * l.1.1 * g⁻¹
  classification :
    MulAction.orbitRel.Quotient (CSp F n) (FullCharacterPair F K p n unipotent) ≃
      Irr K (SpecialClifford n F)
  rational_membership : ∀ (s : SemisimpleParameter F p n)
      (l : FullCharacterPair F K p n unipotent),
    rationalSeries s (classification (Quotient.mk _ l)) ↔ IsConj s.1 l.1.1

namespace Equation34Source

variable {unipotent}
variable (S : Equation34Source (ell := ell) unipotent)

/-- The selected ordinary carrier is definitionally the union of the
source rational series indexed by admissible semisimple parameters. -/
def selectedSeries (chi : Irr K (SpecialClifford n F)) : Prop :=
  ∃ s : AdmissibleParameter F p ell n,
    S.rationalSeries (admissibleToSemisimple F p ell n s) chi

abbrev SelectedCharacter :=
  {chi : Irr K (SpecialClifford n F) // S.selectedSeries chi}

/-- The actual ordinary character assigned to a full equation-(3.4) label. -/
def fullCharacter (l : FullCharacterPair F K p n unipotent) :
    Irr K (SpecialClifford n F) := S.classification (Quotient.mk _ l)

theorem fullCharacter_surjective : Function.Surjective S.fullCharacter := by
  intro chi
  obtain ⟨l, hl⟩ := Quotient.mk_surjective (S.classification.symm chi)
  refine ⟨l, ?_⟩
  change S.classification (Quotient.mk _ l) = chi
  rw [hl, S.classification.apply_symm_apply]

/-- The ell-prime character map is the restriction of equation (3.4),
not an independently supplied correspondence. -/
def character (l : CharacterPair F K p ell n unipotent) : S.SelectedCharacter :=
  ⟨S.fullCharacter (characterPairToFull F K p ell n unipotent l),
    l.1, (S.rational_membership _ _).mpr (IsConj.refl _)⟩

@[simp]
theorem character_val (l : CharacterPair F K p ell n unipotent) :
    (S.character l).1 = S.fullCharacter (characterPairToFull F K p ell n unipotent l) := rfl

/-- Raw ell-prime label surjectivity is derived from the full quotient
classification and the literal rational-series membership equation. -/
theorem character_surjective : Function.Surjective S.character := by
  intro chi
  obtain ⟨l, hl⟩ := S.fullCharacter_surjective chi.1
  obtain ⟨s, hs⟩ := chi.2
  have hmem : S.rationalSeries (admissibleToSemisimple F p ell n s)
      (S.classification (Quotient.mk _ l)) := by
    change S.rationalSeries (admissibleToSemisimple F p ell n s) (S.fullCharacter l)
    rw [hl]
    exact hs
  have hc := (S.rational_membership (admissibleToSemisimple F p ell n s) l).mp hmem
  obtain ⟨g, hg⟩ := hc
  have ho : orderOf s.1 = orderOf l.1.1 := SemiconjBy.orderOf_eq (g : CSp F n) hg
  have he : ell.Coprime (orderOf l.1.1) := ho ▸ s.2.2
  let a : AdmissibleParameter F p ell n := ⟨l.1.1, l.1.2, he⟩
  let m : CharacterPair F K p ell n unipotent := ⟨a, l.2⟩
  refine ⟨m, Subtype.ext ?_⟩
  change S.fullCharacter (characterPairToFull F K p ell n unipotent m) = chi.1
  exact hl

/-- Membership of the constructed character in an individual rational
series records its actual semisimple first coordinate. -/
theorem character_rational_membership (s : SemisimpleParameter F p n)
    (l : CharacterPair F K p ell n unipotent) :
    S.rationalSeries s (S.character l).1 ↔ IsConj s.1 l.1.1 :=
  S.rational_membership s (characterPairToFull F K p ell n unipotent l)

/-- Two source rational series containing the same actual character have
conjugate parameters. This is deduced from equation (3.4), not added as
an independent compatibility input. -/
theorem parameters_isConj_of_rational_membership
    (s t : SemisimpleParameter F p n) (chi : Irr K (SpecialClifford n F))
    (hs : S.rationalSeries s chi) (ht : S.rationalSeries t chi) :
    IsConj s.1 t.1 := by
  obtain ⟨l, hl⟩ := S.fullCharacter_surjective chi
  rw [← hl] at hs ht
  exact ((S.rational_membership s l).mp hs).trans
    ((S.rational_membership t l).mp ht).symm

/-- The literal rational series indexed by rational conjugacy classes.
The membership predicate is the one in the equation-(3.4) certificate. -/
def rationalFamily (i : SourceIndex F p ell n) :
    Set (Irr K (SpecialClifford n F)) :=
  {chi | ∃ s : AdmissibleParameter F p ell n,
    parameterIndex F p ell n s = i ∧
      S.rationalSeries (admissibleToSemisimple F p ell n s) chi}

theorem rationalFamily_disjoint {i j : SourceIndex F p ell n}
    {chi : Irr K (SpecialClifford n F)}
    (hi : chi ∈ S.rationalFamily i) (hj : chi ∈ S.rationalFamily j) : i = j := by
  obtain ⟨s, hs, hsi⟩ := hi
  obtain ⟨t, ht, htj⟩ := hj
  rw [← hs, ← ht]
  apply (parameterIndex_eq_iff F p ell n s t).mpr
  exact S.parameters_isConj_of_rational_membership _ _ chi hsi htj

/-- The common family consumed by the individual FLZ-2.3 certificates and
the global basic-set aggregation, with disjointness proved above. -/
def rationalSeriesSource :
    TypeBRationalSeriesSource.RationalSeriesSource K (SpecialClifford n F)
      (SourceIndex F p ell n) where
  rationalSeries := S.rationalFamily
  disjoint := S.rationalFamily_disjoint

theorem rationalFamily_selected {i : SourceIndex F p ell n}
    {chi : Irr K (SpecialClifford n F)} (h : chi ∈ S.rationalFamily i) :
    S.selectedSeries chi := by
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, hs⟩

theorem rationalSeriesSource_selected_iff (chi : Irr K (SpecialClifford n F)) :
    S.rationalSeriesSource.selectedSeries chi ↔ S.selectedSeries chi := by
  constructor
  · rintro ⟨i, hi⟩
    exact S.rationalFamily_selected hi
  · rintro ⟨s, hs⟩
    exact ⟨parameterIndex F p ell n s, s, rfl, hs⟩

/-- The two presentations of the selected union preserve the actual
ordinary character exactly. -/
def selectedCharacterEquiv : S.SelectedCharacter ≃ S.rationalSeriesSource.Basic where
  toFun chi := ⟨chi.1, (S.rationalSeriesSource_selected_iff chi.1).mpr chi.2⟩
  invFun chi := ⟨chi.1, (S.rationalSeriesSource_selected_iff chi.1).mp chi.2⟩
  left_inv chi := by
    apply Subtype.ext
    rfl
  right_inv chi := by
    apply Subtype.ext
    rfl

@[simp]
theorem selectedCharacterEquiv_val (chi : S.SelectedCharacter) :
    (S.selectedCharacterEquiv chi).1 = chi.1 := rfl

@[simp]
theorem selectedCharacterEquiv_symm_val (chi : S.rationalSeriesSource.Basic) :
    (S.selectedCharacterEquiv.symm chi).1 = chi.1 := rfl

/-- Equation (3.4)'s character on the common rational-family carrier. -/
def familyCharacter (l : CharacterPair F K p ell n unipotent) :
    S.rationalSeriesSource.Basic := S.selectedCharacterEquiv (S.character l)

@[simp]
theorem familyCharacter_val (l : CharacterPair F K p ell n unipotent) :
    (S.familyCharacter l).1 = (S.character l).1 := rfl

theorem familyCharacter_surjective : Function.Surjective S.familyCharacter :=
  S.selectedCharacterEquiv.surjective.comp S.character_surjective

/-- The index on the existing selected carrier is determined by the
source rational series, so callers need no carrier transport. -/
def ordinaryIndex (chi : S.SelectedCharacter) : SourceIndex F p ell n :=
  parameterIndex F p ell n (Classical.choose chi.2)

theorem ordinaryIndex_mem (chi : S.SelectedCharacter) :
    chi.1 ∈ S.rationalFamily (S.ordinaryIndex chi) :=
  ⟨Classical.choose chi.2, rfl, Classical.choose_spec chi.2⟩

theorem ordinaryIndex_eq_iff (chi : S.SelectedCharacter) (i : SourceIndex F p ell n) :
    S.ordinaryIndex chi = i ↔ chi.1 ∈ S.rationalFamily i := by
  constructor
  · intro h
    simpa [h] using S.ordinaryIndex_mem chi
  · intro h
    exact S.rationalFamily_disjoint (S.ordinaryIndex_mem chi) h

@[simp]
theorem ordinaryIndex_selectedCharacterEquiv (chi : S.SelectedCharacter) :
    S.rationalSeriesSource.ordinaryIndex (S.selectedCharacterEquiv chi) =
      S.ordinaryIndex chi := by
  apply (S.rationalSeriesSource.ordinaryIndex_eq_iff _ _).mpr
  exact S.ordinaryIndex_mem chi

@[simp]
theorem ordinaryIndex_character (l : CharacterPair F K p ell n unipotent) :
    S.ordinaryIndex (S.character l) = parameterIndex F p ell n l.1 := by
  apply (S.ordinaryIndex_eq_iff _ _).mpr
  exact ⟨l.1, rfl, (S.character_rational_membership _ l).mpr (IsConj.refl _)⟩

@[simp]
theorem ordinaryIndex_familyCharacter (l : CharacterPair F K p ell n unipotent) :
    S.rationalSeriesSource.ordinaryIndex (S.familyCharacter l) =
      parameterIndex F p ell n l.1 := by
  exact (S.ordinaryIndex_selectedCharacterEquiv (S.character l)).trans
    (S.ordinaryIndex_character l)

/-- The index fibre is the very same rational-series membership subtype
on which the one-way integral basic-set certificate is stated. -/
def ordinaryFibreEquiv (i : SourceIndex F p ell n) :
    TypeBRationalSeriesBasicSet.SeriesFibre S.ordinaryIndex i ≃
      {chi : Irr K (SpecialClifford n F) // chi ∈ S.rationalFamily i} where
  toFun chi := ⟨chi.1.1, (S.ordinaryIndex_eq_iff chi.1 i).mp chi.2⟩
  invFun chi :=
    ⟨⟨chi.1, S.rationalFamily_selected chi.2⟩,
      (S.ordinaryIndex_eq_iff _ i).mpr chi.2⟩
  left_inv chi := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv chi := by
    apply Subtype.ext
    rfl

@[simp]
theorem ordinaryFibreEquiv_val (i : SourceIndex F p ell n)
    (chi : TypeBRationalSeriesBasicSet.SeriesFibre S.ordinaryIndex i) :
    (S.ordinaryFibreEquiv i chi).1 = chi.1.1 := rfl

end Equation34Source

end Equation34

section Theorem63

variable {F K p ell n}
variable [Finite F] [CharP F p] [IsAlgClosed K]
variable [Finite (Clifford n F)]
variable {k : Type u} [Field k] [CharP k ell] [IsAlgClosed k]
variable (unipotent : UnipotentPredicate F K p n)
variable [MulAction (CSp F n) (FullCharacterPair F K p n unipotent)]
variable (S : Equation34Source (ell := ell) unipotent)
variable (Core : AdmissibleParameter F p ell n → Type u)
variable [MulAction (CSp F n) (BlockPair F p ell n Core)]
variable (ordinaryBlock : Irr K (SpecialClifford n F) →
  LiteralPrimitiveBlock k (SpecialClifford n F))

/-- E2: Theorem 6.3(1) on literal primitive block idempotents and its
part-(2) core-membership clause at t=1. Core extraction is fibrewise over
the same semisimple parameter, so preservation of that parameter is
definitional. The combinatorial core family remains a named source datum.
-/
structure Theorem63Source where
  modular_characteristic : CharP k ell
  modular_splitting : IsAlgClosed k
  coreAt : ∀ s : AdmissibleParameter F p ell n,
    {chi : Irr K (parameterCentralizer F p n (admissibleToSemisimple F p ell n s)) //
      unipotent (admissibleToSemisimple F p ell n s) chi} → Core s
  parameter_conjugation : ∀ (g : CSp F n) (b : BlockPair F p ell n Core),
    (g • b).1.1 = g * b.1.1 * g⁻¹
  classification : MulAction.orbitRel.Quotient (CSp F n) (BlockPair F p ell n Core) ≃
    LiteralPrimitiveBlock k (SpecialClifford n F)
  membership : ∀ l : CharacterPair F K p ell n unipotent,
    ordinaryBlock (S.character l).1 =
      classification (Quotient.mk _ (⟨l.1, coreAt l.1 l.2⟩ : BlockPair F p ell n Core))

namespace Theorem63Source

variable {unipotent S Core ordinaryBlock}
variable (T : Theorem63Source unipotent S Core ordinaryBlock)

/-- First-coordinate index on core-pair orbits. Well-definedness uses
the literal conjugation equation of the source action. -/
def blockOrbitIndex :
    MulAction.orbitRel.Quotient (CSp F n) (BlockPair F p ell n Core) →
      SourceIndex F p ell n :=
  Quotient.lift (fun b => parameterIndex F p ell n b.1) (by
    intro b c h
    apply (parameterIndex_eq_iff F p ell n b.1 c.1).mpr
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
    have hp : b.1.1 = g * c.1.1 * g⁻¹ := by
      rw [← hg, T.parameter_conjugation]
    exact (isConj_iff.mpr ⟨g, hp.symm⟩).symm)

/-- A primitive block's series is forced by the inverse of the actual
Theorem-6.3 block classification, rather than supplied independently. -/
def blockSeries (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :
    SourceIndex F p ell n := T.blockOrbitIndex (T.classification.symm b)

@[simp]
theorem blockSeries_classification (b : BlockPair F p ell n Core) :
    T.blockSeries (T.classification (Quotient.mk _ b)) =
      parameterIndex F p ell n b.1 := by
  simp [blockSeries, blockOrbitIndex]

/-- The t=1 membership clause joins the ordinary rational-series index
to the block partition on literal primitive idempotents. -/
@[simp]
theorem blockSeries_character (l : CharacterPair F K p ell n unipotent) :
    T.blockSeries (ordinaryBlock (S.character l).1) =
      parameterIndex F p ell n l.1 := by
  rw [T.membership, T.blockSeries_classification]

theorem blockSeries_ordinaryBlock (chi : S.SelectedCharacter) :
    T.blockSeries (ordinaryBlock chi.1) = S.ordinaryIndex chi := by
  obtain ⟨l, rfl⟩ := S.character_surjective chi
  rw [T.blockSeries_character, S.ordinaryIndex_character]

@[simp]
theorem blockSeries_familyCharacter (l : CharacterPair F K p ell n unipotent) :
    T.blockSeries (ordinaryBlock (S.familyCharacter l).1) =
      parameterIndex F p ell n l.1 := T.blockSeries_character l

theorem blockSeries_familyOrdinaryBlock (chi : S.rationalSeriesSource.Basic) :
    T.blockSeries (ordinaryBlock chi.1) = S.rationalSeriesSource.ordinaryIndex chi := by
  obtain ⟨l, rfl⟩ := S.familyCharacter_surjective chi
  rw [T.blockSeries_familyCharacter, S.ordinaryIndex_familyCharacter]

end Theorem63Source

/-- Construct the reusable block-label interface from the distinct source
certificates. Character surjectivity is proved above from equation (3.4);
neither it nor same-block conjugacy is a Theorem-6.3 assumption. -/
def toBlockLabelSource (T : Theorem63Source unipotent S Core ordinaryBlock) :
    TypeBBlockLabelConjugacy.BlockLabelSource
      (Dual := CSp F n)
      (CharacterLabel := CharacterPair F K p ell n unipotent)
      (BlockLabel := BlockPair F p ell n Core)
      (fun chi : S.SelectedCharacter => ordinaryBlock chi.1) where
  character := S.character
  character_surjective := S.character_surjective
  characterParameter l := l.1.1
  core l := ⟨l.1, T.coreAt l.1 l.2⟩
  blockParameter b := b.1.1
  core_parameter _ := rfl
  parameter_conjugation := T.parameter_conjugation
  classification := T.classification
  membership := T.membership

/-- The same independently sourced label packet on the canonical family
carrier consumed by the FLZ-2.3 basic-set aggregation. -/
def toFamilyBlockLabelSource (T : Theorem63Source unipotent S Core ordinaryBlock) :
    TypeBBlockLabelConjugacy.BlockLabelSource
      (Dual := CSp F n)
      (CharacterLabel := CharacterPair F K p ell n unipotent)
      (BlockLabel := BlockPair F p ell n Core)
      (fun chi : S.rationalSeriesSource.Basic => ordinaryBlock chi.1) where
  character := S.familyCharacter
  character_surjective := S.familyCharacter_surjective
  characterParameter l := l.1.1
  core l := ⟨l.1, T.coreAt l.1 l.2⟩
  blockParameter b := b.1.1
  core_parameter _ := rfl
  parameter_conjugation := T.parameter_conjugation
  classification := T.classification
  membership := T.membership

end Theorem63

end ModularRep.PaperProofs.TypeBFLZLabelSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
