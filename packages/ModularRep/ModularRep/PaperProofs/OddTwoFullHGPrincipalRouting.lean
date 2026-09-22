import ModularRep.PaperProofs.EvenFieldFLZFullHG
import ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Semisimple

/-!
# Principal-block routing on the full odd-field relative class

The output concerns every pair of the existing `FullHG` and the same literal
selected block in its `Definition35Family`.  Its alternatives are an actual
special linear/unitary matrix presentation or an
`OddSymplecticPrincipalCarrier`.  The rank-one alternative is type A.

E1/E2 inputs retain the standard finite-classical-group identifications,
the dual Frobenius and connected-centralizer/Levi interpretation, the
selected strictly quasi-isolated semisimple two-regular label, and its
generalised Brauer-series membership.  The finite centralizer and linear
semisimplicity are literal.  Bonnafe's square implication is guarded by
semisimplicity on an actual odd-characteristic special orthogonal group.
The identity-series source compares actual Brauer blocks with the block of
a constant-one character; it has no strict-block hypothesis.

K derives label equality, identity-series membership, and a constant-one
character in the selected block before packaging the principal carrier.
There is no freely chosen unipotent predicate, `strict -> principal` input,
iBAW input, or all-strict-block iBAW conclusion in this file.

Source locators: FLZ 2022, pp. 30--31, Assumption 5.3, Remark 5.4 and
Hypothesis 5.5; pp. 33--34, Theorem 5.7 and Remark 5.8 (the latter is scoped
to simple PSp over an odd field and Sp).  Bonnafe, Proposition 4.11(a),
Section 4.E, pp. 2330--2331, supplies the semisimple square implication.
The root/finite group classifications use SF-C-SUBDIAGRAMS,
SF-RANK-ONE-ROOT, SF-C-ODD-FORMS and SF-FIXED-CLASSICAL.  FLZ 2023,
Theorem 5.2 and proof of Theorem 1, will handle the actual type-A branch;
the old even-field adapter requiring `ell != 2` is not used.

The source interpretation/completeness of `FullHG` and of its strict
predicate remains explicit E1/U.  No universal-cover hypothesis is imposed
on each member of the relative class.  The principal orbit/relation join
and its transport are still needed before Hypothesis 5.5(b) can be built.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport

universe u

/-- A group-only presentation of the split type-A branch. -/
structure LinearCoordinates (pDef rank : ℕ) (H : Type u) [Group H] where
  F : Type u
  [fieldF : Field F]
  [fintypeF : Fintype F]
  [charF : CharP F pDef]
  fieldOdd : Odd (Fintype.card F)
  groupEquiv : H ≃* Matrix.SpecialLinearGroup (Fin (rank + 1)) F

attribute [instance] LinearCoordinates.fieldF LinearCoordinates.fintypeF
  LinearCoordinates.charF

/-- A genuine finite unitary presentation.  In particular, the star is
the q-power involution on a field of size q squared; an arbitrary star
ring cannot be substituted for the source unitary group. -/
structure UnitaryCoordinates (pDef rank : ℕ) (H : Type u) [Group H] where
  E : Type u
  [fieldE : Field E]
  [fintypeE : Fintype E]
  [charE : CharP E pDef]
  [starE : StarRing E]
  exponent : ℕ
  exponentPositive : 0 < exponent
  fieldSize : Fintype.card E = pDef ^ (2 * exponent)
  fieldOdd : Odd (Fintype.card E)
  star_eq_frobenius : ∀ x : E, star x = x ^ (pDef ^ exponent)
  groupEquiv : H ≃* Matrix.specialUnitaryGroup (Fin (rank + 1)) E

attribute [instance] UnitaryCoordinates.fieldE UnitaryCoordinates.fintypeE
  UnitaryCoordinates.charE UnitaryCoordinates.starE

/-- The two actual matrix families in the cited type-A result.  This
contains no theorem about their blocks or their covers. -/
inductive TypeAActualPresentation (pDef rank : ℕ) (H : Type u) [Group H] : Type (u + 1) where
  | linear (coordinates : LinearCoordinates pDef rank H)
  | unitary (coordinates : UnitaryCoordinates pDef rank H)

/-- Finite odd-field coordinates for the group of one relative pair.
The field may vary with the pair, while its characteristic is fixed. -/
structure SymplecticCoordinates (pDef rank : ℕ) (H : Type u) [Group H] where
  F : Type u
  [fieldF : Field F]
  [fintypeF : Fintype F]
  [charF : CharP F pDef]
  fieldOdd : Odd (Fintype.card F)
  groupEquiv : H ≃* Matrix.symplecticGroup (Fin rank) F

attribute [instance] SymplecticCoordinates.fieldF
  SymplecticCoordinates.fintypeF SymplecticCoordinates.charF

/-- The dual is literally SO in dimension 2r+1 over an algebraically
closed field in the same defining characteristic.  The chosen coordinates
identify its Frobenius with entrywise q-power, q the selected finite field
size.  This is standard dual-group/coordinate source data, not a new
algebraic-group foundation. -/
structure OddSODualModel (pDef rank : ℕ) (F : Type u) [Field F] [Fintype F] where
  Closure : Type u
  [fieldClosure : Field Closure]
  [algClosedClosure : IsAlgClosed Closure]
  [charClosure : CharP Closure pDef]
  twoNeZero : (2 : Closure) ≠ 0
  fieldEmbedding : F →+* Closure
  frobenius : Matrix.specialOrthogonalGroup (Fin (2 * rank + 1)) Closure →*
    Matrix.specialOrthogonalGroup (Fin (2 * rank + 1)) Closure
  frobenius_matrix : ∀ s i j,
    ((frobenius s : Matrix.specialOrthogonalGroup
      (Fin (2 * rank + 1)) Closure) :
        Matrix (Fin (2 * rank + 1)) (Fin (2 * rank + 1)) Closure) i j =
      (s : Matrix (Fin (2 * rank + 1)) (Fin (2 * rank + 1)) Closure) i j ^
        Fintype.card F

attribute [instance] OddSODualModel.fieldClosure
  OddSODualModel.algClosedClosure OddSODualModel.charClosure

namespace OddSODualModel

variable {pDef rank : ℕ} {F : Type u} [Field F] [Fintype F]

abbrev SO (D : OddSODualModel pDef rank F) :=
  Matrix.specialOrthogonalGroup (Fin (2 * rank + 1)) D.Closure

/-- Semisimplicity of the actual matrix on its natural module. -/
def IsSemisimple (D : OddSODualModel pDef rank F) (s : D.SO) : Prop :=
  Module.End.IsSemisimple (Matrix.toLin'
    (s : Matrix (Fin (2 * rank + 1)) (Fin (2 * rank + 1)) D.Closure))

/-- The centralizer in the literal Frobenius fixed-point subgroup, viewed
inside the same algebraic dual-group carrier as the connected centralizer. -/
def finiteCentralizer (D : OddSODualModel pDef rank F) (s : D.SO) :
    Subgroup D.SO :=
  D.frobenius.eqLocus (MonoidHom.id _) ⊓ Subgroup.centralizer {s}

theorem finiteCentralizer_le (D : OddSODualModel pDef rank F) (s : D.SO) :
    D.finiteCentralizer s ≤ Subgroup.centralizer {s} := inf_le_right

end OddSODualModel

/-- Fixed source geometry and E_2-series on the actual family.  The series
relation is the modular E_2(H, s) relation on irreducible Brauer characters,
not a freely named unipotent predicate.  Its interpretation, the connected
centralizers and proper Levis remain the precise substantial E1/E2 source
inputs.  Defining this record does not authenticate those interpretations. -/
structure SymplecticJordanGeometry (pDef rank : ℕ)
    (family : Definition35Family.{u} 2)
    (coordinates : SymplecticCoordinates pDef rank family.H) where
  dual : OddSODualModel pDef rank coordinates.F
  connectedCentralizer : dual.SO → Subgroup dual.SO
  connectedCentralizer_le : ∀ s,
    connectedCentralizer s ≤ Subgroup.centralizer {s}
  IsProperLevi : Set dual.SO → Prop
  generalizedBrauerSeries : dual.SO → Set (IBr family.iota)
  bonnafe_square : ∀ s : dual.SO,
    dual.IsSemisimple s →
      NotContainedInProperLevi
        (Subgroup.centralizer {s} : Set dual.SO) IsProperLevi → s ^ 2 = 1

/-- The selected label and selected actual Brauer character of one strict
block.  All centralizers and the Levi predicate come from the same fixed
geometry.  Semisimplicity is required only of this selected label. -/
structure SelectedStrictBlockLabel {pDef rank : ℕ}
    {family : Definition35Family.{u} 2}
    {coordinates : SymplecticCoordinates pDef rank family.H}
    (geometry : SymplecticJordanGeometry pDef rank family coordinates)
    (block : family.Block) where
  label : geometry.dual.SO
  label_fixed : geometry.dual.frobenius label = label
  semisimple : geometry.dual.IsSemisimple label
  twoRegular : IsPrimeRegular 2 label
  strict : NotContainedInProperLevi
    ((geometry.dual.finiteCentralizer label : Set geometry.dual.SO) *
      (geometry.connectedCentralizer label : Set geometry.dual.SO))
    geometry.IsProperLevi
  character : Definition35Brauer (family.problem block)
  series_member : character.1 ∈ geometry.generalizedBrauerSeries label

namespace SelectedStrictBlockLabel

variable {pDef rank : ℕ} {family : Definition35Family.{u} 2}
variable {coordinates : SymplecticCoordinates pDef rank family.H}
variable {geometry : SymplecticJordanGeometry pDef rank family coordinates}
variable {block : family.Block} (L : SelectedStrictBlockLabel geometry block)

/-- The existing guarded kernel argument, now on the literal selected dual
matrix and the same finite/connected centralizers. -/
theorem label_eq_one : L.label = 1 :=
  semisimple_strictlyQuasiIsolated_label_eq_one
    geometry.dual.IsSemisimple geometry.IsProperLevi
    (geometry.dual.finiteCentralizer L.label)
    (geometry.connectedCentralizer L.label)
    (geometry.dual.finiteCentralizer_le L.label)
    (geometry.connectedCentralizer_le L.label)
    L.semisimple L.twoRegular L.strict geometry.bonnafe_square

theorem character_mem_identity_series :
    L.character.1 ∈ geometry.generalizedBrauerSeries 1 := by
  simpa only [L.label_eq_one] using L.series_member

end SelectedStrictBlockLabel

/-- The narrow unique-unipotent-block source used after the label is one.
It compares the actual block of every member of the identity E_2 series
with the actual block of a constant-one Brauer character.  No selected
strict block, principal-carrier output, or character correspondence is an
input.  FLZ Remark 5.8 licenses this only for the actual odd Sp setting. -/
structure IdentitySeriesBlockSource {pDef rank : ℕ}
    {family : Definition35Family.{u} 2}
    {coordinates : SymplecticCoordinates pDef rank family.H}
    (geometry : SymplecticJordanGeometry pDef rank family coordinates) where
  symplecticCentralQuotientSimple : IsSimpleGroup
    (Matrix.symplecticGroup (Fin rank) coordinates.F ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin rank) coordinates.F))
  trivialCharacter : IBr family.iota
  trivial_value : ∀ x, trivialCharacter.1 x = 1
  identity_series_block : 2 ≤ rank → ∀ psi : IBr family.iota,
    psi ∈ geometry.generalizedBrauerSeries 1 →
      irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks psi =
      irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks trivialCharacter

/-- Source data for one actual symplectic family.  Labels are supplied
only for the existing source-strict blocks; no field gives their principal
membership or an iBAW conclusion. -/
structure SymplecticJordanData (pDef rank : ℕ)
    (family : Definition35Family.{u} 2) (isStrict : family.Block → Prop) where
  coordinates : SymplecticCoordinates pDef rank family.H
  geometry : SymplecticJordanGeometry pDef rank family coordinates
  identitySource : IdentitySeriesBlockSource geometry
  selectedLabel : ∀ block : family.Block,
    isStrict block → SelectedStrictBlockLabel geometry block

namespace SymplecticJordanData

variable {pDef rank : ℕ} {family : Definition35Family.{u} 2}
variable {isStrict : family.Block → Prop}
variable (D : SymplecticJordanData pDef rank family isStrict)

/-- The constant-one character belongs to the SAME selected block.  This
is derived through its selected label and identity-series membership. -/
theorem trivialCharacter_block (rankAtLeastTwo : 2 ≤ rank)
    (block : family.Block) (hstrict : isStrict block) :
    irreducibleBrauerCharacterBlock family.iota
      family.irreducibleBrauerInjective family.blocks
      D.identitySource.trivialCharacter = block := by
  let L := D.selectedLabel block hstrict
  exact (D.identitySource.identity_series_block rankAtLeastTwo L.character.1
    L.character_mem_identity_series).symm.trans L.character.2

/-- A literal principal carrier, after the guarded label calculation. -/
def principalCarrier (rankAtLeastTwo : 2 ≤ rank)
    (block : family.Block) (hstrict : isStrict block) :
    OddSymplecticPrincipalCarrier (family.problem block) rank D.coordinates.F where
  rankAtLeastTwo := rankAtLeastTwo
  fieldOdd := D.coordinates.fieldOdd
  coefficientTwo := rfl
  symplecticEquiv := D.coordinates.groupEquiv
  principalCharacter :=
    ⟨D.identitySource.trivialCharacter,
      D.trivialCharacter_block rankAtLeastTwo block hstrict⟩
  principalCharacter_value_one := D.identitySource.trivial_value

end SymplecticJordanData

/-- The standard connected-subdiagram and finite-classical classification
for one actual family.  Type A is witnessed by actual SL/SU coordinates;
type C contains the source geometry above.  The rank-one field has a
group-only conclusion and cannot supply a block theorem. -/
structure RelativePairSource (pDef : ℕ) (family : Definition35Family.{u} 2)
    (isStrict : family.Block → Prop) where
  rank : ℕ
  rankPositive : 0 < rank
  rankOneTypeA : rank = 1 →
    Nonempty (TypeAActualPresentation pDef rank family.H)
  typeAlternative : Nonempty (TypeAActualPresentation pDef rank family.H) ∨
    Nonempty (SymplecticJordanData pDef rank family isStrict)

/-- Total source data over the existing nonselective relative class.
No new pair carrier, membership filter, set of blocks or strict predicate
is introduced here. -/
structure FullHGPrincipalRoutingSource {pDef : ℕ}
    {scope : FLZFullHGUniverse pDef 2}
    (coverage : FullHGDefinition35Coverage scope)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage) where
  pairSource : ∀ pair : FullHG scope,
    RelativePairSource pDef (coverage.presentation pair).family
      (strictSource.predicate pair)

namespace FullHGPrincipalRoutingSource

variable {pDef : ℕ} {scope : FLZFullHGUniverse pDef 2}
variable {coverage : FullHGDefinition35Coverage scope}
variable {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
variable (S : FullHGPrincipalRoutingSource coverage strictSource)

/-- Every selected source-strict block has an actual type-A group
presentation or is the principal block on an actual odd Sp carrier of rank
at least two.  This is a routing theorem, not Hypothesis 5.5(b). -/
theorem strictBlock_typeA_or_principal (pair : FullHG scope)
    (block : (coverage.presentation pair).family.Block)
    (hstrict : strictSource.predicate pair block) :
    Nonempty (TypeAActualPresentation pDef (S.pairSource pair).rank
      (coverage.presentation pair).family.H) ∨
    ∃ coordinates : SymplecticCoordinates pDef (S.pairSource pair).rank
        (coverage.presentation pair).family.H,
      Nonempty (OddSymplecticPrincipalCarrier
        ((coverage.presentation pair).family.problem block)
        (S.pairSource pair).rank coordinates.F) := by
  rcases typeA_or_typeC_rankAtLeastTwo
      (S.pairSource pair).rankPositive (S.pairSource pair).rankOneTypeA
      (S.pairSource pair).typeAlternative with hA | ⟨⟨D⟩, hrank⟩
  · exact Or.inl hA
  · exact Or.inr ⟨D.coordinates, ⟨D.principalCarrier hrank block hstrict⟩⟩

end FullHGPrincipalRoutingSource

end ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
