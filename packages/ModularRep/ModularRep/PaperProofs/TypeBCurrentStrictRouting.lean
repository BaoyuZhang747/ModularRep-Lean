import ModularRep.PaperProofs.OddTwoTypeASourceJoin
import ModularRep.PaperProofs.TypeBConformalDualFieldAction
import ModularRep.OddQuasiIsolation

/-!
# Strict blocks in the complete relative type B class

The class of relative pairs is the existing nonselective `FullHG` carrier.
The structural input presents each of its finite groups as an actual special
linear or unitary group, Sp4, or a Spin group of rank at least three.

For the Spin branch, the dual is the actual projective conformal symplectic
group over an algebraically closed field. The source boundaries are the
algebraic interpretation of its proper Levis and connected centralisers,
Bonnafe's semisimple quasi-isolated order bound, and the unique unipotent
two-block theorem. The selected semisimple label, two-regularity and series
membership have their usual separate roles. Lean proves that the label is
one and that the constant-one Brauer character belongs to the selected block.
No strict-block iBAW conclusion is a field of this structural input.

The rank-two branch reuses the corrected type C principal construction.
The rank-one branch is included in type A. The source class, classifications,
algebraic interpretations and character-series dictionary remain E1/E2/U.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBCurrentStrictRouting

open ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.TypeBCliffordCarriers

/-- Group coordinates only. The field and norm have their literal definitions. -/
structure SpinCoordinates (p rank : ℕ) (H : Type) [Group H] where
  F : Type
  [fieldF : Field F]
  [fintypeF : Fintype F]
  [charF : CharP F p]
  exponent : ℕ
  parameters : OddFieldParameters F p exponent
  norm : NormSource rank F
  groupEquiv : H ≃* Spin rank F norm

attribute [instance] SpinCoordinates.fieldF SpinCoordinates.fintypeF
  SpinCoordinates.charF

/-- The actual central projection from Sp to the adjoint dual. -/
def symplecticDualProjection (A : Type) [Field A] (rank : ℕ) :
    (TypeBConformalDualCarriers.multiplier A rank).ker →*
      TypeBConformalDualCarriers.PCSp A rank :=
  (QuotientGroup.mk' (TypeBConformalDualCarriers.scalarSubgroup A rank)).comp
    (TypeBConformalDualCarriers.multiplier A rank).ker.subtype

/-- Principality is witnessed by the actual constant-one character in the
same selected block fibre, rather than an independent named predicate. -/
structure PrincipalSpinCarrier {p : ℕ} (family : Definition35Family 2)
    (block : family.Block) (rank : ℕ)
    (coordinates : SpinCoordinates p rank family.H) where
  rankAtLeastThree : 3 ≤ rank
  principalCharacter : Definition35Brauer (family.problem block)
  principalCharacter_value_one : ∀ x, principalCharacter.1.1 x = 1

/-- The algebraic dual and its rational Frobenius on fixed coordinates. -/
structure SpinDualGeometry {p rank : ℕ} (family : Definition35Family 2)
    (coordinates : SpinCoordinates p rank family.H) where
  Closure : Type
  [fieldClosure : Field Closure]
  [algClosedClosure : IsAlgClosed Closure]
  [charClosure : CharP Closure p]
  embedding : coordinates.F →+* Closure
  frobenius : Closure ≃+* Closure
  frobenius_value : ∀ a, frobenius a = a ^ (p ^ coordinates.exponent)
  connectedCentralizer : TypeBConformalDualCarriers.PCSp Closure rank →
    Subgroup (TypeBConformalDualCarriers.PCSp Closure rank)
  connected_le : ∀ s, connectedCentralizer s ≤ Subgroup.centralizer {s}
  IsProperLevi : Set (TypeBConformalDualCarriers.PCSp Closure rank) → Prop
  generalizedBrauerSeries : TypeBConformalDualCarriers.PCSp Closure rank →
    Set (IBr family.iota)
  rankAtLeastTwo : 2 ≤ rank
  /-- E1: semisimple elements lift through the central isogeny on the
  algebraically closed point group. Both groups and the map are fixed. -/
  semisimple_lift : ∀ s : TypeBConformalDualCarriers.PCSp Closure rank,
    IsPrimeRegular p s → ∃ t : (TypeBConformalDualCarriers.multiplier Closure rank).ker,
      symplecticDualProjection Closure rank t = s ∧ IsPrimeRegular p t
  /-- Bonnafe, Proposition 5.3(a): fourth powers of semisimple symplectic
  lifts with quasi-isolated image. The adjoint quotient is CSp/scalars on
  the same algebraically closed field, the standard PSp identification. -/
  bonnafe_fourth : 2 ≤ rank →
    ∀ t : (TypeBConformalDualCarriers.multiplier Closure rank).ker,
    IsPrimeRegular p t →
    NotContainedInProperLevi
      (Subgroup.centralizer {symplecticDualProjection Closure rank t} :
        Set (TypeBConformalDualCarriers.PCSp Closure rank))
      IsProperLevi →
    t ^ 4 = 1

attribute [instance] SpinDualGeometry.fieldClosure SpinDualGeometry.algClosedClosure
  SpinDualGeometry.charClosure

namespace SpinDualGeometry

variable {p rank : ℕ} {family : Definition35Family 2}
  {coordinates : SpinCoordinates p rank family.H}

abbrev Dual (D : SpinDualGeometry family coordinates) :=
  TypeBConformalDualCarriers.PCSp D.Closure rank

def dualFrobenius (D : SpinDualGeometry family coordinates) : MulAut D.Dual :=
  TypeBConformalDualFieldAction.pcspAutomorphism D.Closure rank D.frobenius

def finiteCentralizer (D : SpinDualGeometry family coordinates) (s : D.Dual) :
    Subgroup D.Dual :=
  Subgroup.centralizer {s} ⊓
    D.dualFrobenius.toMonoidHom.eqLocus (MonoidHom.id _)

theorem finiteCentralizer_le (D : SpinDualGeometry family coordinates) (s : D.Dual) :
    D.finiteCentralizer s ≤ Subgroup.centralizer {s} := inf_le_left

end SpinDualGeometry

/-- A source-strict block's semisimple label and one character in its series.
It contains neither a principal-block statement nor an iBAW witness. -/
structure SelectedSpinLabel {p rank : ℕ} {family : Definition35Family 2}
    {coordinates : SpinCoordinates p rank family.H}
    (geometry : SpinDualGeometry family coordinates) (block : family.Block) where
  label : geometry.Dual
  label_fixed : geometry.dualFrobenius label = label
  semisimple : IsPrimeRegular p label
  twoRegular : IsPrimeRegular 2 label
  strict : NotContainedInProperLevi
    ((geometry.finiteCentralizer label : Set geometry.Dual) *
      (geometry.connectedCentralizer label : Set geometry.Dual)) geometry.IsProperLevi
  character : Definition35Brauer (family.problem block)
  series_member : character.1 ∈ geometry.generalizedBrauerSeries label

namespace SelectedSpinLabel

variable {p rank : ℕ} {family : Definition35Family 2}
  {coordinates : SpinCoordinates p rank family.H}
  {geometry : SpinDualGeometry family coordinates} {block : family.Block}

/-- Strictness implies quasi-isolation; the odd-order/fourth-power argument
then determines the selected actual dual element. -/
theorem label_eq_one (L : SelectedSpinLabel geometry block) : L.label = 1 := by
  have quasi := quasiIsolated_of_strictlyQuasiIsolated
    (geometry.finiteCentralizer_le L.label) (geometry.connected_le L.label) L.strict
  obtain ⟨t, ht, hregular⟩ := geometry.semisimple_lift L.label L.semisimple
  have liftFourth := geometry.bonnafe_fourth geometry.rankAtLeastTwo t hregular
    (by simpa only [ht] using quasi)
  have fourth : L.label ^ 4 = 1 := by
    have mapped := congrArg (symplecticDualProjection geometry.Closure rank) liftFourth
    simpa only [map_pow, map_one, ht] using mapped
  have coprime : (orderOf L.label).Coprime 4 := by
    simpa only [show 4 = 2 ^ 2 by decide] using L.twoRegular.pow_right 2
  exact (show IsPrimeRegular 4 L.label from coprime).eq_one_of_pow_eq_one fourth

theorem character_mem_identity_series (L : SelectedSpinLabel geometry block) :
    L.character.1 ∈ geometry.generalizedBrauerSeries 1 := by
  simpa only [L.label_eq_one] using L.series_member

end SelectedSpinLabel

/-- E2 identity-series block theorem on the fixed Spin family, expressed for
every character of that series. Its conclusion is equality of actual block
labels with the block containing a constant-one character. Cabanes--Enguehard,
Theorems 21.14 and 9.12(i)--(ii), with the standard Brauer reduction and
primitive-block interpretation, provide this boundary. -/
structure SpinIdentitySeriesSource {p rank : ℕ} {family : Definition35Family 2}
    {coordinates : SpinCoordinates p rank family.H}
    (geometry : SpinDualGeometry family coordinates) where
  trivialCharacter : IBr family.iota
  trivial_value : ∀ x, trivialCharacter.1 x = 1
  identity_series_block : ∀ psi : IBr family.iota,
    psi ∈ geometry.generalizedBrauerSeries 1 →
      irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks psi =
      irreducibleBrauerCharacterBlock family.iota
        family.irreducibleBrauerInjective family.blocks trivialCharacter

structure SpinJordanData (p rank : ℕ) (family : Definition35Family 2)
    (isStrict : family.Block → Prop) where
  coordinates : SpinCoordinates p rank family.H
  geometry : SpinDualGeometry family coordinates
  identitySource : SpinIdentitySeriesSource geometry
  selectedLabel : ∀ block, isStrict block → SelectedSpinLabel geometry block

namespace SpinJordanData

variable {p rank : ℕ} {family : Definition35Family 2}
  {isStrict : family.Block → Prop} (D : SpinJordanData p rank family isStrict)

theorem trivialCharacter_block (block : family.Block) (hstrict : isStrict block) :
    irreducibleBrauerCharacterBlock family.iota family.irreducibleBrauerInjective
      family.blocks D.identitySource.trivialCharacter = block := by
  let L := D.selectedLabel block hstrict
  exact (D.identitySource.identity_series_block L.character.1
    L.character_mem_identity_series).symm.trans L.character.2

def principalCarrier (rankAtLeastThree : 3 ≤ rank)
    (block : family.Block) (hstrict : isStrict block) :
    PrincipalSpinCarrier family block rank D.coordinates where
  rankAtLeastThree := rankAtLeastThree
  principalCharacter :=
    ⟨D.identitySource.trivialCharacter, D.trivialCharacter_block block hstrict⟩
  principalCharacter_value_one := D.identitySource.trivial_value

end SpinJordanData

/-- Exhaustive standard connected-subdiagram classification. The rank-one
identification is inside the type A constructor. No pair or block is removed. -/
inductive RelativePairSource (p : ℕ) (family : Definition35Family 2)
    (isStrict : family.Block → Prop) : Type 1 where
  | typeA (rank : ℕ) (positive : 0 < rank)
      (presentation : TypeAActualPresentation p rank family.H)
  | rankTwo (data : SymplecticJordanData p 2 family isStrict)
  | spin (rank : ℕ) (rankAtLeastThree : 3 ≤ rank)
      (data : SpinJordanData p rank family isStrict)

structure FullHGRouting {p : ℕ} {scope : FLZFullHGUniverse p 2}
    (coverage : FullHGDefinition35Coverage scope)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage) where
  atPair : ∀ pair : FullHG scope,
    RelativePairSource p (coverage.presentation pair).family (strictSource.predicate pair)

end ModularRep.PaperProofs.TypeBCurrentStrictRouting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
