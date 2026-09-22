import ModularRep.PaperProofs.TypeBExceptionalCanonicalCover
import ModularRep.PaperProofs.TypeBFLZLabelSource

/-!
# Selection of the actual cover in Proposition 4.3

The parameter test selects the complete structural cover data before any
block, character, local reduction or family witness is introduced. The
generic branch is the accepted Spin cover. The exceptional branch is the
accepted free-presentation cover of the caller's same Omega N. The source
callbacks are guarded by the corresponding actual parameter proofs.

CoverData is a bundle of constructed output, not a new source premise.
The source assumptions are exactly those of the two accepted structural
providers. Selection is coefficient-free: a caller with Msys uses its
prime field, while retaining the same Msys in the later branch inputs.
The generic downstairsFamily and exceptional primitiveFamily need not
be identified, and no equality of those families is claimed here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBProposition44SelectedCover

open TypeBCliffordCarriers TypeBSpinCoverSource
open TypeBExceptionalCanonicalCover EvenFieldFLZSourceConditions

variable {n p f ell : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]

/-- The field degree is positive in the same finite-field parameters. -/
def fieldDegreeNeZero (parameters : OddFieldParameters F p f) : NeZero f :=
  ⟨Nat.ne_of_gt parameters.exponent_pos⟩

/-- The manuscript's nondivisibility guard gives the FLZ prime inequality. -/
theorem nondefining_prime (parameters : OddFieldParameters F p f)
    (nondefining : ¬ ell ∣ Nat.card F) : ell ≠ p := by
  intro heq
  apply nondefining
  rw [heq, parameters.cardinality]
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt parameters.exponent_pos)
  rw [hd, pow_succ]
  exact dvd_mul_left p (p ^ d)

/-- The full numerical applicability object is derived from manuscript guards. -/
def applicability (parameters : OddFieldParameters F p f)
    (prime : ell.Prime) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
    (rank : 3 ≤ n) : TypeBFLZLabelSource.Applicability p ell n where
  defining_prime := parameters.prime
  defining_odd := parameters.odd
  modular_prime := prime
  modular_odd := odd
  nondefining := nondefining_prime parameters nondefining
  rank := rank

/-- A structural output bundle whose simple quotient is the prescribed S. -/
structure CoverData (ell : ℕ) (S : Type) [Group S] where
  H : Type
  [groupH : Group H]
  [fintypeH : Fintype H]
  cover : EllPrimeCoverSource ell H
  simpleQuotient : cover.S ≃* S

attribute [instance] CoverData.groupH CoverData.fintypeH

variable (N : NormSource n F)

/-- The generic structural bundle, with the existing Spin enumeration. -/
def genericData [Finite (Spin n F N)]
    (source : GenericSpinCoverSource (p := p) (f := f) (ell := ell) N)
    (prime : ell.Prime) (odd : Odd ell) : CoverData ell (Omega N) := by
  letI : Fintype (Spin n F N) := Fintype.ofFinite _
  exact {
    H := Spin n F N
    groupH := inferInstance
    fintypeH := inferInstance
    cover := genericSpinEllPrimeCover N prime odd source
    simpleQuotient := MulEquiv.refl (Omega N) }

/-- The exceptional field-order test converts the same nondefining guard. -/
theorem nondefining_three (exceptional : (n, Nat.card F) = (3, 3))
    (nondefining : ¬ ell ∣ Nat.card F) : ell ≠ 3 := by
  have hq : Nat.card F = 3 := congrArg Prod.snd exceptional
  intro heq
  apply nondefining
  simpa only [hq, heq] using (dvd_refl 3)

/-- The exceptional bundle uses the accepted canonical group and projection. -/
def exceptionalData (parameters : OddFieldParameters F p f)
    (exceptional : (n, Nat.card F) = (3, 3))
    (source : ExceptionalOmegaSource N parameters exceptional)
    (freeSource : FreePresentationCoverSource)
    (prime : ell.Prime) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F) :
    CoverData ell (Omega N) := by
  letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional source
  exact {
    H := ExceptionalCover N
    groupH := inferInstance
    fintypeH := inferInstance
    cover := TypeBExceptionalCanonicalCover.ellPrimeCover N parameters exceptional
      source freeSource prime odd (nondefining_three exceptional nondefining)
    simpleQuotient := MulEquiv.refl (Omega N) }

section Select

variable [Finite (Spin n F N)]
variable (parameters : OddFieldParameters F p f)
variable (prime : ell.Prime) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
variable (genericSource : (n, Nat.card F) ≠ (3, 3) →
  GenericSpinCoverSource (p := p) (f := f) (ell := ell) N)
variable (exceptionalSource : ∀ h : (n, Nat.card F) = (3, 3),
  ExceptionalOmegaSource N parameters h)
variable (freeSource : FreePresentationCoverSource)

/-- Exhaustive selection of actual structural data, before block inputs. -/
def selectedData : CoverData ell (Omega N) := by
  classical
  exact if h : (n, Nat.card F) = (3, 3) then
    exceptionalData N parameters h (exceptionalSource h) freeSource prime odd nondefining
  else
    genericData N (genericSource h) prime odd

theorem selectedData_of_exceptional (h : (n, Nat.card F) = (3, 3)) :
    selectedData N parameters prime odd nondefining genericSource exceptionalSource freeSource =
      exceptionalData N parameters h (exceptionalSource h) freeSource prime odd nondefining := by
  classical
  simp only [selectedData, dif_pos h]

theorem selectedData_of_generic (h : (n, Nat.card F) ≠ (3, 3)) :
    selectedData N parameters prime odd nondefining genericSource exceptionalSource freeSource =
      genericData N (genericSource h) prime odd := by
  classical
  simp only [selectedData, dif_neg h]

theorem selectedGroup_of_exceptional (h : (n, Nat.card F) = (3, 3)) :
    (selectedData N parameters prime odd nondefining
      genericSource exceptionalSource freeSource).H = ExceptionalCover N := by
  rw [selectedData_of_exceptional N parameters prime odd nondefining
    genericSource exceptionalSource freeSource h]
  rfl

theorem selectedGroup_of_generic (h : (n, Nat.card F) ≠ (3, 3)) :
    (selectedData N parameters prime odd nondefining
      genericSource exceptionalSource freeSource).H = Spin n F N := by
  rw [selectedData_of_generic N parameters prime odd nondefining
    genericSource exceptionalSource freeSource h]
  rfl

/-- The simple quotient remains the actual Omega N in both branches. -/
def simpleQuotientEquiv :
    (selectedData N parameters prime odd nondefining
      genericSource exceptionalSource freeSource).cover.S ≃* Omega N :=
  (selectedData N parameters prime odd nondefining
    genericSource exceptionalSource freeSource).simpleQuotient

/-- The selected group's covering map, with the literal Omega codomain. -/
def selectedProjection :
    (selectedData N parameters prime odd nondefining
      genericSource exceptionalSource freeSource).H →* Omega N :=
  (simpleQuotientEquiv N parameters prime odd nondefining
    genericSource exceptionalSource freeSource).toMonoidHom.comp
      (selectedData N parameters prime odd nondefining
        genericSource exceptionalSource freeSource).cover.quotient

theorem selectedProjection_surjective : Function.Surjective
    (selectedProjection N parameters prime odd nondefining
      genericSource exceptionalSource freeSource) :=
  (simpleQuotientEquiv N parameters prime odd nondefining
    genericSource exceptionalSource freeSource).surjective.comp
      (selectedData N parameters prime odd nondefining
        genericSource exceptionalSource freeSource).cover.quotient_surjective

end Select

end ModularRep.PaperProofs.TypeBProposition44SelectedCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
