import ModularRep.PaperProofs.TypeBSpinOrdinaryRestriction
import ModularRep.PaperProofs.TypeBConformalRationalProjection
import ModularRep.PaperProofs.TypeBFLZJordanSourceBinding

/-!
# Spin rational series from the same special Clifford Jordan assignment

Every member is an actual ordinary restriction constituent along the norm
kernel inclusion. The semisimple class is its actual CSp-to-PCSp image.
The family is also identified with the prescribed Jordan values, using the
same cyclotomic embedding. There is no independent Spin family input.

Geck--Malle Proposition 2.6.16, pp.174--175, and Theorem 2.6.2,
pp.167--168, give the narrow common-constituent separation certificate.
The exact restriction formula and rational partition construct that
certificate below. Its published interpretation still requires the SAME
special Clifford Jordan assignment to be authenticated. No block matching,
basic set, BAW or manuscript conclusion is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinJordanRestrictionSource

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBConformalDualCarriers TypeBFLZLabelSource
open TypeBFLZOccurringCharacterSource TypeBFLZOccurringPairOrbits
open TypeBFLZJordanSourceBinding TypeBFLZCyclotomicModel
open TypeBSpinOrdinaryRestriction TypeBConformalRationalProjection
open TypeBSpinBroueMichelCarriers TypeBSpinRationalIndexAction TypeBRationalSeriesSource

variable {n p ell f : ℕ} {F K : Type}
  [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
  [Field K] [CharZero K]
  {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
  {primary : TypeBFLZPrimarySource.PrimarySource parameters scope}
  {source : OccurringCharacterSource (K := K) parameters scope primary}
  {choice : Choice (F := F) (n := n) K}
  {values : JordanValues source}
  (N : NormSource n F) (J : JordanCertificate source choice values)

/-- Spin uses sufficient roots derived from the same common primitive root. -/
def spinRoots (choice : Choice (F := F) (n := n) K) :
    HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) := by
  letI := choice.ordinaryRoots
  exact HasEnoughRootsOfUnity.of_dvd K
    (Subgroup.card_subgroup_dvd_card (SpinSubgroup n F N))

/-- The full rational family is defined by literal restriction occurrence. -/
def rationalSeries (i : FullRationalIndex p n F) : Set (Irr K (Spin n F N)) :=
  {chi | ∃ s : SemisimpleParameter F p n, rationalProjection s = i ∧
    ∃ Phi : Irr K (SpecialClifford n F), J.rationalSeries s Phi ∧ occurs N Phi chi}

@[simp] theorem rationalSeries_mem (i : FullRationalIndex p n F)
    (chi : Irr K (Spin n F N)) :
    chi ∈ rationalSeries N J i ↔
      ∃ s : SemisimpleParameter F p n, rationalProjection s = i ∧
        ∃ Phi : Irr K (SpecialClifford n F), J.rationalSeries s Phi ∧ occurs N Phi chi :=
  Iff.rfl

/-- Exact E2 overlap consequence on the same finite defining field, ordinary
splitting convention, upper rational series and actual restriction scalars.
The roots are explicit constructor guards; no independent Spin index
assignment or Spin rational predicate is supplied. -/
structure SeparationCertificate
    [finiteDefiningField : Finite F] [definingCharacteristic : CharP F p]
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
    [subgroupRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] : Prop where
  overlap : ∀ (s t : SemisimpleParameter F p n)
    (Phi Psi : Irr K (SpecialClifford n F)) (chi : Irr K (Spin n F N)),
    J.rationalSeries s Phi → J.rationalSeries t Psi →
    occurs N Phi chi → occurs N Psi chi →
    IsConj (projection F n s.val) (projection F n t.val)

section Splitting

variable [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

/-- The literal GM restriction formula plus the literal rational partition
derive the overlap certificate. This auxiliary source reconstruction does
not put the published lower predicate into the consumer's input interface. -/
def separation_of_geckMalle
    (published : FullRationalIndex p n F → Set (Irr K (Spin n F N)))
    (partition : ∀ {i j : FullRationalIndex p n F} {chi : Irr K (Spin n F N)},
      chi ∈ published i → chi ∈ published j → i = j)
    (restriction : ∀ (s : SemisimpleParameter F p n) (chi : Irr K (Spin n F N)),
      chi ∈ published (rationalProjection s) ↔
        ∃ Phi : Irr K (SpecialClifford n F), J.rationalSeries s Phi ∧ occurs N Phi chi) :
    SeparationCertificate N J where
  overlap s t Phi Psi chi hs ht hPhi hPsi :=
    (rationalProjection_eq_iff s t).mp
      (partition ((restriction s chi).mpr ⟨Phi, hs, hPhi⟩)
        ((restriction t chi).mpr ⟨Psi, ht, hPsi⟩))

variable (separation : SeparationCertificate N J)

include separation in
/-- Disjointness is proved for the constructed family from actual
common-constituent separation. -/
theorem rationalSeries_disjoint {i j : FullRationalIndex p n F}
    {chi : Irr K (Spin n F N)}
    (hi : chi ∈ rationalSeries N J i) (hj : chi ∈ rationalSeries N J j) : i = j := by
  obtain ⟨s, hs, Phi, hPhi, hsChi⟩ := hi
  obtain ⟨t, ht, Psi, hPsi, htChi⟩ := hj
  rw [← hs, ← ht]
  exact (rationalProjection_eq_iff s t).mpr
    (separation.overlap s t Phi Psi chi hPhi hPsi hsChi htChi)

def fullFamily : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F) where
  rationalSeries := rationalSeries N J
  disjoint := rationalSeries_disjoint N J separation

@[simp] theorem fullFamily_mem (i : FullRationalIndex p n F)
    (chi : Irr K (Spin n F N)) :
    chi ∈ (fullFamily N J separation).rationalSeries i ↔ chi ∈ rationalSeries N J i :=
  Iff.rfl

end Splitting

local instance occurringAction : MulAction (CSp F n) (OccurringPair F p n) := pairAction

/-- The upper family covers all upper ordinary characters by the already
prescribed Jordan classification, with no extra coverage source. -/
theorem upper_series_cover (Phi : Irr K (SpecialClifford n F)) :
    ∃ s : SemisimpleParameter F p n, J.rationalSeries s Phi := by
  obtain ⟨q, rfl⟩ := J.classification.surjective Phi
  induction q using Quotient.inductionOn with
  | h P => exact ⟨P.1, (J.rational_membership P.1 P).mpr (IsConj.refl _)⟩

/-- Eliminate the upper rational predicate in favor of the same actual
occurring-pair assignment and the actual projected class. -/
theorem rationalSeries_iff_pair (i : FullRationalIndex p n F)
    (chi : Irr K (Spin n F N)) :
    chi ∈ rationalSeries N J i ↔
      ∃ P : OccurringPair F p n, rationalProjection P.1 = i ∧
        occurs N (J.classification (Quotient.mk _ P)) chi := by
  constructor
  · rintro ⟨s, hs, Phi, hPhi, hChi⟩
    obtain ⟨q, hq⟩ := J.classification.surjective Phi
    obtain ⟨P, hP⟩ := Quotient.exists_rep q
    have hAssign : J.classification (Quotient.mk _ P) = Phi := by rw [hP, hq]
    have hConj := (J.rational_membership s P).mp (hAssign.symm ▸ hPhi)
    exact ⟨P, (rationalProjection_eq_of_isConj s P.1 hConj).symm.trans hs,
      hAssign.symm ▸ hChi⟩
  · rintro ⟨P, hP, hChi⟩
    exact ⟨P.1, hP, _, (J.rational_membership P.1 P).mpr (IsConj.refl _), hChi⟩

/-- Restrict the prescribed Jordan values using the SAME cyclotomic map. -/
def restrictedJordanValues (P : OccurringPair F p n) : Spin n F N → K :=
  fun x => choice.embedding (values P.1 (publishedLabel source P.1 P.2) x.val)

theorem restrictionClassFunction_jordan (P : OccurringPair F p n) :
    restrictionClassFunction N (J.classification (Quotient.mk _ P)) =
      restrictedJordanValues (choice := choice) (values := values) N P := by
  funext x
  exact (choice.value_eq_iff _ _).mp (J.value P x.val)

/-- The constructed Spin family is literally tested against those same
Jordan values, not against an independent Spin value assignment. -/
theorem rationalSeries_iff_jordan_values (i : FullRationalIndex p n F)
    (chi : Irr K (Spin n F N)) :
    chi ∈ rationalSeries N J i ↔
      ∃ P : OccurringPair F p n, rationalProjection P.1 = i ∧
        TypeBSpinPrincipalProjectiveBinding.scalarProductRight chi.val
          (restrictedJordanValues (choice := choice) (values := values) N P) ≠ 0 := by
  rw [rationalSeries_iff_pair]
  apply exists_congr
  intro P
  rw [occurs, restrictionClassFunction_jordan N J]

/-- Routine ordinary restriction-above, applied to the actual scalar
product. The finite splitting hypothesis is visible; no semisimple index
or source-series membership is requested of this E1 input. -/
structure RestrictionAboveCertificate
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
    [subgroupRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] : Prop where
  above : ∀ chi : Irr K (Spin n F N), ∃ Phi : Irr K (SpecialClifford n F), occurs N Phi chi

theorem rationalSeries_cover
    [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
    [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
    (above : RestrictionAboveCertificate (K := K) N) (chi : Irr K (Spin n F N)) :
    ∃ i : FullRationalIndex p n F, chi ∈ rationalSeries N J i := by
  obtain ⟨Phi, hPhi⟩ := above.above chi
  obtain ⟨s, hs⟩ := upper_series_cover J Phi
  exact ⟨rationalProjection s, s, rfl, Phi, hs, hPhi⟩

/-- Diagonal stability is a deduction: the SAME upper character and
semisimple witness work after inner conjugation of its restriction. -/
theorem rationalSeries_diagonal (g : SpecialClifford n F)
    (i : FullRationalIndex p n F) (chi : Irr K (Spin n F N))
    (hchi : chi ∈ rationalSeries N J i) :
    twist K (Spin n F N) chi (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)
      ∈ rationalSeries N J i := by
  obtain ⟨s, hs, Phi, hPhi, hChi⟩ := hchi
  exact ⟨s, hs, Phi, hPhi, (occurs_diagonal N Phi chi g).mpr hChi⟩

/-- Only the upper SC family requires published field naturality. The
lower field action and its positive projective dual index are derived. -/
theorem rationalSeries_field (fs : FieldActionSource n F p f parameters N)
    (natural : ∀ (e : FieldGroup f) (s : SemisimpleParameter F p n)
      (Phi : Irr K (SpecialClifford n F)), J.rationalSeries s Phi →
        J.rationalSeries (semisimpleField parameters e s)
          (twist K (SpecialClifford n F) Phi (fs.action e⁻¹)))
    (e : FieldGroup f) (i : FullRationalIndex p n F) (chi : Irr K (Spin n F N))
    (hchi : chi ∈ rationalSeries N J i) :
    twist K (Spin n F N) chi (spinFieldAction n F fs e⁻¹)
      ∈ rationalSeries N J
        (fullIndexMap (TypeBConformalDualFieldAction.pcspFieldAction F n parameters e) i) := by
  obtain ⟨s, hs, Phi, hPhi, hChi⟩ := hchi
  refine ⟨semisimpleField parameters e s, ?_, _, natural e s Phi hPhi, ?_⟩
  · rw [rationalProjection_field, hs]
  · exact (occurs_field N fs Phi chi e).mpr hChi

end ModularRep.PaperProofs.TypeBSpinJordanRestrictionSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
