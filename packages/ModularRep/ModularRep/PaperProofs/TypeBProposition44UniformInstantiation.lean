import ModularRep.PaperProofs.TypeBProposition44SelectedCover
import ModularRep.PaperProofs.TypeBProposition44GenericInputs
import ModularRep.PaperProofs.TypeBProposition44ExceptionalInputs

/-!
# Proposition 4.3 on the actual cover selected by its numerical parameters

Only independent sources occur in the two branch packages. The generic
Clifford, field-action and ordinary-root data are needed only in that
branch; the exceptional specified data use its canonical sixfold cover.
One parameter test selects both the structural cover and the complete
normalized witness type. Its two branches retain the existing literal
family constructors and the caller's same modular system.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBProposition44UniformInstantiation

open ModularRep
open TypeBCliffordCarriers TypeBSpinCoverSource
open TypeBExceptionalCanonicalCover TypeBProposition44SelectedCover
open TypeBFullCriterionSplittingSource

variable {n p f ell : ℕ} {F k K O : Type}
  [Field F] [Finite F] [CharP F p]
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (parameters : OddFieldParameters F p f) (N : NormSource n F)
  (Msys : ModularSystem ell K O k)
  (rank : 3 ≤ n) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
  (divides : ell ∣ Nat.card (Omega N))

/-- Generic geometry and structural data precede the independent block inputs. -/
structure GenericBranch where
  [cliffordFinite : Finite (Clifford n F)]
  coverSource : GenericSpinCoverSource (p := p) (f := f) (ell := ell) N
  fs : FieldActionSource n F p f parameters N
  choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K
  inputs :
    letI : NeZero f := fieldDegreeNeZero parameters
    TypeBProposition44GenericInputs.Inputs parameters N fs Msys
      (applicability parameters Msys.prime odd nondefining rank) choice coverSource divides

/-- The exceptional structural source fixes the cover before its specified inputs. -/
structure ExceptionalBranch (exceptional : (n, Nat.card F) = (3, 3)) where
  omega : ExceptionalOmegaSource N parameters exceptional
  freeSource : FreePresentationCoverSource
  inputs : TypeBProposition44ExceptionalInputs.Inputs N parameters exceptional omega
    freeSource Msys odd nondefining divides

/-- Each raw source package is required only on its actual numerical branch. -/
structure Inputs where
  generic : (n, Nat.card F) ≠ (3, 3) →
    GenericBranch parameters N Msys rank odd nondefining divides
  exceptional : ∀ h : (n, Nat.card F) = (3, 3),
    ExceptionalBranch parameters N Msys odd nondefining divides h

variable (inputs : Inputs parameters N Msys rank odd nondefining divides)

/-- The selected cover is computed from structural fields only. -/
def selectedCoverData : CoverData ell (Omega N) := by
  classical
  exact if h : (n, Nat.card F) = (3, 3) then
    let e := inputs.exceptional h
    exceptionalData N parameters h e.omega e.freeSource Msys.prime odd nondefining
  else
    let g := inputs.generic h
    letI := g.cliffordFinite
    genericData N g.coverSource Msys.prime odd

/-- A complete witness type on the same selected actual cover and modular system. -/
def Witness : Type 1 := by
  classical
  exact if h : (n, Nat.card F) = (3, 3) then
    let e := inputs.exceptional h
    NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := TypeBProposition44ExceptionalInputs.family N parameters h e.omega
        e.freeSource Msys odd nondefining divides e.inputs)
      Msys (TypeBProposition44ExceptionalInputs.selectedCover N parameters h e.omega
        e.freeSource Msys odd nondefining)
  else
    let g := inputs.generic h
    letI := g.cliffordFinite
    letI : NeZero f := fieldDegreeNeZero parameters
    NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := TypeBProposition44GenericInputs.family parameters N g.fs Msys
        (applicability parameters Msys.prime odd nondefining rank) g.choice
        g.coverSource divides g.inputs)
      Msys (TypeBProposition44GenericInputs.cover parameters N g.fs Msys
        (applicability parameters Msys.prime odd nondefining rank) g.choice
        g.coverSource divides g.inputs)

/-- The structural selection uses the exact exceptional package. -/
theorem selectedCoverData_of_exceptional (h : (n, Nat.card F) = (3, 3)) :
    selectedCoverData parameters N Msys rank odd nondefining divides inputs =
      let e := inputs.exceptional h
      exceptionalData N parameters h e.omega e.freeSource Msys.prime odd nondefining := by
  classical
  simp only [selectedCoverData, dif_pos h]

/-- Generic finiteness is installed only after this branch is selected. -/
theorem selectedCoverData_of_generic (h : (n, Nat.card F) ≠ (3, 3)) :
    selectedCoverData parameters N Msys rank odd nondefining divides inputs =
      let g := inputs.generic h
      letI := g.cliffordFinite
      genericData N g.coverSource Msys.prime odd := by
  classical
  simp only [selectedCoverData, dif_neg h]

/-- The exceptional result is on that same package's family and actual cover. -/
theorem Witness_of_exceptional (h : (n, Nat.card F) = (3, 3)) :
    Witness parameters N Msys rank odd nondefining divides inputs =
      let e := inputs.exceptional h
      NormalizedFamilyWitness
        (familyAlgebra := (show Algebra O K from inferInstance))
        (family := TypeBProposition44ExceptionalInputs.family N parameters h e.omega
          e.freeSource Msys odd nondefining divides e.inputs)
        Msys (TypeBProposition44ExceptionalInputs.selectedCover N parameters h e.omega
          e.freeSource Msys odd nondefining) := by
  classical
  simp only [Witness, dif_pos h]

/-- The generic result retains its own exact family and ordinary-root requirements. -/
theorem Witness_of_generic (h : (n, Nat.card F) ≠ (3, 3)) :
    Witness parameters N Msys rank odd nondefining divides inputs =
      let g := inputs.generic h
      letI := g.cliffordFinite
      letI : NeZero f := fieldDegreeNeZero parameters
      NormalizedFamilyWitness
        (familyAlgebra := (show Algebra O K from inferInstance))
        (family := TypeBProposition44GenericInputs.family parameters N g.fs Msys
          (applicability parameters Msys.prime odd nondefining rank) g.choice
          g.coverSource divides g.inputs)
        Msys (TypeBProposition44GenericInputs.cover parameters N g.fs Msys
          (applicability parameters Msys.prime odd nondefining rank) g.choice
          g.coverSource divides g.inputs) := by
  classical
  simp only [Witness, dif_neg h]

/-- The selected structural quotient is the caller's same Omega N. -/
def simpleQuotientEquiv :
    (selectedCoverData parameters N Msys rank odd nondefining divides inputs).cover.S ≃* Omega N :=
  (selectedCoverData parameters N Msys rank odd nondefining divides inputs).simpleQuotient

/-- The exceptional family uses the literal canonical covering map. -/
theorem exceptional_cover_quotient (h : (n, Nat.card F) = (3, 3)) :
    let e := inputs.exceptional h
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters h e.omega
    (TypeBProposition44ExceptionalInputs.selectedCover N parameters h e.omega
      e.freeSource Msys odd nondefining).quotient = exceptionalProjection N := rfl

/-- The exceptional witness and structural display use the same full cover record. -/
theorem exceptional_cover_binding (h : (n, Nat.card F) = (3, 3)) :
    let e := inputs.exceptional h
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters h e.omega
    TypeBProposition44ExceptionalInputs.selectedCover N parameters h e.omega
      e.freeSource Msys odd nondefining =
      (exceptionalData N parameters h e.omega e.freeSource Msys.prime odd nondefining).cover := rfl

/-- The generic witness and structural display use the same full Spin cover record. -/
theorem generic_cover_binding (h : (n, Nat.card F) ≠ (3, 3)) :
    let g := inputs.generic h
    letI := g.cliffordFinite
    letI : NeZero f := fieldDegreeNeZero parameters
    TypeBProposition44GenericInputs.cover parameters N g.fs Msys
      (applicability parameters Msys.prime odd nondefining rank) g.choice
      g.coverSource divides g.inputs =
      (genericData N g.coverSource Msys.prime odd).cover := rfl

/-- Both independently established branches give the full uniform proposition. -/
theorem proposition_4_4_modular_instantiated :
    Nonempty (Witness parameters N Msys rank odd nondefining divides inputs) := by
  classical
  by_cases h : (n, Nat.card F) = (3, 3)
  · let e := inputs.exceptional h
    simpa only [Witness, dif_pos h] using
      TypeBProposition44ExceptionalInputs.witness N parameters h e.omega e.freeSource
        Msys odd nondefining divides e.inputs
  · let g := inputs.generic h
    letI := g.cliffordFinite
    letI : NeZero f := fieldDegreeNeZero parameters
    simpa only [Witness, dif_neg h] using
      (show Nonempty (NormalizedFamilyWitness
        (familyAlgebra := (show Algebra O K from inferInstance))
        (family := TypeBProposition44GenericInputs.family parameters N g.fs Msys
          (applicability parameters Msys.prime odd nondefining rank) g.choice
          g.coverSource divides g.inputs)
        Msys (TypeBProposition44GenericInputs.cover parameters N g.fs Msys
          (applicability parameters Msys.prime odd nondefining rank) g.choice
          g.coverSource divides g.inputs)) from
        ⟨TypeBProposition44GenericInputs.witness parameters N g.fs Msys
          (applicability parameters Msys.prime odd nondefining rank) g.choice
          g.coverSource divides g.inputs⟩)

end ModularRep.PaperProofs.TypeBProposition44UniformInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
