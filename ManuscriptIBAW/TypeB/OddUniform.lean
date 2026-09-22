import ManuscriptIBAW.TypeB.OddApplication
import ModularRep.PaperProofs.TypeBProposition44ExceptionalInputs
import ModularRep.PaperProofs.TypeBProposition44SelectedCover
import ManuscriptIBAW.FamilyCertificate

/-!
# Proposition 4.3, including the exceptional case at odd primes

The generic Spin case uses the central character argument and Conlon's
theorem. The case (3,3) uses the specified sixfold cover and the theorem for
cyclic defect groups. A numerical case distinction fixes the primitive
family and covering map before applying either theorem. All source
assumptions remain explicit.
-/

noncomputable section
namespace ManuscriptIBAW.TypeB.OddUniform
open ModularRep ModularRep.PaperProofs
open TypeBCliffordCarriers TypeBSpinCoverSource
open TypeBExceptionalCanonicalCover TypeBProposition44SelectedCover
open TypeBFullCriterionSplittingSource TypeBFullBlockCondition
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions TypeBCurrentCertificate

variable {n p f ell : ℕ} {F k K O : Type}
  [Field F] [Finite F] [CharP F p]
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (parameters : OddFieldParameters F p f) (N : NormSource n F)
  (Msys : ModularSystem ell K O k)
  (rank : 3 ≤ n) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
  (divides : ell ∣ Nat.card (Omega N))

/-- Only the generic branch needs these actual Clifford and character data. -/
structure GenericBranch where
  [cliffordFinite : Finite (Clifford n F)]
  coverSource : GenericSpinCoverSource (p := p) (f := f) (ell := ell) N
  fs : FieldActionSource n F p f parameters N
  choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K
  inputs :
    letI : NeZero f := fieldDegreeNeZero parameters
    OddApplication.Inputs parameters N fs Msys
      (applicability parameters Msys.prime odd nondefining rank) choice coverSource divides

/-- The exceptional cover is fixed by structural sources before its block data. -/
structure ExceptionalBranch (exceptional : (n, Nat.card F) = (3, 3)) where
  omega : ExceptionalOmegaSource N parameters exceptional
  freeSource : FreePresentationCoverSource
  inputs : TypeBProposition44ExceptionalInputs.Inputs N parameters exceptional omega
    freeSource Msys odd nondefining divides

/-- Each independent source family is required only on its numerical branch. -/
structure Inputs where
  generic : (n, Nat.card F) ≠ (3, 3) →
    GenericBranch parameters N Msys rank odd nondefining divides
  exceptional : ∀ h : (n, Nat.card F) = (3, 3),
    ExceptionalBranch parameters N Msys odd nondefining divides h

/-- A family and actual cover, with no witness to the inductive condition. -/
structure Target (S : Type) [Group S] (ell : ℕ) where
  family : Definition35Family ell
  cover : EllPrimeCoverSource ell family.H
  simpleEquiv : cover.S ≃* S

variable (inputs : Inputs parameters N Msys rank odd nondefining divides)

/-- Fix the family in the proposition before applying the theorem. -/
def target : Target (Omega N) ell := by
  classical
  exact if exceptional : (n, Nat.card F) = (3, 3) then
    let e := inputs.exceptional exceptional
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional e.omega
    {
      family := TypeBProposition44ExceptionalInputs.family N parameters exceptional e.omega
        e.freeSource Msys odd nondefining divides e.inputs
      cover := TypeBProposition44ExceptionalInputs.selectedCover N parameters exceptional e.omega
        e.freeSource Msys odd nondefining
      simpleEquiv := MulEquiv.refl (Omega N) }
  else
    let g := inputs.generic exceptional
    letI := g.cliffordFinite
    letI : NeZero f := fieldDegreeNeZero parameters
    {
      family := OddApplication.family parameters N g.fs Msys
        (applicability parameters Msys.prime odd nondefining rank) g.choice g.coverSource divides g.inputs
      cover := OddApplication.cover parameters N g.fs Msys
        (applicability parameters Msys.prime odd nondefining rank) g.choice g.coverSource divides g.inputs
      simpleEquiv := MulEquiv.refl (Omega N) }

/-- Both case proofs establish the full inductive condition on the specified
family. -/
theorem complete :
    Nonempty (FamilyWitness
      (target parameters N Msys rank odd nondefining divides inputs).family
      (target parameters N Msys rank odd nondefining divides inputs).cover) := by
  classical
  by_cases exceptional : (n, Nat.card F) = (3, 3)
  · let e := inputs.exceptional exceptional
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional e.omega
    let T : Target (Omega N) ell := {
      family := TypeBProposition44ExceptionalInputs.family N parameters exceptional e.omega
        e.freeSource Msys odd nondefining divides e.inputs
      cover := TypeBProposition44ExceptionalInputs.selectedCover N parameters exceptional e.omega
        e.freeSource Msys odd nondefining
      simpleEquiv := MulEquiv.refl (Omega N) }
    have hT : target parameters N Msys rank odd nondefining divides inputs = T := by
      simp only [target, dif_pos exceptional]
      rfl
    obtain ⟨witness⟩ := TypeBProposition44ExceptionalInputs.witness
      N parameters exceptional e.omega e.freeSource Msys odd nondefining divides e.inputs
    exact (congrArg (fun U : Target (Omega N) ell =>
      Nonempty (FamilyWitness U.family U.cover)) hT).mpr
        ⟨NormalizedFamilyWitness.full
          (familyAlgebra := (show Algebra O K from inferInstance)) witness⟩
  · let g := inputs.generic exceptional
    letI := g.cliffordFinite
    letI : NeZero f := fieldDegreeNeZero parameters
    let T : Target (Omega N) ell := {
      family := OddApplication.family parameters N g.fs Msys
        (applicability parameters Msys.prime odd nondefining rank) g.choice g.coverSource divides g.inputs
      cover := OddApplication.cover parameters N g.fs Msys
        (applicability parameters Msys.prime odd nondefining rank) g.choice g.coverSource divides g.inputs
      simpleEquiv := MulEquiv.refl (Omega N) }
    have hT : target parameters N Msys rank odd nondefining divides inputs = T := by
      simp only [target, dif_neg exceptional]
      rfl
    let witness := OddApplication.witness parameters N g.fs Msys
      (applicability parameters Msys.prime odd nondefining rank) g.choice g.coverSource divides g.inputs
    exact (congrArg (fun U : Target (Omega N) ell =>
      Nonempty (FamilyWitness U.family U.cover)) hT).mpr
        ⟨NormalizedFamilyWitness.full
          (familyAlgebra := (show Algebra O K from inferInstance)) witness⟩

include inputs in
/-- The same family establishes the full inductive condition for the specified
group. -/
theorem certificate : Nonempty (FamilyCertificate (Omega N) ell) := by
  obtain ⟨witness⟩ := complete parameters N Msys rank odd nondefining divides inputs
  let T := target parameters N Msys rank odd nondefining divides inputs
  exact ⟨⟨T.family, T.cover, T.simpleEquiv, witness⟩⟩

end ManuscriptIBAW.TypeB.OddUniform

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
