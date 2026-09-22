import ModularRep.PaperProofs.TypeBProposition44UniformInstantiation
import ModularRep.PaperProofs.TypeBCurrentCertificate
import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding

/-!
# The retained odd-prime proof in the current actual-group certificate

The earlier normalized complete-family proof is retained. Its numerical
choice of the generic Spin cover or exceptional cover is unfolded only
to expose the family and cover already used by that proof. The current
matrix Omega coordinates are supplied by the constructed Clifford map.
No change of matching, coefficient system or local presentation occurs.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCurrentOddCertificate

open ModularRep TypeBCliffordCarriers TypeBSpinCoverSource
open TypeBExceptionalCanonicalCover TypeBProposition44SelectedCover
open TypeBProposition44UniformInstantiation TypeBFullCriterionSplittingSource
open TypeBCurrentCertificate

variable {n p f ell : ℕ} {F k K O : Type}
  [Field F] [Finite F] [CharP F p]
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (parameters : OddFieldParameters F p f) (N : NormSource n F)
  (Msys : ModularSystem ell K O k)
  (rank : 3 ≤ n) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
  (divides : ell ∣ Nat.card (Omega N))

/-- The complete accepted output supplies its own exact selected family. -/
theorem quotientCertificate
    (inputs : TypeBProposition44UniformInstantiation.Inputs parameters N Msys
      rank odd nondefining divides) : Nonempty (IBAWCertificate (Omega N) ell) := by
  classical
  obtain ⟨witness⟩ := proposition_4_4_modular_instantiated
    parameters N Msys rank odd nondefining divides inputs
  by_cases exceptional : (n, Nat.card F) = (3, 3)
  · let e := inputs.exceptional exceptional
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional e.omega
    have complete : NormalizedFamilyWitness
        (familyAlgebra := (show Algebra O K from inferInstance))
        (family := TypeBProposition44ExceptionalInputs.family N parameters exceptional e.omega
          e.freeSource Msys odd nondefining divides e.inputs)
        Msys (TypeBProposition44ExceptionalInputs.selectedCover N parameters exceptional e.omega
          e.freeSource Msys odd nondefining) := by
      simpa only [Witness, dif_pos exceptional] using witness
    exact ⟨.family _ _ (MulEquiv.refl (Omega N))
      (NormalizedFamilyWitness.full
        (family := TypeBProposition44ExceptionalInputs.family N parameters exceptional e.omega
          e.freeSource Msys odd nondefining divides e.inputs)
        (familyAlgebra := (show Algebra O K from inferInstance)) (Msys := Msys) complete)⟩
  · let g := inputs.generic exceptional
    letI := g.cliffordFinite
    letI : NeZero f := fieldDegreeNeZero parameters
    have complete : NormalizedFamilyWitness
        (familyAlgebra := (show Algebra O K from inferInstance))
        (family := TypeBProposition44GenericInputs.family parameters N g.fs Msys
          (applicability parameters Msys.prime odd nondefining rank) g.choice
          g.coverSource divides g.inputs)
        Msys (TypeBProposition44GenericInputs.cover parameters N g.fs Msys
          (applicability parameters Msys.prime odd nondefining rank) g.choice
          g.coverSource divides g.inputs) := by
      simpa only [Witness, dif_neg exceptional] using witness
    exact ⟨.family _ _ (MulEquiv.refl (Omega N))
      (NormalizedFamilyWitness.full
        (family := TypeBProposition44GenericInputs.family parameters N g.fs Msys
          (applicability parameters Msys.prime odd nondefining rank) g.choice
          g.coverSource divides g.inputs)
        (familyAlgebra := (show Algebra O K from inferInstance)) (Msys := Msys) complete)⟩

/-- The first-isomorphism-theorem coordinates connect the retained proof
to the independently defined matrix group in the current statement. -/
theorem matrixCertificate
    (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (inputs : TypeBProposition44UniformInstantiation.Inputs parameters N Msys
      rank odd nondefining divides) :
    Nonempty (IBAWCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) ell) := by
  obtain ⟨certificate⟩ := quotientCertificate parameters N Msys rank odd nondefining divides inputs
  exact ⟨certificate.along
    (TypeBCliffordOrthogonalSourceBinding.matrixOmegaEquiv n F N parameters rank C centre)⟩

end ModularRep.PaperProofs.TypeBCurrentOddCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
