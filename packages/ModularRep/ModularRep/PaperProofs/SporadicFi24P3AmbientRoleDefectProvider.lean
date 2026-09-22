import Mathlib.Data.ZMod.Basic
import ModularRep.DefectNormalizerSandwich
import ModularRep.Navarro411CentralBrauerAdapter
import ModularRep.PaperProofs.SporadicFi24P3QSquaredAmbientUniqueness

/-!
# Positive ambient role-defect provider for `Fi'_{24}` at three

This file supplies a positive interface from which the two exclusions in
`SporadicFi24P3QSquaredAmbientUniqueness.Source` can be constructed.  The
source is independent of the nominated subgroup `Q`: it records a full-defect
representative for the named principal block and the trivial representative
for the named defect-zero block on the existing literal ambient catalogue.

The kernel then compares any second Navarro (4.11) representative for the
same literal block by conjugacy and cardinality.  A subgroup of cardinality
`3^2` can therefore be neither the full-defect representative of cardinality
`3^16` nor the trivial representative.  The elementary-abelian presentation
of `Q` is used only to derive its cardinality.

There is no concrete `Fi'_{24}` instance or transcript-to-block map here.  No
uniqueness, First Main image, cancellation, character--weight correspondence,
BAW, or iBAW assertion is an input to the provider.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3AmbientRoleDefectProvider

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3QSquaredCarrierAlignment

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance primeThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ## Positive external role-defect data -/

/-- Positive defect representatives for the two named ambient block roles,
on the literal ambient catalogue carried by `R`.

The full-defect principal representative and the defect-zero trivial
representative are composite E1/E2/U inputs: published block-defect facts
must still be matched to the literal group, subgroup, and block-role carriers.
An external computation transcript may provide optional E3 corroboration for
a future concrete provider, but it is not required by this abstract source.
The record is deliberately independent of any nominated subgroup `Q`. -/
structure Fi24P3AmbientRoleDefectSource
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (three : Fi24ThreeBlockSource (k := k) (X := X)) : Prop where
  principal_fullDefectRepresentative :
    ∃ D : Subgroup X,
      AmbientHasDefect R D three.principalBlock ∧ Nat.card D = 3 ^ 16
  defectZero_trivialRepresentative :
    AmbientHasDefect R (⊥ : Subgroup X) three.defectZeroBlock

/-! ## Kernel comparison lemmas -/

/-- Two Navarro (4.11) defect representatives for the same literal ambient
block are conjugate. -/
theorem ambientHasDefect_areConjugate
    {R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X)}
    {B : ActualBlock (k := k) (X := X)}
    {D E : Subgroup X}
    (hD : AmbientHasDefect R D B)
    (hE : AmbientHasDefect R E B) :
    D.AreConjugate E := by
  let O := R.1.operations
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  change Navarro411DefectRepresentative
    O.ambientBlockData.blocks B D at hD
  change Navarro411DefectRepresentative
    O.ambientBlockData.blocks B E at hE
  exact Navarro411CentralBrauerSource.areConjugate
    hD.isPGroup hE.isPGroup hD.support411 hE.support411

/-- Two Navarro (4.11) defect representatives for the same literal ambient
block have the same cardinality. -/
theorem ambientHasDefect_card_eq
    {R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X)}
    {B : ActualBlock (k := k) (X := X)}
    {D E : Subgroup X}
    (hD : AmbientHasDefect R D B)
    (hE : AmbientHasDefect R E B) :
    Nat.card D = Nat.card E :=
  (ambientHasDefect_areConjugate hD hE).card_eq

omit [Fintype X] in
/-- The displayed elementary-abelian presentation has cardinality `3^2`.
This is a kernel cardinality calculation and contains no group or subgroup
identification with `Fi'_{24}`. -/
theorem card_eq_three_sq_of_elementary
    {Q : Subgroup X}
    (hQ : Q ≃* Multiplicative (Fin 2 → ZMod 3)) :
    Nat.card Q = 3 ^ 2 := by
  calc
    Nat.card Q = Nat.card (Multiplicative (Fin 2 → ZMod 3)) :=
      Nat.card_congr hQ.toEquiv
    _ = Fintype.card (Multiplicative (Fin 2 → ZMod 3)) :=
      Nat.card_eq_fintype_card
    _ = 3 ^ 2 := by
      simp only [Fintype.card_multiplicative, Fintype.card_fun,
        Fintype.card_fin, ZMod.card]

/-! ## Construction of the existing two-negative consumer -/

/-- Positive ambient role-defect representatives exclude a nominated subgroup
of cardinality `3^2` from the principal and defect-zero roles.  The result is
exactly the existing two-field consumer source; it contains no existence or
uniqueness statement for the remaining block. -/
theorem source_of_roleDefects_of_card
    {R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X)}
    {three : Fi24ThreeBlockSource (k := k) (X := X)}
    {Q : Subgroup X}
    (S : Fi24P3AmbientRoleDefectSource R three)
    (hQcard : Nat.card Q = 3 ^ 2) :
    SporadicFi24P3QSquaredAmbientUniqueness.Source R three Q := by
  constructor
  · intro hPrincipal
    obtain ⟨D, hD, hDcard⟩ := S.principal_fullDefectRepresentative
    have hcard : Nat.card Q = Nat.card D :=
      ambientHasDefect_card_eq hPrincipal hD
    rw [hQcard, hDcard] at hcard
    exact (by decide : (3 ^ 2 : Nat) ≠ 3 ^ 16) hcard
  · intro hDefectZero
    have hcard : Nat.card Q = Nat.card (⊥ : Subgroup X) :=
      ambientHasDefect_card_eq hDefectZero
        S.defectZero_trivialRepresentative
    have hbot : Nat.card (⊥ : Subgroup X) = 1 := by simp
    rw [hQcard, hbot] at hcard
    exact (by decide : (3 ^ 2 : Nat) ≠ 1) hcard

/-- The elementary-abelian presentation of `Q` supplies the cardinality input
to `source_of_roleDefects_of_card`. -/
theorem source_of_roleDefects_of_elementary
    {R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X)}
    {three : Fi24ThreeBlockSource (k := k) (X := X)}
    {Q : Subgroup X}
    (S : Fi24P3AmbientRoleDefectSource R three)
    (hQ : Q ≃* Multiplicative (Fin 2 → ZMod 3)) :
    SporadicFi24P3QSquaredAmbientUniqueness.Source R three Q :=
  source_of_roleDefects_of_card S
    (card_eq_three_sq_of_elementary hQ)

end ModularRep.PaperProofs.SporadicFi24P3AmbientRoleDefectProvider


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
