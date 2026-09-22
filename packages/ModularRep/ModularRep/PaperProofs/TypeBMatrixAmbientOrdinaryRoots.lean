import ModularRep.PaperProofs.TypeBSpinSOOrdinaryRoots
import ModularRep.PaperProofs.TypeBRankThreePrincipalMatchedInertia
import ModularRep.PaperProofs.TypeBLocalOrdinaryExtensionSplitting
import ModularRep.PaperProofs.TypeBExtensionClausesSplitting

/-!
# Sufficient ordinary roots for the actual matrix ambient and local quotients

The ambient group is the existing SO and field semidirect product. Its
order includes the full field degree. A sufficient-root guard for that
order supplies SO, Spin and the two raw-inertia quotient guards in the
same coefficient field. The checked cyclic extension construction then applies
to these literal groups and the prescribed Brauer root.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBMatrixAmbientOrdinaryRoots

open ModularRep TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers
open TypeBCliffordOrthogonalAmbientQuotient TypeBRankThreePrincipalMatchedInertia
open TypeBCriterionHypotheses TypeBLocalOrdinaryGeometry

variable {p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  (parameters : OddFieldParameters F p f)
  (N : NormSource 3 F) (fieldSource : FieldActionSource 3 F p f parameters N)
  (C : TypeBCliffordOrthogonalSourceBinding.Source
    3 F p f parameters (Nat.le_refl 3) N)

/-- The actual field degree is positive in the displayed parameter scope. -/
def fieldDegreeNeZero : NeZero f := ⟨parameters.exponent_pos.ne'⟩

/-- The cardinal of the displayed cyclic field carrier is its degree. -/
theorem fieldGroup_card (f : ℕ) : Nat.card (FieldGroup f) = f :=
  (Nat.card_congr (Multiplicative.toAdd : FieldGroup f ≃ ZMod f)).trans (Nat.card_zmod f)

/-- The existing matrix ambient retains its prescribed complete field action. -/
abbrev MatrixAmbient := OrthogonalAmbient 3 F parameters (Nat.le_refl 3) N C fieldSource

local notation "matrixField" =>
  soFieldAction 3 F parameters (Nat.le_refl 3) N C fieldSource
local notation "matrixAction" => matrixNaturalAction F parameters N fieldSource C

/-- Counting the literal semidirect carrier includes the full field degree. -/
theorem ambient_card :
    Nat.card (MatrixAmbient parameters N fieldSource C) =
      Nat.card (SpecialOrthogonal 3 F) * f := by
  change Nat.card (SpecialOrthogonal 3 F ⋊[matrixField] FieldGroup f) = _
  rw [SemidirectProduct.card, fieldGroup_card]

/-- The SO order divides the order of its actual field ambient. -/
theorem so_order_dvd_ambient :
    Nat.card (SpecialOrthogonal 3 F) ∣ Nat.card (MatrixAmbient parameters N fieldSource C) :=
  ⟨f, ambient_card parameters N fieldSource C⟩

/-- Only the actual SO quotient by Omega is shown to be cyclic. -/
theorem omegaQuotient_isCyclic (indexTwo : (omegaSubgroup 3 F).index = 2) :
    IsCyclic (SpecialOrthogonal 3 F ⧸ omegaSubgroup 3 F) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCyclic_of_prime_card ((omegaSubgroup 3 F).index_eq_card.symm.trans indexTwo)

section Roots

variable [NeZero f] {K : Type} [Field K]
  [HasEnoughRootsOfUnity K (Nat.card (MatrixAmbient parameters N fieldSource C))]

/-- The ambient sufficient-root guard supplies the actual SO guard. -/
def soOrdinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialOrthogonal 3 F)) :=
  HasEnoughRootsOfUnity.of_dvd K (so_order_dvd_ambient parameters N fieldSource C)

/-- The same ambient guard supplies Spin roots through the proved order equality. -/
def spinOrdinaryRoots (indexTwo : (omegaSubgroup 3 F).index = 2) :
    HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N)) := by
  letI := soOrdinaryRoots (K := K) parameters N fieldSource C
  exact TypeBSpinSOOrdinaryRoots.spinOrdinaryRoots
    (K := K) N parameters (Nat.le_refl 3) C indexTwo

end Roots

section LocalQuotients

variable [NeZero f] {ell : ℕ} {K : Type} [Field K] [CharZero K]
  (W : CharacterWeight ell K (omegaSubgroup 3 F))

/-- The actual SO-side raw inertia, modulo its embedded radical. -/
abbrev MInertiaQuotient :=
  Inertia (omegaSubgroup 3 F) matrixField matrixAction W (embeddedM matrixField) ⧸
    RadicalInInertia (omegaSubgroup 3 F) matrixField matrixAction W (embeddedM matrixField)

/-- The actual Omega-and-field-side raw inertia, modulo the same embedded radical. -/
abbrev GEInertiaQuotient :=
  Inertia (omegaSubgroup 3 F) matrixField matrixAction W
      (baseFieldGroup (omegaSubgroup 3 F) matrixField) ⧸
    RadicalInInertia (omegaSubgroup 3 F) matrixField matrixAction W
      (baseFieldGroup (omegaSubgroup 3 F) matrixField)

theorem mInertia_order_dvd_ambient :
    Nat.card (MInertiaQuotient parameters N fieldSource C W) ∣
      Nat.card (MatrixAmbient parameters N fieldSource C) :=
  TypeBLocalOrdinaryExtensionSplitting.local_order_dvd_ambient
    (omegaSubgroup 3 F) matrixField matrixAction W (embeddedM matrixField)

theorem geInertia_order_dvd_ambient :
    Nat.card (GEInertiaQuotient parameters N fieldSource C W) ∣
      Nat.card (MatrixAmbient parameters N fieldSource C) :=
  TypeBLocalOrdinaryExtensionSplitting.local_order_dvd_ambient
    (omegaSubgroup 3 F) matrixField matrixAction W
    (baseFieldGroup (omegaSubgroup 3 F) matrixField)

variable [HasEnoughRootsOfUnity K (Nat.card (MatrixAmbient parameters N fieldSource C))]

/-- The accepted local divisor lemma supplies roots for the literal SO-side quotient. -/
def mInertiaOrdinaryRoots :
    HasEnoughRootsOfUnity K (Nat.card (MInertiaQuotient parameters N fieldSource C W)) :=
  TypeBLocalOrdinaryExtensionSplitting.localRoots_of_ambientRoots
    (omegaSubgroup 3 F) matrixField matrixAction W (embeddedM matrixField)

/-- The second guard concerns the literal Omega-and-field-side quotient. -/
def geInertiaOrdinaryRoots :
    HasEnoughRootsOfUnity K (Nat.card (GEInertiaQuotient parameters N fieldSource C W)) :=
  TypeBLocalOrdinaryExtensionSplitting.localRoots_of_ambientRoots
    (omegaSubgroup 3 F) matrixField matrixAction W
    (baseFieldGroup (omegaSubgroup 3 F) matrixField)

end LocalQuotients

section Extensions

variable [NeZero f] {ell : ℕ} {K k : Type}
  [Field K] [CharZero K] [Field k] [CharP k ell] [IsAlgClosed k]
  [HasEnoughRootsOfUnity K (Nat.card (MatrixAmbient parameters N fieldSource C))]
  (iota : PrimeRegularRootEmbedding ell k K (omegaSubgroup 3 F))

/-- The four clauses concern the same actual action, root and two local quotients. -/
theorem extensionClauses
    (indexTwo : (omegaSubgroup 3 F).index = 2)
    (brauerPrinciple : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (ordinaryM : ∀ W : CharacterWeight ell K (omegaSubgroup 3 F),
      letI := mInertiaOrdinaryRoots parameters N fieldSource C W
      TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K
        (MInertiaQuotient parameters N fieldSource C W))
    (ordinaryGE : ∀ W : CharacterWeight ell K (omegaSubgroup 3 F),
      letI := geInertiaOrdinaryRoots parameters N fieldSource C W
      TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K
        (GEInertiaQuotient parameters N fieldSource C W)) :
    ExtensionClauses (omegaSubgroup 3 F) matrixField matrixAction iota :=
  TypeBExtensionClausesSplitting.extensionClauses
    (omegaSubgroup 3 F) matrixField matrixAction iota
    brauerPrinciple (omegaQuotient_isCyclic indexTwo) ordinaryM ordinaryGE

end Extensions

end ModularRep.PaperProofs.TypeBMatrixAmbientOrdinaryRoots


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
