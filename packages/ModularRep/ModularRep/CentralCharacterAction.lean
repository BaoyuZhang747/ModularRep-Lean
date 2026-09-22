import ModularRep.CentralAction
import ModularRep.CentralCharacterIdempotent
import ModularRep.CentralIdempotentSupport
import ModularRep.LinearCharacterOrthogonality

/-!
# Action of central character idempotents

This file connects the scalar action of a central subgroup on an irreducible
representation with the corresponding element of the group algebra.
-/

open scoped BigOperators MonoidAlgebra

namespace Representation

open ModularRep

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

noncomputable local instance linearCharacterDecidableEq {Z : Type*} [Group Z] :
    DecidableEq (Z →* kˣ) := Classical.decEq _

/-- The action of a central character idempotent is the normalised weighted
sum of the actions of the elements of the central subgroup. -/
theorem centralCharacterIdempotent_smul_eq_sum
    (rho : Representation k G V) (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (mu : Z →* kˣ) (v : rho.asModule) :
    rho.asModuleEquiv (centralCharacterIdempotent Z mu • v) =
      ⅟(Fintype.card Z : k) •
        ∑ z : Z, (((mu z)⁻¹ : kˣ) : k) •
          rho (z : G) (rho.asModuleEquiv v) := by
  rw [rho.asModuleEquiv_map_smul,
    ModularRep.centralCharacterIdempotent_eq_weightedSum]
  simp [ModularRep.linearCharacterWeightedSum, map_sum,
    Representation.asAlgebraHom_single,
    Finset.smul_sum, smul_smul]

variable [FiniteDimensional k V] [IsAlgClosed k]

/-- On an irreducible representation, the action of a central character
idempotent is scalar.  The scalar is the normalised pairing of its character
with the central character of the representation. -/
theorem centralCharacterIdempotent_smul_eq_centralCharacterSum
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) (mu : Z →* kˣ) (v : rho.asModule) :
    rho.asModuleEquiv (centralCharacterIdempotent Z mu • v) =
      (⅟(Fintype.card Z : k) *
        ∑ z : Z, (((mu z)⁻¹ * centralCharacter rho Z hZ z : kˣ) : k)) •
          rho.asModuleEquiv v := by
  rw [centralCharacterIdempotent_smul_eq_sum]
  simp_rw [LinearMap.congr_fun (centralCharacter_spec rho Z hZ _) (rho.asModuleEquiv v),
    LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  rw [← Finset.sum_smul, smul_smul]
  congr 1

/-- The idempotent indexed by the central character of an irreducible
representation acts as the identity. -/
@[simp]
theorem centralCharacterIdempotent_centralCharacter_smul
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) (v : rho.asModule) :
    centralCharacterIdempotent Z (centralCharacter rho Z hZ) • v = v := by
  apply rho.asModuleEquiv.injective
  rw [centralCharacterIdempotent_smul_eq_centralCharacterSum rho Z hZ]
  simp

/-- A vanishing character sum makes the corresponding central character
idempotent act as zero. -/
theorem centralCharacterIdempotent_smul_eq_zero_of_sum_eq_zero
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) (mu : Z →* kˣ)
    (hsum :
      (∑ z : Z, (((mu z)⁻¹ * centralCharacter rho Z hZ z : kˣ) : k)) = 0)
    (v : rho.asModule) :
    centralCharacterIdempotent Z mu • v = 0 := by
  apply rho.asModuleEquiv.injective
  rw [centralCharacterIdempotent_smul_eq_centralCharacterSum rho Z hZ mu v, hsum,
    mul_zero, zero_smul, map_zero]

/-- An idempotent indexed by a character different from the central
character of an irreducible representation acts as zero. -/
@[simp]
theorem centralCharacterIdempotent_smul_eq_zero_of_ne
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) (mu : Z →* kˣ)
    (hmu : mu ≠ centralCharacter rho Z hZ) (v : rho.asModule) :
    centralCharacterIdempotent Z mu • v = 0 :=
  centralCharacterIdempotent_smul_eq_zero_of_sum_eq_zero rho Z hZ mu
    (ModularRep.sum_linearCharacter_inv_mul_eq_zero
      mu (centralCharacter rho Z hZ) hmu) v

/-- Every central character idempotent acts on an irreducible representation
as either the identity or zero, according to its index. -/
theorem centralCharacterIdempotent_smul_eq_ite
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) (mu : Z →* kˣ) (v : rho.asModule) :
    centralCharacterIdempotent Z mu • v =
      if mu = centralCharacter rho Z hZ then v else 0 := by
  classical
  by_cases hmu : mu = centralCharacter rho Z hZ
  · subst mu
    simp
  · rw [if_neg hmu, centralCharacterIdempotent_smul_eq_zero_of_ne rho Z hZ mu hmu]

/-- The central character is the support index singled out by the action of
the central character idempotents on an irreducible representation. -/
theorem centralCharacterIdempotent_isSupport
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) :
    CompleteOrthogonalCentralIdempotents.IsSupport
      (V := rho.asModule) (fun mu : Z →* kˣ ↦ centralCharacterIdempotent Z mu)
      (centralCharacter rho Z hZ) := by
  constructor
  · exact centralCharacterIdempotent_centralCharacter_smul rho Z hZ
  · intro mu hmu v
    exact centralCharacterIdempotent_smul_eq_zero_of_ne rho Z hZ mu hmu v

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
