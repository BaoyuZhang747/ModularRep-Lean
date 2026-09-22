import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.RepresentationTheory.Irreducible

/-!
# Scalar action of central subgroups

This file packages the scalar by which a central element acts on a finite dimensional
irreducible representation over an algebraically closed field.  The scalars form a unique
multiplicative character of the central subgroup.
-/

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The action of a central subgroup, regarded as intertwining endomorphisms. -/
def centralIntertwiningMapHom (rho : Representation k G V) (Z : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) : Z →* IntertwiningMap rho rho where
  toFun z :=
    { toLinearMap := rho (z : G)
      isIntertwining' g := by
        change rho (z : G) * rho g = rho g * rho (z : G)
        rw [← rho.map_mul, ← rho.map_mul]
        exact congrArg rho ((Subgroup.mem_center_iff.mp (hZ z.property) g).symm) }
  map_one' := by
    apply IntertwiningMap.ext
    exact rho.map_one
  map_mul' z w := by
    apply IntertwiningMap.ext
    exact rho.map_mul z w

variable [FiniteDimensional k V] [IsAlgClosed k]

/-- Schur's lemma as an algebra equivalence between scalars and intertwining endomorphisms. -/
noncomputable def scalarIntertwiningEquiv (rho : Representation k G V) [rho.IsIrreducible] :
    k ≃ₐ[k] IntertwiningMap rho rho :=
  AlgEquiv.ofBijective (Algebra.ofId k (IntertwiningMap rho rho))
    IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed

@[simp]
theorem scalarIntertwiningEquiv_toLinearMap (rho : Representation k G V) [rho.IsIrreducible]
    (c : k) : (scalarIntertwiningEquiv rho c).toLinearMap = c • LinearMap.id := by
  change (algebraMap k (IntertwiningMap rho rho) c).toLinearMap = c • LinearMap.id
  rw [IntertwiningMap.algebraMap_apply, IntertwiningMap.toLinearMap_smul]
  rfl

/-- The scalar by which each element of a central subgroup acts. -/
noncomputable def centralScalar (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) : Z →* k :=
  (scalarIntertwiningEquiv rho).symm.toMonoidHom.comp
    (centralIntertwiningMapHom rho Z hZ)

/-- The multiplicative central character of an irreducible representation. -/
noncomputable def centralCharacter (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) : Z →* kˣ :=
  (centralScalar rho Z hZ).toHomUnits

theorem centralScalar_spec (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) (z : Z) :
    rho (z : G) = centralScalar rho Z hZ z • LinearMap.id := by
  have h := (scalarIntertwiningEquiv rho).apply_symm_apply
    (centralIntertwiningMapHom rho Z hZ z)
  have ht := congrArg IntertwiningMap.toLinearMap h.symm
  change rho (z : G) =
    (scalarIntertwiningEquiv rho (centralScalar rho Z hZ z)).toLinearMap at ht
  simpa only [scalarIntertwiningEquiv_toLinearMap] using ht

theorem centralCharacter_spec (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) (z : Z) :
    rho (z : G) = (centralCharacter rho Z hZ z : k) • LinearMap.id := by
  simpa [centralCharacter] using centralScalar_spec rho Z hZ z

/-- A central subgroup acts through a unique multiplicative character into the nonzero scalars. -/
theorem existsUnique_centralCharacter (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) :
    ∃! nu : Z →* kˣ, ∀ z : Z, rho (z : G) = (nu z : k) • LinearMap.id := by
  refine ⟨centralCharacter rho Z hZ, centralCharacter_spec rho Z hZ, ?_⟩
  intro nu hnu
  ext z
  apply (scalarIntertwiningEquiv rho).injective
  apply IntertwiningMap.toLinearMap_injective
  simpa only [scalarIntertwiningEquiv_toLinearMap] using
    (hnu z).symm.trans (centralCharacter_spec rho Z hZ z)

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
