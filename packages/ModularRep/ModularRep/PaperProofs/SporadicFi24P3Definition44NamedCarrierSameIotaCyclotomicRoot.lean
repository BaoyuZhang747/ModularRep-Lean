import ModularRep.CyclotomicRootSumReflection
import ModularRep.PrimeRegularRootEmbeddingSubgroup

/-!
# A conductor root carried by the original root embedding

The target root is the restriction of the original iota. Identification
with a character table's printed root convention remains a literal binding.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot

open ModularRep

universe u v w
variable {p n : ℕ} {k : Type u} {K : Type v} {X : Type w}
variable [Field k] [Field K] [Group X] [Finite X]

structure SameIotaConductorRoot
    (iota : PrimeRegularRootEmbedding p k K X) (n : ℕ) : Type (max u v w) where
  conductor_pos : 0 < n
  conductor_dvd : n ∣ primeRegularExponent p X
  source_root : k
  source_root_isPrimitive : IsPrimitiveRoot source_root n

def sourceRootOfUnity (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) : rootsOfUnity n k := by
  let _ : NeZero n := ⟨Nat.ne_of_gt R.conductor_pos⟩
  exact CyclotomicRootSumReflection.primitiveRootOfUnity R.source_root_isPrimitive

def ambientSourceRoot (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) :
    rootsOfUnity (primeRegularExponent p X) k :=
  PrimeRegularRootEmbedding.rootsOfUnityInclusion R.conductor_dvd (sourceRootOfUnity iota R)

def targetRootOfUnity (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) : rootsOfUnity n K :=
  PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv R.conductor_dvd
    iota.toMulEquiv (sourceRootOfUnity iota R)

def targetRoot (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) : K :=
  ((targetRootOfUnity iota R : Kˣ) : K)

theorem targetRoot_isPrimitive (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) : IsPrimitiveRoot (targetRoot iota R) n := by
  let _ : NeZero n := ⟨Nat.ne_of_gt R.conductor_pos⟩
  simpa only [targetRoot, targetRootOfUnity, sourceRootOfUnity] using
    CyclotomicRootSumReflection.image_primitive_isPrimitive
      (PrimeRegularRootEmbedding.restrictRootsOfUnityEquiv R.conductor_dvd iota.toMulEquiv)
      R.source_root_isPrimitive

theorem targetRoot_eq_iota_lift (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) :
    targetRoot iota R = iota.lift (((ambientSourceRoot iota R : kˣ) : k)) := by
  rw [PrimeRegularRootEmbedding.lift_coe]
  rfl

@[simp]
theorem sourceRootOfUnity_coe (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) :
    ((sourceRootOfUnity iota R : kˣ) : k) = R.source_root := rfl

@[simp]
theorem ambientSourceRoot_coe (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) :
    ((ambientSourceRoot iota R : kˣ) : k) = R.source_root := rfl

theorem targetRoot_eq_iota_lift_source (iota : PrimeRegularRootEmbedding p k K X)
    (R : SameIotaConductorRoot iota n) :
    targetRoot iota R = iota.lift R.source_root := targetRoot_eq_iota_lift iota R

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
