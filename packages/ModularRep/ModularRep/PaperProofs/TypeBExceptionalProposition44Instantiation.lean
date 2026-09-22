import ModularRep.PaperProofs.TypeBExceptionalCanonicalCover
import ModularRep.PaperProofs.TypeBExceptionalCyclicSplittingSource

/-!
# The exceptional odd-prime application on the canonical sixfold cover

The quotient is the same Omega N over the caller's field of order three.
Its cover and projection are fixed free-presentation constructions.
Order, prime enumeration and cyclicity are proved before the generic
published cyclic-defect implication is applied. Local specified block
compatibility is derived from the ordinary sources in the same modular
system. No exceptional character matching or final condition is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBExceptionalProposition44Instantiation

open ModularRep FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBSpinCoverSource
open TypeBExceptionalCanonicalCover TypeBExceptionalOddPrimeOrder
open TypeBExceptionalPrimitiveFamilySplitting TypeBLocalReductionInstantiation
open TypeBLocalPhysicalBlockBinding TypeBFullCriterionSplittingSource
open EvenFieldFLZSourceConditions

variable {n p f ell : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  (N : NormSource n F) (parameters : OddFieldParameters F p f)
  (exceptional : (n, Nat.card F) = (3, 3))
  (omega : ExceptionalOmegaSource N parameters exceptional)
  (freeSource : FreePresentationCoverSource)

include exceptional in
theorem nondefining_three (nondefining : ¬ ell ∣ Nat.card F) : ell ≠ 3 := by
  have hq : Nat.card F = 3 := congrArg Prod.snd exceptional
  intro heq
  apply nondefining
  simpa only [hq, heq] using (dvd_refl 3)

include parameters exceptional omega freeSource in
/-- The existing order deduction applies to every actual subgroup of this cover. -/
theorem every_nondefining_subgroup_cyclic
    (prime : ell.Prime) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
    (divides : ell ∣ Nat.card (Omega N)) :
    ∀ D : Subgroup (ExceptionalCover N), IsPGroup ell D → IsCyclic D := by
  letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
  have hCover : ell ∣ Nat.card (ExceptionalCover N) := divides.trans
    (Subgroup.card_dvd_of_surjective (exceptionalProjection N)
      (projection_surjective N parameters exceptional omega freeSource))
  have hcard := cover_order N parameters exceptional omega freeSource
  obtain ⟨t, ht⟩ := exists_exceptionalPrime prime odd
    (nondefining_three exceptional nondefining) (hcard ▸ hCover)
  intro D hD
  exact everyPrimeSubgroupCyclic_of_order t hcard D (ht ▸ hD)

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  [Fintype (LiteralPrimitiveBlock k (ExceptionalCover N))]
  [HasEnoughRootsOfUnity K (Nat.card (ExceptionalCover N))]

/-- Source-instantiated exceptional output with all specified and root carriers fixed. -/
theorem exceptional_proposition_4_4_modular_instantiated
    (Msys : ModularSystem ell K O k)
    (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
    (divides : ell ∣ Nat.card (Omega N)) :
    letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
    ∀
    (data : PrimitiveBlockData ell k K (ExceptionalCover N))
    (navarro : ∀ (T : Type) [Group T] [Finite T]
      [HasEnoughRootsOfUnity K (Nat.card T)]
      (iota : PrimeRegularRootEmbedding ell k K T)
      (compatible : RootResidueCompatible Msys iota),
        ScopedDefectZeroReductionSource Msys iota compatible)
    (expansion : ∀ (T : Type) [Group T] [Finite T]
      [HasEnoughRootsOfUnity K (Nat.card T)],
        ScopedDecompositionExpansionSource (H := T) Msys)
    (ordinary : ∀ Q : Subgroup (ExceptionalCover N),
      NormalizerOrdinarySource Msys data.blockSource.operations Q)
    (membership : OrdinaryInflationMembership Msys data.blockSource.operations ordinary)
    (coefficient : SpathCoefficientField ell k Msys.prime)
    (source : TypeBExceptionalCyclicSplittingSource.CyclicDefectSplittingCertificate),
    Nonempty (NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := primitiveFamily Msys data navarro)
      Msys (ellPrimeCover N parameters exceptional omega freeSource Msys.prime odd
        (nondefining_three exceptional nondefining))) := by
  letI : Fintype (ExceptionalCover N) := coverFintype N parameters exceptional omega
  intro data navarro expansion ordinary membership coefficient source
  let physical := primitiveFamily_blockCompatibility Msys data navarro
    expansion ordinary membership
  exact ⟨TypeBExceptionalCyclicSplittingSource.witness Msys data navarro physical
    coefficient (ellPrimeCover N parameters exceptional omega freeSource Msys.prime odd
      (nondefining_three exceptional nondefining)) odd source divides
    (every_nondefining_subgroup_cyclic N parameters exceptional omega freeSource
      Msys.prime odd nondefining divides)⟩

end ModularRep.PaperProofs.TypeBExceptionalProposition44Instantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
