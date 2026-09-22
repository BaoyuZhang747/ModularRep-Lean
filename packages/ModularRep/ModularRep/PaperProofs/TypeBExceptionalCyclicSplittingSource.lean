import ModularRep.PaperProofs.TypeBExceptionalPrimitiveFamilySplitting
import ModularRep.PaperProofs.TypeBFullCriterionSplittingSource

/-!
# The cyclic-defect theorem in one splitting modular system

Koshitani--Spath, J. Group Theory 19 (2016), Theorem 1.1, p. 778,
is used with both displayed primes equal to ell. Its Definition 3.2,
pp. 782--783, retains the actual central quotient, full automorphism
stabilizers, both Brauer extensions and every intermediate block equation.
Lemma 3.3, p. 783, gives Spath Definition 5.17, pp. 208--209.
With the set of all ell-groups, Remark 5.18, p. 209, gives Definition 4.1,
p. 182, including the trivial-radical normalization.

The independent domain below fixes the actual primitive blocks, local
ordinary weights, modular system and its constructed roots. Every actual
ell-subgroup is cyclic, so every block defect group is cyclic. The output
is a newly chosen complete normalized family. It is not obtained by
normalizing an arbitrary previously chosen family witness.

The published existence theorem is E2. Interpreting its finite characters,
specified blocks and all existential Brauer values in this same splitting
modular system is E1. Roots for the original group split its ordinary
subquotient characters; the same complete modular system supplies all
prime-to-ell roots required by the output's finite Brauer ambient groups.
No ordinary algebraic closure or Type B conclusion is an input.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBExceptionalCyclicSplittingSource

open ModularRep FDRepSimpleClassKZero
open EvenFieldFLZSourceConditions TypeBFixedRootDefinitionFamily
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding
open TypeBExceptionalPrimitiveFamilySplitting TypeBFullCriterionSplittingSource

/-- The exact generic one-way cyclic-defect result on a computed specified
family, with one simultaneous modular-system normalization of the output. -/
structure CyclicDefectSplittingCertificate : Prop where
  allBlocks : ∀ {ell : ℕ} {k K O H : Type}
      [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
      [CharP k ell] [IsAlgClosed k] [CharZero K]
      [Group H] [Fintype H] [Fintype (LiteralPrimitiveBlock k H)]
      [HasEnoughRootsOfUnity K (Nat.card H)]
      (Msys : ModularSystem ell K O k)
      (data : PrimitiveBlockData ell k K H)
      (navarro : ∀ (T : Type) [Group T] [Finite T]
        [HasEnoughRootsOfUnity K (Nat.card T)]
        (iota : PrimeRegularRootEmbedding ell k K T)
        (compatible : RootResidueCompatible Msys iota),
          ScopedDefectZeroReductionSource Msys iota compatible)
      (physical : GuardedBlockCompatibility (groupRoot Msys H)
        data.blockSource.operations)
      (coefficient : SpathCoefficientField ell k Msys.prime)
      (cover : EllPrimeCoverSource ell H)
      (odd : Odd ell)
      (divides_simple_order : ell ∣ Nat.card cover.S)
      (cyclic : ∀ P : Subgroup H, IsPGroup ell P → IsCyclic P),
    Nonempty (NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := TypeBExceptionalPrimitiveFamilySplitting.primitiveFamily
        Msys data navarro)
      Msys cover)

/-- Apply the generic theorem only after cyclicity and the actual cover
and local specified data have been supplied independently. -/
def witness {ell : ℕ} {k K O H : Type}
    [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
    [CharP k ell] [IsAlgClosed k] [CharZero K]
    [Group H] [Fintype H] [Fintype (LiteralPrimitiveBlock k H)]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (Msys : ModularSystem ell K O k)
    (data : PrimitiveBlockData ell k K H)
    (navarro : ∀ (T : Type) [Group T] [Finite T]
      [HasEnoughRootsOfUnity K (Nat.card T)]
      (iota : PrimeRegularRootEmbedding ell k K T)
      (compatible : RootResidueCompatible Msys iota),
        ScopedDefectZeroReductionSource Msys iota compatible)
    (physical : GuardedBlockCompatibility (groupRoot Msys H)
      data.blockSource.operations)
    (coefficient : SpathCoefficientField ell k Msys.prime)
    (cover : EllPrimeCoverSource ell H)
    (odd : Odd ell)
    (source : CyclicDefectSplittingCertificate)
    (divides_simple_order : ell ∣ Nat.card cover.S)
    (cyclic : ∀ P : Subgroup H, IsPGroup ell P → IsCyclic P) :
    NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := TypeBExceptionalPrimitiveFamilySplitting.primitiveFamily
        Msys data navarro)
      Msys cover :=
  Classical.choice (source.allBlocks Msys data navarro physical coefficient
    cover odd divides_simple_order cyclic)

end ModularRep.PaperProofs.TypeBExceptionalCyclicSplittingSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
