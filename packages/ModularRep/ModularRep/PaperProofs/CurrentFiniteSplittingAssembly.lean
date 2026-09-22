import ModularRep.PaperProofs.CurrentFiniteSplittingFamily
import ModularRep.PaperProofs.TypeBFullCriterionSplittingSource

/-!
# Complete block-family construction in a splitting modular system

Koshitani--Spath, Definition 3.2 and Lemma 3.3, together with Spath's
Definition 5.17 and Remark 5.18, supply the blockwise-to-global implication.
This interface uses a complete discrete valuation modular system and a
splitting field for the actual finite base group. It does not require its
fraction field to be algebraically closed.

The input contains complete independently established block witnesses.
The output may choose fresh compatible maps and extension data, with
the ambient Brauer roots in the same residue convention. Prime regular
roots for every finite auxiliary group are given by the existing modular
system construction. This is an exact E2 source boundary, not a proof of
the cited family-normalisation theorem or of its hypotheses.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.CurrentFiniteSplittingAssembly

open ModularRep CharacterWeight
open CyclicOuterLemma37LiteralLocalExtension EvenFieldFLZSourceConditions
open EvenFieldFLZDefinition35Family TypeBFixedRootDefinitionFamily
open TypeBFullBlockCondition TypeBFullCriterionSplittingSource

/-- The published implication with finite splitting, fixed specified block
operations and one actual modular system. No old matching is required to
equal the fresh globally compatible matching. -/
structure Source : Prop where
  allBlocks : ∀ {ell : ℕ} (family : Definition35Family.{0} ell)
      (cover : EllPrimeCoverSource ell family.H)
      (O : Type) [CommRing O] [IsDomain O] [Algebra O family.K]
      (Msys : ModularSystem ell family.K O family.k),
    HasEnoughRootsOfUnity family.K (Nat.card family.H) →
    family.iota = TypeBModularGroupRootBinding.groupRoot Msys family.H →
    SpathCoefficientField ell family.k family.ellPrime →
    (∀ b, family.blockSource.operations.ambientBlockData.blockIdempotent b =
      family.blockIdempotent b) →
    GuardedBlockCompatibility family.iota family.blockSource.operations →
    (∀ b w, QuotientRootAgreement family.iota
      (SelectedRadical family.blockSource b w) (family.localReduction b w).iota) →
    (∀ b, Nonempty (BlockWitness family cover b)) →
      Nonempty (NormalizedFamilyWitness (family := family) Msys cover)

variable {ell : ℕ} (family : Definition35Family.{0} ell)
  (cover : EllPrimeCoverSource ell family.H)
  {O : Type} [CommRing O] [IsDomain O] [Algebra O family.K]
  (Msys : ModularSystem ell family.K O family.k)

/-- Forget only the extra normalization field after the published construction.
The exact complete family and cover remain unchanged. -/
theorem fullFamily (source : Source)
    (ordinaryRoots : HasEnoughRootsOfUnity family.K (Nat.card family.H))
    (root : family.iota = TypeBModularGroupRootBinding.groupRoot Msys family.H)
    (coefficient : SpathCoefficientField ell family.k family.ellPrime)
    (idempotent : ∀ b, family.blockSource.operations.ambientBlockData.blockIdempotent b =
      family.blockIdempotent b)
    (physical : GuardedBlockCompatibility family.iota family.blockSource.operations)
    (roots : ∀ b w, QuotientRootAgreement family.iota
      (SelectedRadical family.blockSource b w) (family.localReduction b w).iota)
    (blocks : ∀ b, Nonempty (BlockWitness family cover b)) :
    Nonempty (FamilyWitness family cover) := by
  obtain ⟨witness⟩ := source.allBlocks family cover O Msys ordinaryRoots root
    coefficient idempotent physical roots blocks
  exact ⟨witness.full⟩

end ModularRep.PaperProofs.CurrentFiniteSplittingAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
