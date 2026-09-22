import ModularRep.PaperProofs.TypeBSpinHallJGInstantiation
import ModularRep.PaperProofs.TypeBLocalOrdinaryExtensionSplitting
import ModularRep.PaperProofs.TypeBGlobalExtensionBinding

/-!
# The four cyclic extension clauses on the same actual Spin carriers

The root and natural action below are the existing constructions from the
same modular system, ordinary choice and Clifford norm. The norm kernel
makes the actual special-Clifford/Spin quotient cyclic.

Navarro (8.12), p. 163, supplies the modular cyclic extension principle on
the algebraically closed residue field. The ordinary source is the fixed
finite group Isaacs/Serre theorem with the sufficient-root guard INSIDE
its quantifier. It supplies no Type B extension record.

A single sufficient-root assumption for the actual ambient group supplies
every local inertia-quotient root guard by the checked order divisibility.
All four clauses then follow from the actual inclusion, invariance and
quotient-embedding deductions. No matching or stabilizer factorization
is needed for this all-character and all-weight extension statement.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinExtensionInstantiation

open ModularRep TypeBCliffordCarriers TypeBCriterionHypotheses
open TypeBCriterionCarrierBindings TypeBLocalOrdinaryExtensionSplitting

variable {n p f ell : ℕ} [NeZero f] {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k]
  [Algebra O K] [CharP k ell] [IsAlgClosed k]
  {parameters : OddFieldParameters F p f}

/-- All extension clauses on the canonical Spin root, with one explicitly
sufficient ordinary coefficient guard for the actual ambient group. -/
theorem extensionClauses_modular_instantiated
    (N : NormSource n F) (fs : FieldActionSource n F p f parameters N)
    (Msys : ModularSystem ell K O k)
    (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)
    [HasEnoughRootsOfUnity K (Nat.card (Ambient fs.action))]
    (brauerSource : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (ordinarySource : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)], ScopedCyclicExtensionSource K H) :
    ExtensionClauses (SpinSubgroup n F N) fs.action (naturalAction N fs)
      (TypeBFLZModularRootBinding.spinRoot Msys choice N) := by
  let iota := TypeBFLZModularRootBinding.spinRoot Msys choice N
  have cyclic := TypeBSpinHallJGInstantiation.normQuotient_cyclic N
  refine {
    brauer_M := ?_
    brauer_GE := ?_
    ordinary_M := ?_
    ordinary_GE := ?_ }
  · intro phi
    exact ⟨TypeBGlobalExtensionBinding.brauer_M (SpinSubgroup n F N)
      fs.action (naturalAction N fs) iota phi brauerSource cyclic⟩
  · intro phi
    exact ⟨TypeBGlobalExtensionBinding.brauer_GE (SpinSubgroup n F N)
      fs.action (naturalAction N fs) iota phi brauerSource⟩
  · intro W
    letI := localRoots_of_ambientRoots (SpinSubgroup n F N)
      fs.action (naturalAction N fs) W (embeddedM fs.action)
    exact TypeBLocalOrdinaryExtensionSplitting.ordinary_M (SpinSubgroup n F N)
      fs.action (naturalAction N fs) W (ordinarySource _) cyclic
  · intro W
    letI := localRoots_of_ambientRoots (SpinSubgroup n F N)
      fs.action (naturalAction N fs) W (baseFieldGroup (SpinSubgroup n F N) fs.action)
    exact TypeBLocalOrdinaryExtensionSplitting.ordinary_GE (SpinSubgroup n F N)
      fs.action (naturalAction N fs) W (ordinarySource _)

end ModularRep.PaperProofs.TypeBSpinExtensionInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
