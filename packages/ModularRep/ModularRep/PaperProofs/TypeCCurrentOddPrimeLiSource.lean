import ModularRep.PaperProofs.TypeCOddPrimeLiSourceApplication
import ModularRep.PaperProofs.TypeBExtensionClausesSplitting
import ModularRep.PaperProofs.TypeCCurrentWeightStabilizerTransport

/-!
# Li's standard subgroups and cyclic extensions over finite splitting fields

Li's Section 2.C and Lemma 5.5(1) provide the standard radical subgroup
family and the weight stabiliser factorisation for each weight's local character.
The certificate assumes this construction and factorisation over every coefficient
field of characteristic zero containing the roots required by the full semidirect
product. This interpretation is an external assumption of the formalisation.

The old whole-pair conjugation argument derives the global raw-normalizer
clause. The four extension clauses are separately constructed by the existing
finite-splitting cyclic-extension deductions on the actual inertia quotients.
Neither a downstairs character matching nor an iBAW conclusion is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeCCurrentOddPrimeLiSource

open ModularRep TypeBCriterionHypotheses
open TypeCOddPrimeConformalCriterionCarriers
open TypeCOddPrimeLiSourceApplication
open TypeBLocalOrdinaryExtensionSplitting
open TypeBLocalOrdinaryGeometry
open OddTwoConformalProjectiveRealisation (CSp)

/-- The same one-way standard-family implication in its finite-splitting
ordinary coefficient interpretation. The source chooses actual subgroups;
its conclusion does not assert the global raw-normalizer clause. -/
structure Li55SplittingCertificate : Prop where
  normalForms : ∀ (n : ℕ) (F : Type) [Field F] [Finite F]
      [(SpSubgroup n F).Normal] (ell : ℕ) (K : Type)
      [Field K] [CharZero K]
      [HasEnoughRootsOfUnity K (Nat.card (Ambient (fieldAction n F)))],
    3 ≤ n → Odd (Nat.card F) → Nat.Prime ell → Odd ell →
      ¬ ell ∣ Nat.card F → Nonempty (StandardFamily n F ell K)

variable (n : ℕ) (F : Type) [Field F] [Finite F]
variable [(SpSubgroup n F).Normal]
variable {ell : ℕ} {k K : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [HasEnoughRootsOfUnity K (Nat.card (Ambient (fieldAction n F)))]

/-- Choose the published family only after all numerical hypotheses are fixed. -/
def standardFamily (source : Li55SplittingCertificate)
    (structural : StructuralSource n F) (prime : Nat.Prime ell)
    (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F) :
    StandardFamily n F ell K :=
  Classical.choice (source.normalForms n F ell K structural.rank
    structural.field_odd prime odd nondefining)

/-- Whole-pair conjugation retains each weight's own quotient character. -/
theorem rawNormalizerClause (source : Li55SplittingCertificate)
    (structural : StructuralSource n F) (prime : Nat.Prime ell)
    (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F) :
    RawNormalizerClause (ell := ell) (K := K)
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) := by
  let family := standardFamily n F (K := K) source structural prime odd nondefining
  refine TypeCCurrentWeightStabilizerTransport.rawNormalizerClause_of_standard_subgroups
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F)
    (fun R : {R : Subgroup (SpSubgroup n F) // R ∈ family.representatives} => R.1) ?_ ?_
  · intro Q hQ
    obtain ⟨R, hR, g, hg⟩ := family.conjugacyCoverage Q hQ
    exact ⟨⟨R, hR⟩, g, hg⟩
  · intro R W hW
    exact family.formula R.1 R.2 W hW

/-- The original four literal extension clauses, using the finite roots of
the full ambient group for both actual local inertia quotients. -/
theorem extensionClauses
    (iota : PrimeRegularRootEmbedding ell k K (SpSubgroup n F))
    (structural : StructuralSource n F)
    (brauer : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (ordinaryM : ∀ W : CharacterWeight ell K (SpSubgroup n F),
      letI := TypeBExtensionClausesSplitting.mRoots
        (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
      ScopedCyclicExtensionSource K
        (Inertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
          (embeddedM (fieldAction n F)) ⧸
        RadicalInInertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
          (embeddedM (fieldAction n F))))
    (ordinaryGE : ∀ W : CharacterWeight ell K (SpSubgroup n F),
      letI := TypeBExtensionClausesSplitting.geRoots
        (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
      ScopedCyclicExtensionSource K
        (Inertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
          (baseFieldGroup (SpSubgroup n F) (fieldAction n F)) ⧸
        RadicalInInertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
          (baseFieldGroup (SpSubgroup n F) (fieldAction n F)))) :
    ExtensionClauses (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iota := by
  letI := structural.field_cyclic
  exact TypeBExtensionClausesSplitting.extensionClauses
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iota
    brauer structural.quotient_cyclic ordinaryM ordinaryGE

end ModularRep.PaperProofs.TypeCCurrentOddPrimeLiSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
