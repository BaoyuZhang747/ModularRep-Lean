/-!
# Logical core of the finite group reduction

This file checks the quantifier step used in Corollary 1.2.  The
representation theoretic reduction theorem and the two ways of proving the
inductive condition for a simple section remain explicit inputs.  What is
proved here is that it is enough to treat involved simple sections whose
orders are divisible by the modular prime by the three family theorems, and
to treat the remaining involved simple sections by the defect-zero result.
-/

namespace Formalisation

universe u v

/-- Abstract logical form of the last paragraph of the manuscript.  A simple
section whose order is divisible by the modular prime is assigned to one of
the covered families.  A section outside that prime support is handled by the
defect-zero argument.  These two branches verify the hypothesis of the
reduction theorem for every involved simple section. -/
theorem finiteGroupReduction_of_covered_sections
    {SimpleGroup : Type u} {Family : Type v}
    (Involved : SimpleGroup → Prop)
    (PrimeDividesOrder : SimpleGroup → Prop)
    (BelongsToFamily : SimpleGroup → Family → Prop)
    (InductiveBAW : SimpleGroup → Prop)
    (FamilyVerified : Family → Prop)
    (BlockwiseAWC : Prop)
    (covered : ∀ S, Involved S → PrimeDividesOrder S →
      ∃ family, BelongsToFamily S family)
    (familyTheorems : ∀ family, FamilyVerified family)
    (familySpecialisation : ∀ S family,
      BelongsToFamily S family → FamilyVerified family → InductiveBAW S)
    (defectZeroCase : ∀ S,
      Involved S → ¬ PrimeDividesOrder S → InductiveBAW S)
    (reductionTheorem : (∀ S, Involved S → InductiveBAW S) →
      BlockwiseAWC) :
    BlockwiseAWC := by
  apply reductionTheorem
  intro S hInvolved
  by_cases hPrime : PrimeDividesOrder S
  · obtain ⟨family, hFamily⟩ := covered S hInvolved hPrime
    exact familySpecialisation S family hFamily (familyTheorems family)
  · exact defectZeroCase S hInvolved hPrime

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
