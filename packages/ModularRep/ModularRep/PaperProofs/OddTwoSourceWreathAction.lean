import Mathlib.GroupTheory.RegularWreathProduct
import ModularRep.PaperProofs.OddTwoQuaternionFactor

/-!
# The source permutation group in the corrected odd characteristic factor

Feng--Yu--Zhang write `A_c` for the elementary abelian group of order
`2^c` in its left regular representation and, for
`c = (c_t, ..., c_1)`, set

`A_c = A_{c_1} wr A_{c_2} wr ... wr A_{c_t}`.

This file gives that description a literal Lean type and faithful
permutation representation.  The list is stored in the source order
`[c_t, ..., c_1]`, so recursion adds the outermost regular wreath factor.
The construction removes the previously arbitrary permutation homomorphism
from the corrected-factor endpoint.  Identifying a named subgroup in the
classification with the resulting ambient image remains a source-level
input; no such equality is postulated here.
-/

namespace ModularRep.PaperProofs.OddTwoSourceWreathAction

open OddTwoCorrectedFactorAdapter
open OddTwoQuaternionFactor

/-- The elementary abelian group of order `2^c`, written multiplicatively. -/
abbrev ElementaryAbelianTwo (c : ℕ) := Multiplicative (Fin c → ZMod 2)

/-- The iterated regular wreath product in the source order
`[c_t, ..., c_1]`. -/
def SourceWreathGroup : List ℕ → Type
  | [] => PUnit
  | [c] => ElementaryAbelianTwo c
  | c :: d :: cs =>
      RegularWreathProduct (SourceWreathGroup (d :: cs)) (ElementaryAbelianTwo c)

instance sourceWreathGroupGroup (cs : List ℕ) : Group (SourceWreathGroup cs) := by
  induction cs with
  | nil =>
      simp only [SourceWreathGroup]
      infer_instance
  | cons c cs ih =>
      cases cs with
      | nil =>
          simp only [SourceWreathGroup]
          infer_instance
      | cons d ds =>
          simp only [SourceWreathGroup]
          infer_instance

/-- The point set of the natural iterated imprimitive action. -/
def SourceWreathPoints : List ℕ → Type
  | [] => PUnit
  | [c] => ElementaryAbelianTwo c
  | c :: d :: cs => SourceWreathPoints (d :: cs) × ElementaryAbelianTwo c

instance sourceWreathPointsNonempty (cs : List ℕ) : Nonempty (SourceWreathPoints cs) := by
  induction cs with
  | nil =>
      simp only [SourceWreathPoints]
      infer_instance
  | cons c cs ih =>
      cases cs with
      | nil =>
          simp only [SourceWreathPoints]
          infer_instance
      | cons d ds =>
          simp only [SourceWreathPoints]
          infer_instance

instance sourceWreathPointsFinite (cs : List ℕ) : Finite (SourceWreathPoints cs) := by
  induction cs with
  | nil =>
      simp only [SourceWreathPoints]
      infer_instance
  | cons c cs ih =>
      cases cs with
      | nil =>
          simp only [SourceWreathPoints]
          infer_instance
      | cons d ds =>
          simp only [SourceWreathPoints]
          infer_instance

/-- The faithful permutation representation of the source iterated wreath
product.  At each stage `RegularWreathProduct.toPerm` uses the left regular
action of the new elementary abelian outer factor. -/
def sourceWreathAction :
    (cs : List ℕ) → SourceWreathGroup cs →* Equiv.Perm (SourceWreathPoints cs)
  | [] => 1
  | [c] => MulAction.toPermHom (ElementaryAbelianTwo c) (ElementaryAbelianTwo c)
  | c :: d :: cs => by
      let _ := MulAction.compHom
        (SourceWreathPoints (d :: cs)) (sourceWreathAction (d :: cs))
      exact RegularWreathProduct.toPerm
        (SourceWreathGroup (d :: cs)) (ElementaryAbelianTwo c)
          (SourceWreathPoints (d :: cs))

theorem sourceWreathAction_injective :
    (cs : List ℕ) → Function.Injective (sourceWreathAction cs)
  | [] => by
      intro x y _
      cases x
      cases y
      rfl
  | [c] => by
      change Function.Injective
        (MulAction.toPermHom (ElementaryAbelianTwo c) (ElementaryAbelianTwo c))
      exact MulAction.toPerm_injective
  | c :: d :: cs => by
      let _ := MulAction.compHom
        (SourceWreathPoints (d :: cs)) (sourceWreathAction (d :: cs))
      have hfaithful :
          FaithfulSMul (SourceWreathGroup (d :: cs))
            (SourceWreathPoints (d :: cs)) :=
        ⟨fun h => sourceWreathAction_injective (d :: cs) (Equiv.ext h)⟩
      exact RegularWreathProduct.toPermInj
        (SourceWreathGroup (d :: cs)) (ElementaryAbelianTwo c)
          (SourceWreathPoints (d :: cs))

section SourceEndpoint

universe u v w

variable {F : Type u} [Field F]
variable {I : Type v} {K G : Type w}
variable [Fintype I] [DecidableEq I]
variable [Group K] [Group G]

/-- A source-shaped exclusion endpoint with an explicit quaternion choice.

The field characteristic supplies the faithful quaternion factor, while
`cs` supplies the exact iterated regular wreath action.  The remaining
premises are the routine left orthogonal reflection and the genuinely
source-specific ambient realisation and principal-centre statement.  The
equality `hR` must in particular identify the chosen quaternion image with
the required source conjugacy class.  The later ambient endpoint avoids
building that identification into an equality by parameterising the right
factor and working up to conjugacy. -/
theorem source_wreath_quaternion_factor_and_exclusion
    (p : ℕ) [NeZero p] [CharP F p] (hp : ¬ p ∣ 2)
    (cs : List ℕ)
    (JI : Matrix I I F)
    (C : Subgroup K)
    (f :
      (CorrectedWreathGroup JI (omega (F := F)) (sourceWreathAction cs) × K) →* G)
    (hf : Function.Injective f)
    (t : FormIsometryGroup JI) (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ a : F,
      (↑t.1 : Matrix I I F) ≠ a • (1 : Matrix I I F))
    (Rsource : Subgroup G)
    (hR : Rsource = correctedAmbientSubgroup JI (omega (F := F))
      (sourceWreathAction cs) (canonicalQuaternionSubgroup (F := F) p) C f)
    (IsPrincipalWeight : Prop)
    (principalCentreSylow : IsPrincipalWeight →
      ∃ P : Sylow 2 (Subgroup.centralizer (Rsource : Set G)),
        (P : Subgroup (Subgroup.centralizer (Rsource : Set G))) =
          OddTwoWreathReflection.centreInCentralizer Rsource) :
    Nonempty
        (QuaternionGroup 2 ≃* canonicalQuaternionSubgroup (F := F) p) ∧
      ¬ IsPrincipalWeight := by
  let a := canonicalQuaternionParameterA (F := F) p
  let b := canonicalQuaternionParameterB (F := F) p
  let hab := canonicalQuaternionParameters_spec (F := F) p
  have hTwo : (2 : F) ≠ 0 := two_ne_zero_of_charP p hp
  exact source_identified_quaternion_factor_and_exclusion
    a b hab hTwo JI (sourceWreathAction cs) C f hf t htSq htNonscalar
      Rsource hR IsPrincipalWeight principalCentreSylow

/-- The exclusion-only form of
`source_wreath_quaternion_factor_and_exclusion`. -/
theorem source_wreath_quaternion_factor_not_principal
    (p : ℕ) [NeZero p] [CharP F p] (hp : ¬ p ∣ 2)
    (cs : List ℕ)
    (JI : Matrix I I F)
    (C : Subgroup K)
    (f :
      (CorrectedWreathGroup JI (omega (F := F)) (sourceWreathAction cs) × K) →* G)
    (hf : Function.Injective f)
    (t : FormIsometryGroup JI) (htSq : t ^ 2 = 1)
    (htNonscalar : ∀ a : F,
      (↑t.1 : Matrix I I F) ≠ a • (1 : Matrix I I F))
    (Rsource : Subgroup G)
    (hR : Rsource = correctedAmbientSubgroup JI (omega (F := F))
      (sourceWreathAction cs) (canonicalQuaternionSubgroup (F := F) p) C f)
    (IsPrincipalWeight : Prop)
    (principalCentreSylow : IsPrincipalWeight →
      ∃ P : Sylow 2 (Subgroup.centralizer (Rsource : Set G)),
        (P : Subgroup (Subgroup.centralizer (Rsource : Set G))) =
          OddTwoWreathReflection.centreInCentralizer Rsource) :
    ¬ IsPrincipalWeight :=
  (source_wreath_quaternion_factor_and_exclusion
    p hp cs JI C f hf t htSq htNonscalar Rsource hR IsPrincipalWeight
      principalCentreSylow).2

end SourceEndpoint

end ModularRep.PaperProofs.OddTwoSourceWreathAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
