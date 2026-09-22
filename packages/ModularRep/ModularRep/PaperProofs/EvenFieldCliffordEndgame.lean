import Mathlib

/-!
# Paper proof: the Clifford--Gallagher--induction endgame

This file isolates the final character-theoretic deduction in the generic
weight half of manuscript Lemma 3.6.  It deliberately assumes only the exact
equations supplied by Clifford correspondence, Gallagher factorisation, an
invariant extension, triviality on the relative quotient, and naturality of
the two operations.  Neither fixation conclusion is an input.
-/

namespace ModularRep.PaperProofs.EvenFieldCliffordEndgame

universe uE uQ uC uW

/-- Source-shaped data for one chosen generic-weight representative and one
chosen inner-twisted field automorphism.

`gallagherFactorisation` and `cliffordInduction` place the chosen characters
in the relevant Gallagher and Clifford fibres.  Equivariance preserves each
relation, and uniqueness within the fibre supplies the equalities used in the
proof.  No multiplication or induction map is postulated on characters
outside the relevant fibres. -/
structure Data
    (ExtensionCharacter QuotientCharacter Correspondent
      WeightRepresentative : Type*)
    (extensionAction : ExtensionCharacter → ExtensionCharacter)
    (quotientAction : QuotientCharacter → QuotientCharacter)
    (correspondentAction : Correspondent → Correspondent)
    (weightAction : WeightRepresentative → WeightRepresentative)
    (Multiplies : ExtensionCharacter → QuotientCharacter →
      Correspondent → Prop)
    (Induces : Correspondent → WeightRepresentative → Prop)
    (kappa : Correspondent) (weight : WeightRepresentative) where
  extension : ExtensionCharacter
  quotientCharacter : QuotientCharacter
  gallagherFactorisation :
    Multiplies extension quotientCharacter kappa
  extensionFixed : extensionAction extension = extension
  quotientCharacterFixed :
    quotientAction quotientCharacter = quotientCharacter
  multiplicationEquivariant : ∀ extension quotientCharacter correspondent,
    Multiplies extension quotientCharacter correspondent →
      Multiplies (extensionAction extension)
        (quotientAction quotientCharacter) (correspondentAction correspondent)
  multiplicationUnique : ∀ extension quotientCharacter correspondent₁ correspondent₂,
    Multiplies extension quotientCharacter correspondent₁ →
      Multiplies extension quotientCharacter correspondent₂ →
        correspondent₁ = correspondent₂
  cliffordInduction : Induces kappa weight
  inductionEquivariant : ∀ correspondent representative,
    Induces correspondent representative →
      Induces (correspondentAction correspondent)
        (weightAction representative)
  inductionUnique : ∀ correspondent representative₁ representative₂,
    Induces correspondent representative₁ →
      Induces correspondent representative₂ →
        representative₁ = representative₂

variable
    {ExtensionCharacter : Type uE}
    {QuotientCharacter : Type uQ}
    {Correspondent : Type uC}
    {WeightRepresentative : Type uW}
    {extensionAction : ExtensionCharacter → ExtensionCharacter}
    {quotientAction : QuotientCharacter → QuotientCharacter}
    {correspondentAction : Correspondent → Correspondent}
    {weightAction : WeightRepresentative → WeightRepresentative}
    {Multiplies : ExtensionCharacter → QuotientCharacter →
      Correspondent → Prop}
    {Induces : Correspondent → WeightRepresentative → Prop}
    {kappa : Correspondent}
    {weight : WeightRepresentative}

/-- Gallagher factorisation and naturality fix the chosen Clifford
correspondent. -/
theorem correspondent_fixed
    (D : Data ExtensionCharacter QuotientCharacter Correspondent
      WeightRepresentative extensionAction quotientAction correspondentAction
      weightAction Multiplies Induces kappa weight) :
    correspondentAction kappa = kappa := by
  have transformed := D.multiplicationEquivariant
    D.extension D.quotientCharacter kappa D.gallagherFactorisation
  rw [D.extensionFixed, D.quotientCharacterFixed] at transformed
  exact D.multiplicationUnique D.extension D.quotientCharacter
    (correspondentAction kappa) kappa transformed D.gallagherFactorisation

/-- The manuscript's exact final deduction: the Clifford correspondent is
fixed, and equivariance of induction then fixes the chosen generic-weight
representative under the inner-twisted field automorphism. -/
theorem cliffordGallagherInduction_fixed
    (D : Data ExtensionCharacter QuotientCharacter Correspondent
      WeightRepresentative extensionAction quotientAction correspondentAction
      weightAction Multiplies Induces kappa weight) :
    correspondentAction kappa = kappa ∧ weightAction weight = weight := by
  have hkappa := correspondent_fixed D
  refine ⟨hkappa, ?_⟩
  have transformed := D.inductionEquivariant kappa weight D.cliffordInduction
  rw [hkappa] at transformed
  exact D.inductionUnique kappa (weightAction weight) weight
    transformed D.cliffordInduction

end ModularRep.PaperProofs.EvenFieldCliffordEndgame


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
