import ModularRep.PaperProofs.TypeBQ3PrincipalRadicalDecoding

/-! The radical and local character deductions for an arbitrary fixed block.
Only the graph of the same matching is used; no principality or extension
assertion enters these deductions. The final consumer supplies this graph
from its constructed stabilizer-equivariant matching. -/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3FaithfulRadicalCovariance

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalRadicalDecoding

variable {k K Y : Type} [Field k] [Field K] [CharZero K]
  [Group Y] [Finite Y] [CharP k 2] [IsAlgClosed k]

local instance groupFintype : Fintype Y := Fintype.ofFinite Y

variable {root : PrimeRegularRootEmbedding 2 k K Y}
  {S : CoverWeightSource (k := k) (K := K) Y}
  {b : LiteralPrimitiveBlock k Y}
  (omega : BrauerFibre root b ≃ CoverWeight S b)

theorem part_of_class_transport (alpha : (MulAut Y)ᵐᵒᵖ)
    (phi psi : BrauerFibre root b)
    (graph : (omega psi).val = alpha • (omega phi).val) :
    part omega psi = alpha • part omega phi := by
  unfold part
  rw [graph]
  exact radicalClass_equivariant alpha (omega phi).val

theorem localMap_of_class_transport (alpha : (MulAut Y)ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := 2) (G := Y))
    (phi : BrauerAtRadical omega Q)
    (psi : BrauerAtRadical omega (Q.rightTwist alpha.unop))
    (graph : (omega psi.val).val = alpha • (omega phi.val).val) :
    (localMap omega (Q.rightTwist alpha.unop) psi).val =
      localCharacterTwist Q alpha (localMap omega Q phi).val := by
  apply (localDefectZeroEquivWeightRadicalFibre Nat.prime_two
    (Q.rightTwist alpha.unop)).injective
  apply Subtype.ext
  rw [localDefectZeroEquivWeightRadicalFibre_apply_val,
    localDefectZeroEquivWeightRadicalFibre_apply_val]
  change (Quotient.mk'' (Quotient.mk''
      (characterWeightAt Nat.prime_two (Q.rightTwist alpha.unop)
        (localMap omega (Q.rightTwist alpha.unop) psi).val)) :
        CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Y)) =
    alpha • (Quotient.mk'' (Quotient.mk''
      (characterWeightAt Nat.prime_two Q (localMap omega Q phi).val)) :
        CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Y))
  rw [localMap_class, localMap_class]
  exact graph

theorem localMap_raw_of_class_transport (alpha : (MulAut Y)ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := 2) (G := Y))
    (phi : BrauerAtRadical omega Q)
    (psi : BrauerAtRadical omega (Q.rightTwist alpha.unop))
    (graph : (omega psi.val).val = alpha • (omega phi.val).val) :
    CharacterWeight.Isomorphic
      ((characterWeightAt Nat.prime_two Q (localMap omega Q phi).val).rightTwist alpha.unop)
      (characterWeightAt Nat.prime_two (Q.rightTwist alpha.unop)
        (localMap omega (Q.rightTwist alpha.unop) psi).val) := by
  rw [localMap_of_class_transport omega alpha Q phi psi graph]
  exact ⟨rfl, rfl⟩

end ModularRep.PaperProofs.TypeBQ3FaithfulRadicalCovariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
