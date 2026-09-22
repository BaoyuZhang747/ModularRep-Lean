import ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding
import Mathlib.Algebra.Field.ZMod

/-!
# The principal Brauer action on actual Omega over ZMod 3

The finite simple-table labels are realized as function-valued irreducible
Brauer characters in the prescribed root convention. Injectivity, complete
principal support, and the action of the same actual SO element are separate
source fields. Their table, character, block, and action authentication
remains E3/U.

The fibre map and its inverse are constructed from those fields. Transport
of fixed points then gives the already checked twelve-point, eight-fixed
signature on the complete supported specified principal fibre. No weight
character or correspondence is selected in this module.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalBrauerBinding

open ModularRep
open TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalCountBinding
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

/-- The table dictionary on the complete actual principal Brauer fibre.
The chosen SO element is outside Omega; its action is the existing specified
permutation, not an independently supplied permutation of actual characters. -/
structure LiteralSource
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
    (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
    (delta : H (ZMod 3)) (indexTwo : (G (ZMod 3)).index = 2)
    (outside : delta ∉ G (ZMod 3)) where
  character : SimplePrincipalBrauerLabel → IBr root
  character_injective : Function.Injective character
  supported : ∀ label, Supported root b (character label)
  complete : ∀ phi : OmegaBrauer (ZMod 3) root b,
    ∃ label, character label = phi.val
  actual_action : ∀ label,
    character (simplePrincipalOuterAction label) =
      (brauerPermutation (ZMod 3) S literal root b hb delta indexTwo
        ⟨character label, supported label⟩).val

variable
  (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (root : PrimeRegularRootEmbedding 2 k K (G (ZMod 3)))
  (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
  (delta : H (ZMod 3)) (indexTwo : (G (ZMod 3)).index = 2)
  (outside : delta ∉ G (ZMod 3))
  (D : LiteralSource S literal root b hb delta indexTwo outside)

/-- Restrict the literal character map to its proved specified support. -/
def labelToFibre (label : SimplePrincipalBrauerLabel) :
    OmegaBrauer (ZMod 3) root b :=
  ⟨D.character label, D.supported label⟩

theorem labelToFibre_injective :
    Function.Injective (labelToFibre S literal root b hb delta indexTwo outside D) := by
  intro left right h
  exact D.character_injective (congrArg Subtype.val h)

theorem labelToFibre_surjective :
    Function.Surjective (labelToFibre S literal root b hb delta indexTwo outside D) := by
  intro phi
  obtain ⟨label, hlabel⟩ := D.complete phi
  exact ⟨label, Subtype.ext hlabel⟩

/-- All actual supported principal characters occur in the constructed map. -/
def labelEquiv : SimplePrincipalBrauerLabel ≃ OmegaBrauer (ZMod 3) root b :=
  Equiv.ofBijective (labelToFibre S literal root b hb delta indexTwo outside D)
    ⟨labelToFibre_injective S literal root b hb delta indexTwo outside D,
      labelToFibre_surjective S literal root b hb delta indexTwo outside D⟩

@[simp] theorem labelEquiv_val (label : SimplePrincipalBrauerLabel) :
    (labelEquiv S literal root b hb delta indexTwo outside D label).val =
      D.character label := rfl

/-- The resulting fibre equivalence uses the same actual SO actor. -/
theorem labelEquiv_intertwines (label : SimplePrincipalBrauerLabel) :
    labelEquiv S literal root b hb delta indexTwo outside D
        (simplePrincipalOuterAction label) =
      brauerPermutation (ZMod 3) S literal root b hb delta indexTwo
        (labelEquiv S literal root b hb delta indexTwo outside D label) := by
  apply Subtype.ext
  exact D.actual_action label

/-- The action equality identifies the entire fixed-point fibres. -/
def fixedPointEquiv :
    Function.fixedPoints simplePrincipalOuterAction ≃
      Function.fixedPoints
        (brauerPermutation (ZMod 3) S literal root b hb delta indexTwo) :=
  Equiv.subtypeEquiv (labelEquiv S literal root b hb delta indexTwo outside D)
    fun label => by
      change simplePrincipalOuterAction label = label ↔
        brauerPermutation (ZMod 3) S literal root b hb delta indexTwo
            (labelEquiv S literal root b hb delta indexTwo outside D label) =
          labelEquiv S literal root b hb delta indexTwo outside D label
      rw [← labelEquiv_intertwines S literal root b hb delta indexTwo outside D label]
      constructor
      · intro h
        exact congrArg (labelEquiv S literal root b hb delta indexTwo outside D) h
      · intro h
        exact (labelEquiv S literal root b hb delta indexTwo outside D).injective h

variable [Fintype (OmegaBrauer (ZMod 3) root b)]
  [DecidableEq (OmegaBrauer (ZMod 3) root b)]

include D in
/-- The finite simple-table signature now holds on the complete specified
principal fibre and the existing actual conjugation permutation. -/
theorem principalBrauer_action_signature :
    (Fintype.card (OmegaBrauer (ZMod 3) root b),
      Fintype.card (Function.fixedPoints
        (brauerPermutation (ZMod 3) S literal root b hb delta indexTwo))) = (12, 8) := by
  have signature := simplePrincipal_action_signature
  apply Prod.ext
  · exact (Fintype.card_congr
      (labelEquiv S literal root b hb delta indexTwo outside D)).symm.trans
        (congrArg Prod.fst signature)
  · exact (Fintype.card_congr
      (fixedPointEquiv S literal root b hb delta indexTwo outside D)).symm.trans
        (congrArg Prod.snd signature)

end ModularRep.PaperProofs.TypeBQ3PrincipalBrauerBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
