import ModularRep.PaperProofs.TypeBCharacteristicTwoLinearCharacters
import ModularRep.PaperProofs.TypeBModularLinearCharacterLift
import ModularRep.PaperProofs.TypeCWeightTensorFieldAction

/-!
# A common trivial quotient twist in characteristic two

For an actual normal inclusion of index two, every modular linear character
trivial on the base is one. Its selected ordinary lift is the existing
prime-to-two root lift, and is also one on the whole ambient group.

The final deduction uses the actual Brauer tensor operation and ordinary
weight-class tensor operation. Fixedness under the same automorphism gives
both identities with one common modular character and its selected lift.
No constituent, covering pair, block equality or character triple is chosen.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrincipalCommonTrivialTwist

open ModularRep
open TypeBCharacteristicTwoLinearCharacters TypeBModularLinearCharacterLift

universe u

variable {k H : Type u} [Field k] [CharP k 2] [Group H] [Finite H]
  (G : Subgroup H) [G.Normal] (indexTwo : G.index = 2)

include indexTwo in
/-- Only the quotient coset is asserted to have order dividing two. -/
theorem square_mem (h : H) : h ^ 2 ∈ G := by
  simpa only [indexTwo] using G.pow_index_mem h

include indexTwo in
/-- The actual modular quotient-character subgroup is trivial. -/
theorem linearCharacter_eq_one
    (lambda : linearCharactersTrivialOn (k := k) G) : lambda = 1 := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro h
  apply unit_eq_one_of_square_eq_one
  rw [← map_pow]
  exact lambda.property (square_mem G indexTwo h)

include indexTwo in
/-- The canonical quotient identification gives the same statement on H/G. -/
theorem quotientLinearCharacter_eq_one (lambda : H ⧸ G →* kˣ) : lambda = 1 := by
  let e := LinearCharactersTrivialOn.quotientMulEquiv (k := k) G
  have trivial := linearCharacter_eq_one G indexTwo (e.symm lambda)
  calc
    lambda = e (e.symm lambda) := (e.apply_symm_apply lambda).symm
    _ = e 1 := congrArg e trivial
    _ = 1 := map_one e

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed k]
  (iota : PrimeRegularRootEmbedding 2 k K H)

/-- This is the existing whole-group ordinary lift, evaluated at one. -/
theorem selectedOrdinaryLift_one :
    quotientLift iota G (1 : linearCharactersTrivialOn (k := k) G) =
      (1 : H →* Kˣ) :=
  map_one (quotientLift iota G)

include indexTwo in
/-- Every quotient character has that same selected prime-to-two lift. -/
theorem selectedOrdinaryLift_eq_one
    (lambda : linearCharactersTrivialOn (k := k) G) :
    quotientLift iota G lambda = (1 : H →* Kˣ) := by
  rw [linearCharacter_eq_one G indexTwo lambda]
  exact selectedOrdinaryLift_one G iota

/-- The ordinary identity and modular identity agree under the prescribed root. -/
theorem trivialLift_regularCompatible :
    LinearCharacterReductionCompatible iota (1 : H →* Kˣ) (1 : H →* kˣ) := by
  have compatible := liftCharacter_regularCompatible iota (1 : H →* kˣ)
  change LinearCharacterReductionCompatible iota ((liftHom iota) 1) 1 at compatible
  simpa only [map_one] using compatible

/-- The selected lift is trivial on every actual radical subgroup. -/
def radicalLift (lambda : linearCharactersTrivialOn (k := k) G) :
    TypeCWeightTensorFieldAction.RadicalTensorCharacter (p := 2) (K := K) (G := H) :=
  ⟨quotientLift iota G lambda, by
    rw [selectedOrdinaryLift_eq_one G indexTwo iota lambda]
    exact (TypeCWeightTensorFieldAction.radicalTrivialLinearCharacters
      (p := 2) (K := K) (G := H)).one_mem⟩

@[simp]
theorem radicalLift_val (lambda : linearCharactersTrivialOn (k := k) G) :
    (radicalLift G indexTwo iota lambda).val = quotientLift iota G lambda := rfl

theorem radicalLift_eq_one (lambda : linearCharactersTrivialOn (k := k) G) :
    radicalLift G indexTwo iota lambda = 1 := by
  apply Subtype.ext
  exact selectedOrdinaryLift_eq_one G indexTwo iota lambda

include indexTwo in
/-- The existing tensor operation fixes the same function-valued Brauer character. -/
theorem brauer_twist_eq_self
    (productFormula : BrauerLinearTensorProductFormula iota)
    (lambda : linearCharactersTrivialOn (k := k) G) (Phi : IBr iota) :
    IrreducibleBrauerCharacter.linearTwist iota productFormula Phi lambda.val = Phi := by
  rw [linearCharacter_eq_one G indexTwo lambda]
  exact IrreducibleBrauerCharacter.linearTwist_one iota productFormula Phi

/-- Tensoring by the actual selected lift fixes the ordinary weight class. -/
theorem weightClass_twist_eq_self
    (lambda : linearCharactersTrivialOn (k := k) G)
    (v : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := H)) :
    TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
      (radicalLift G indexTwo iota lambda) v = v := by
  rw [radicalLift_eq_one]
  exact TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass_one v

/-- Fixed upper characters and weight classes use one common quotient twist.
The two fixedness premises concern the same displayed automorphism. -/
theorem commonTrivialTwist_of_fixed
    (productFormula : BrauerLinearTensorProductFormula iota)
    (alpha : MulAut H) (Phi : IBr iota)
    (v : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := H))
    (brauerFixed : IrreducibleBrauerCharacter.twist iota Phi alpha = Phi)
    (weightFixed : CharacterWeight.rightTwistConjugacyClass alpha v = v) :
    ∃ lambda : linearCharactersTrivialOn (k := k) G,
      lambda = 1 ∧ quotientLift iota G lambda = (1 : H →* Kˣ) ∧
        IrreducibleBrauerCharacter.twist iota Phi alpha =
          IrreducibleBrauerCharacter.linearTwist iota productFormula Phi lambda.val ∧
        TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
            (radicalLift G indexTwo iota lambda) v =
          CharacterWeight.rightTwistConjugacyClass alpha v := by
  refine ⟨1, rfl, selectedOrdinaryLift_one G iota, ?_, ?_⟩
  · exact brauerFixed.trans (brauer_twist_eq_self G indexTwo iota productFormula 1 Phi).symm
  · exact (weightClass_twist_eq_self G indexTwo iota 1 v).trans weightFixed.symm

end ModularRep.PaperProofs.TypeBPrincipalCommonTrivialTwist


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
