import ModularRep.BrauerLinearCharacterTensorAction
import ModularRep.KZeroLinearCharacterTensor

/-!
# Linear character tensoring and the decomposition map

This file proves that the exact decomposition homomorphism commutes with
tensoring by compatible ordinary and modular linear characters.  The proof
uses the character square and injectivity of the Brauer-character map.  It
does not assume decomposition naturality or an equivariant basic-set
bijection.
-/

noncomputable section

namespace ModularRep

open ExactGrothendieckGroup
open FDRepSimpleClassKZero

universe u

variable {p : ℕ} {K O k G : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- The Brauer-character homomorphism on exact `K₀` intertwines
linear character tensoring with pointwise multiplication. -/
theorem brauerCharacterKZero_linearCharacterTwist
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (lambda : G →* kˣ) :
    (brauerCharacterKZeroHom iota).comp
        (linearCharacterTwistKZero lambda) =
      (PrimeRegularClassFunction.leftMultiplyAddHom
        (iota.liftedLinearCharacter lambda)).comp
        (brauerCharacterKZeroHom iota) := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [AddMonoidHom.comp_apply, linearCharacterTwistKZero_classOf,
    brauerCharacterKZeroHom_classOf, AddMonoidHom.comp_apply,
    brauerCharacterKZeroHom_classOf]
  ext g
  exact congrFun (congrArg PrimeRegularClassFunction.toFun
    (productFormula V lambda)) g

/-- Compatibility of an ordinary linear character with a modular linear
character under the selected root embedding.  This is an equality of their
values on the prime regular elements. -/
def LinearCharacterReductionCompatible
    (iota : PrimeRegularRootEmbedding p k K G)
    (lambdaK : G →* Kˣ) (lambdak : G →* kˣ) : Prop :=
  PrimeRegularClassFunction.ofLinearCharacter p lambdaK =
    iota.liftedLinearCharacter lambdak

/-- The exact decomposition homomorphism commutes with tensoring by
compatible ordinary and modular linear characters. -/
theorem decompositionMapOfStableReduction_linearCharacterTwist
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (lambdaK : G →* Kˣ) (lambdak : G →* kˣ)
    (hlambda : LinearCharacterReductionCompatible iota lambdaK lambdak)
    (x : FDRepKZero K G) :
    decompositionMapOfStableReduction Msys iota hcompat
        (linearCharacterTwistKZero lambdaK x) =
      linearCharacterTwistKZero lambdak
        (decompositionMapOfStableReduction Msys iota hcompat x) := by
  apply brauerCharacterKZeroHom_injective iota
  have hsquare :=
    decompositionMapOfStableReduction_characterSquare Msys iota hcompat
  have hord := ordinaryCharacterKZero_linearCharacterTwist
    (p := p) lambdaK
  have hbrauer := brauerCharacterKZero_linearCharacterTwist
    iota productFormula lambdak
  calc
    brauerCharacterKZeroHom iota
        (decompositionMapOfStableReduction Msys iota hcompat
          (linearCharacterTwistKZero lambdaK x)) =
        ordinaryCharacterKZero p
          (linearCharacterTwistKZero lambdaK x) :=
      DFunLike.congr_fun hsquare
        (linearCharacterTwistKZero lambdaK x)
    _ = PrimeRegularClassFunction.leftMultiplyAddHom
          (PrimeRegularClassFunction.ofLinearCharacter p lambdaK)
          (ordinaryCharacterKZero p x) :=
      DFunLike.congr_fun hord x
    _ = PrimeRegularClassFunction.leftMultiplyAddHom
          (iota.liftedLinearCharacter lambdak)
          (ordinaryCharacterKZero p x) := by
      rw [hlambda]
    _ = PrimeRegularClassFunction.leftMultiplyAddHom
          (iota.liftedLinearCharacter lambdak)
          (brauerCharacterKZeroHom iota
            (decompositionMapOfStableReduction Msys iota hcompat x)) := by
      exact congrArg
        (PrimeRegularClassFunction.leftMultiplyAddHom
          (iota.liftedLinearCharacter lambdak))
        (DFunLike.congr_fun hsquare x).symm
    _ = brauerCharacterKZeroHom iota
          (linearCharacterTwistKZero lambdak
            (decompositionMapOfStableReduction Msys iota hcompat x)) :=
      (DFunLike.congr_fun hbrauer
        (decompositionMapOfStableReduction Msys iota hcompat x)).symm

/-- The decomposition map intertwines one combined tensor and automorphism
step.  This is the elementwise naturality statement underlying the
tensor-and-field semidirect action. -/
theorem decompositionMapOfStableReduction_linearCharacterTwist_twist
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (lambdaK : G →* Kˣ) (lambdak : G →* kˣ)
    (hlambda : LinearCharacterReductionCompatible iota lambdaK lambdak)
    (alpha : MulAut G) (x : FDRepKZero K G) :
    decompositionMapOfStableReduction Msys iota hcompat
        (linearCharacterTwistKZero lambdaK
          (twistKZero (k := K) alpha x)) =
      linearCharacterTwistKZero lambdak
        (twistKZero (k := k) alpha
          (decompositionMapOfStableReduction Msys iota hcompat x)) := by
  calc
    decompositionMapOfStableReduction Msys iota hcompat
        (linearCharacterTwistKZero lambdaK
          (twistKZero (k := K) alpha x)) =
        linearCharacterTwistKZero lambdak
          (decompositionMapOfStableReduction Msys iota hcompat
            (twistKZero (k := K) alpha x)) :=
      decompositionMapOfStableReduction_linearCharacterTwist
        Msys iota hcompat productFormula lambdaK lambdak hlambda
          (twistKZero (k := K) alpha x)
    _ = linearCharacterTwistKZero lambdak
          (twistKZero (k := k) alpha
            (decompositionMapOfStableReduction Msys iota hcompat x)) := by
      rw [decompositionMapOfStableReduction_twist]

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
