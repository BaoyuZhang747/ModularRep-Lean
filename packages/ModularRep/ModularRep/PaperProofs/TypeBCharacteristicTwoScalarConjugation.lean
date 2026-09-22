import ModularRep.PaperProofs.TypeBLemma47LeviApplication

/-!
# Quotient scalars commute with the literal inertia conjugation action

Commutativity of the actual quotient Gamma/N makes each inertia
conjugation trivial on I/(N intersect I).  A modular linear character
trivial on that literal subgroup therefore has unchanged values.  The
checked tensor/pullback formula then gives the action-commutation field
required by the characteristic-two Gallagher adapter.

No arbitrary quotient action, scalar invariance, character fixedness, or
Gallagher correspondence is an input.  The tensor formula is the existing
exact one-dimensional Brauer tensor source; its naturality is already K.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoScalarConjugation

open TypeBCharacteristicTwoCliffordKernel
open TypeBCharacteristicTwoCliffordApplication
open TypeBLemma47LeviApplication
open scoped IsMulCommutative

universe u

section QuotientConjugation

variable {Gamma : Type u} [Group Gamma]
variable (N : Subgroup Gamma) [N.Normal] [IsMulCommutative (Gamma ⧸ N)]

/-- Conjugation is literally trivial in the specified abelian quotient. -/
theorem quotient_conjugation_eq (a x : Gamma) :
    QuotientGroup.mk' N (a * x * a⁻¹) = QuotientGroup.mk' N x := by
  rw [map_mul, map_mul, map_inv]
  rw [mul_comm (QuotientGroup.mk' N a) (QuotientGroup.mk' N x)]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem conjugation_difference_mem (a x : Gamma) :
    x⁻¹ * (a * x * a⁻¹) ∈ N := by
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N (x⁻¹ * (a * x * a⁻¹)) = 1
  rw [map_mul, map_inv, quotient_conjugation_eq, inv_mul_cancel]

variable {k I : Type u} [Field k] [Group I]

/-- The value proof applies to any literal subgroup embedding and its
actual conjugation square.  It requires no character-theoretic source. -/
theorem linearCharacter_comp_eq_of_conjugation
    (inclusion : I →* Gamma) (a : Gamma) (alpha : MulAut I)
    (value : ∀ x : I, inclusion (alpha x) = a * inclusion x * a⁻¹)
    (lambda : linearCharactersTrivialOn (k := k) (N.comap inclusion)) :
    lambda.1.comp alpha.toMonoidHom = lambda.1 := by
  apply MonoidHom.ext
  intro x
  have hdifference : x⁻¹ * alpha x ∈ N.comap inclusion := by
    change inclusion (x⁻¹ * alpha x) ∈ N
    rw [map_mul, map_inv, value]
    exact conjugation_difference_mem N a (inclusion x)
  have hscalar := lambda.2 hdifference
  change lambda.1 (x⁻¹ * alpha x) = 1 at hscalar
  rw [map_mul, map_inv] at hscalar
  exact (inv_mul_eq_one.mp hscalar).symm

end QuotientConjugation

section ActualBrauerInertia

variable {Gamma k K : Type u}
variable [Group Gamma] [Finite Gamma]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (H N : Subgroup Gamma) [H.Normal] [N.Normal]
variable [IsMulCommutative (Gamma ⧸ N)]
variable (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN)

local instance ambientAction : MulAction Gamma (IBr iotaN) :=
  ambientBrauerAction N iotaN

/-- Every actual Gallagher scalar is fixed by the positive conjugation
homomorphism on the literal inertia subgroup H_theta. -/
theorem brauerGallagherTwist_comp_conjugationHom
    (a : MulAction.stabilizer Gamma theta)
    (lambda : BrauerGallagherTwists (k := k) H N iotaN theta) :
    lambda.1.comp (conjugationOnInertiaSubgroupHom H theta a).toMonoidHom =
      lambda.1 := by
  apply linearCharacter_comp_eq_of_conjugation N
    (H.subtype.comp (BrauerInertia H N iotaN theta).subtype)
    (a : Gamma) (conjugationOnInertiaSubgroupHom H theta a) ?_ lambda
  intro x
  rfl

/-- Pointwise version using the original ambient element and its exact
membership proof in the stabilizer of theta. -/
theorem brauerGallagherTwist_comp_conjugation
    (a : Gamma) (ha : a • theta = theta)
    (lambda : BrauerGallagherTwists (k := k) H N iotaN theta) :
    lambda.1.comp (conjugationOnInertia H theta a ha).toMonoidHom = lambda.1 :=
  brauerGallagherTwist_comp_conjugationHom H N iotaN theta ⟨a, ha⟩ lambda

variable (iotaI : PrimeRegularRootEmbedding 2 k K (BrauerInertia H N iotaN theta))
variable (productFormula : BrauerLinearTensorProductFormula iotaI)

/-- The literal ambient-inertia right action commutes with the literal
inverse tensor action.  This supplies `GallagherLinearTwist.action_commutes`
without accepting scalar invariance as a source field. -/
theorem brauerGallagher_action_commutes :
    letI := MulAction.compHom (IBr iotaI)
      (rightConjugationOnInertiaSubgroupHom H theta);
    letI := brauerGallagherTwistAction H N iotaN theta iotaI productFormula;
    ∀ (a : MulAction.stabilizer Gamma theta)
      (lambda : BrauerGallagherTwists (k := k) H N iotaN theta) (eta : IBr iotaI),
      a • (lambda • eta) = lambda • (a • eta) := by
  intro a lambda eta
  change IrreducibleBrauerCharacter.twist iotaI
      (IrreducibleBrauerCharacter.linearTwist iotaI productFormula eta lambda.1⁻¹)
      (conjugationOnInertiaSubgroupHom H theta a⁻¹) =
    IrreducibleBrauerCharacter.linearTwist iotaI productFormula
      (IrreducibleBrauerCharacter.twist iotaI eta
        (conjugationOnInertiaSubgroupHom H theta a⁻¹)) lambda.1⁻¹
  rw [IrreducibleBrauerCharacter.twist_linearTwist]
  have hscalar :=
    brauerGallagherTwist_comp_conjugationHom H N iotaN theta a⁻¹ lambda⁻¹
  exact congrArg
    (IrreducibleBrauerCharacter.linearTwist iotaI productFormula
      (IrreducibleBrauerCharacter.twist iotaI eta
        (conjugationOnInertiaSubgroupHom H theta a⁻¹))) hscalar

end ActualBrauerInertia

end ModularRep.PaperProofs.TypeBCharacteristicTwoScalarConjugation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
