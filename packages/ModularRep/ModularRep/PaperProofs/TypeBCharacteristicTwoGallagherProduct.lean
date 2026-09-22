import ModularRep.PaperProofs.TypeBCharacteristicTwoScalarConjugation
import ModularRep.PaperProofs.TypeBCharacteristicTwoExtensionCarriers

/-!
# Invariance from the literal ambient extension and Gallagher product

An ambient Brauer character is a class function on Gamma_theta.  Its
restriction to the actual H_theta is therefore invariant under the same
ambient-inertia conjugation.  The quotient-linear factor is invariant by
the separately proved quotient calculation, so their explicit product is
invariant as well.

The final factory fills the existing Gallagher interface from this product
formula.  Its relation is defined by that formula, and its action law is
proved.  It accepts no new source, extension fixedness, or stabilizer
conclusion.  The final source wrapper must obtain `HasGallagherProduct`
from its exact modular Gallagher certificate and actual `AmbientExtension`.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherProduct

open TypeBLemma47LeviApplication
open TypeBCharacteristicTwoCliffordKernel TypeBCharacteristicTwoCliffordApplication
open TypeBCharacteristicTwoExtensionCarriers TypeBCharacteristicTwoScalarConjugation
open ModularRep.ManuscriptVerification.CharacteristicTwoClifford

universe u

variable {Gamma k K : Type u}
variable [Group Gamma] [Finite Gamma]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (H N : Subgroup Gamma) [H.Normal] [N.Normal]
variable (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN)

local instance ambientAction : MulAction Gamma (IBr iotaN) :=
  ambientBrauerAction N iotaN

/-- Both conjugation computations use the same point of Gamma_theta. -/
theorem inertiaInclusion_conjugation
    (a : AmbientInertia N iotaN theta) (x : BrauerInertia H N iotaN theta) :
    inertiaInclusion H N iotaN theta (conjugationOnInertiaSubgroupHom H theta a x) =
      a * inertiaInclusion H N iotaN theta x * a⁻¹ := by
  apply Subtype.ext
  rfl

variable (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta))
variable (chi : IBr iotaA)

/-- Restriction of an actual ambient class function is fixed by ambient
inertia conjugation.  This uses its class-function axiom, not an extension
invariance certificate. -/
theorem restrictedExtension_twist_conjugation
    (a : AmbientInertia N iotaN theta) :
    (restrictedExtension H N iotaN theta iotaA chi).twist
      (conjugationOnInertiaSubgroupHom H theta a) =
        restrictedExtension H N iotaN theta iotaA chi := by
  apply PrimeRegularClassFunction.ext
  intro x
  change chi.1 (PrimeRegularElement.map (inertiaInclusion H N iotaN theta)
      (PrimeRegularElement.map (conjugationOnInertiaSubgroupHom H theta a).toMonoidHom x)) =
    chi.1 (PrimeRegularElement.map (inertiaInclusion H N iotaN theta) x)
  have hpoint :
      PrimeRegularElement.map (inertiaInclusion H N iotaN theta)
        (PrimeRegularElement.map (conjugationOnInertiaSubgroupHom H theta a).toMonoidHom x) =
      ⟨a * (PrimeRegularElement.map (inertiaInclusion H N iotaN theta) x).1 * a⁻¹,
        (PrimeRegularElement.map (inertiaInclusion H N iotaN theta) x).2.conj a⟩ := by
    apply Subtype.ext
    exact inertiaInclusion_conjugation H N iotaN theta a x.1
  rw [hpoint]
  exact chi.1.map_conj a (PrimeRegularElement.map (inertiaInclusion H N iotaN theta) x)

variable [IsMulCommutative (Gamma ⧸ N)]
variable (iotaI : PrimeRegularRootEmbedding 2 k K (BrauerInertia H N iotaN theta))

/-- The literal Gallagher multiplication formula gives invariance under
the actual ambient inertia.  No use of a stabilizer conclusion is made. -/
theorem hasGallagherProduct_fixed
    (eta : IBr iotaI)
    (product : HasGallagherProduct H N iotaN theta iotaI iotaA chi eta)
    (a : AmbientInertia N iotaN theta) :
    letI := MulAction.compHom (IBr iotaI)
      (rightConjugationOnInertiaSubgroupHom H theta);
    a • eta = eta := by
  change IrreducibleBrauerCharacter.twist iotaI eta
    (conjugationOnInertiaSubgroupHom H theta a⁻¹) = eta
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  obtain ⟨lambda, hlambda⟩ := product
  rw [hlambda]
  calc
    (PrimeRegularClassFunction.pointwiseMul
        (iotaI.liftedLinearCharacter lambda.1)
        (restrictedExtension H N iotaN theta iotaA chi)).twist
          (conjugationOnInertiaSubgroupHom H theta a⁻¹) =
      PrimeRegularClassFunction.pointwiseMul
        ((iotaI.liftedLinearCharacter lambda.1).twist
          (conjugationOnInertiaSubgroupHom H theta a⁻¹))
        ((restrictedExtension H N iotaN theta iotaA chi).twist
          (conjugationOnInertiaSubgroupHom H theta a⁻¹)) := by
            ext x
            rfl
    _ = PrimeRegularClassFunction.pointwiseMul
        (iotaI.liftedLinearCharacter lambda.1)
        (restrictedExtension H N iotaN theta iotaA chi) := by
      rw [PrimeRegularRootEmbedding.liftedLinearCharacter_twist,
        brauerGallagherTwist_comp_conjugationHom H N iotaN theta a⁻¹ lambda,
        restrictedExtension_twist_conjugation H N iotaN theta iotaA chi a⁻¹]

variable (productFormula : BrauerLinearTensorProductFormula iotaI)

/-- This K factory adapts the actual multiplication formula to the checked
Gallagher interface.  The local `LiesOver` relation is visibly fixed by the
formula and chosen constituent; it is not a freely supplied predicate. -/
def gallagherLinearTwistOfProduct
    (eta : IBr iotaI)
    (product : HasGallagherProduct H N iotaN theta iotaI iotaA chi eta) :
    letI := MulAction.compHom (IBr iotaN) (AmbientInertia N iotaN theta).subtype;
    letI := MulAction.compHom (IBr iotaI)
      (rightConjugationOnInertiaSubgroupHom H theta);
    letI := brauerGallagherTwistAction H N iotaN theta iotaI productFormula;
    GallagherLinearTwist
      (A := AmbientInertia N iotaN theta)
      (Eta := IBr iotaI) (BrauerGallagherTwists (k := k) H N iotaN theta) theta eta := by
  letI := MulAction.compHom (IBr iotaN) (AmbientInertia N iotaN theta).subtype
  letI := MulAction.compHom (IBr iotaI) (rightConjugationOnInertiaSubgroupHom H theta)
  letI := brauerGallagherTwistAction H N iotaN theta iotaI productFormula
  refine
    { LiesOver := fun t u ↦ t = theta ∧
        HasGallagherProduct H N iotaN theta iotaI iotaA chi u
      chosen := ⟨rfl, product⟩
      exists_twist := ?_
      action_commutes := ?_ }
  · intro a u hu _
    refine ⟨1, ?_⟩
    simpa only [one_smul] using
      hasGallagherProduct_fixed H N iotaN theta iotaA chi iotaI u hu.2 a
  · exact brauerGallagher_action_commutes H N iotaN theta iotaI productFormula

end ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherProduct


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
