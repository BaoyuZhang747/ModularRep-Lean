import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFactorOneExtension

/-! Realize the exact retained factor-one model at its original root.
The top-base restriction determines the resulting irreducible character. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopExtensions

open ModularRep Representation.Extension
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension

universe u
variable {p : ℕ} {k K H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H]
variable (root : PrimeRegularRootEmbedding p k K H) (theta : IBr root)
local notation "eTop" => (Subgroup.topEquiv.symm : H ≃* (⊤ : Subgroup H))
local notation "rTop" => root.alongMulEquiv eTop
local notation "thetaTop" => IrreducibleBrauerCharacter.alongMulEquiv root eTop theta
variable {U : Type u} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
variable (rho : Representation k (⊤ : Subgroup H) U)

def topModelExtension
    (M : AssociatedProjectiveModel (⊤ : Subgroup H) rho)
    (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (haffords : (thetaTop).val = rho.brauerCharacterOfRootEmbedding rTop) :
    BrauerCharacterExtensionWitness root rTop thetaTop := by
  refine brauerExtensionOfFactorOne M hM hirr root rTop thetaTop haffords.symm ?_
  intro zeta
  exact PrimeRegularRootEmbedding.alongMulEquiv_lift root eTop (((zeta : kˣ) : k))

theorem topModelExtension_val
    (M : AssociatedProjectiveModel (⊤ : Subgroup H) rho)
    (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (haffords : (thetaTop).val = rho.brauerCharacterOfRootEmbedding rTop) :
    (topModelExtension root theta rho M hM hirr haffords).val = theta := by
  let W := topModelExtension root theta rho M hM hirr haffords
  change W.val = theta
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  have h := congrArg
    (fun chi : PrimeRegularClassFunction K (⊤ : Subgroup H) p =>
      chi (PrimeRegularElement.map (eTop).toMonoidHom x)) W.property
  change W.val.val x = theta.val x at h
  exact h

theorem topModelExtension_operator_character
    (M : AssociatedProjectiveModel (⊤ : Subgroup H) rho)
    (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (haffords : (thetaTop).val = rho.brauerCharacterOfRootEmbedding rTop) :
    (topModelExtension root theta rho M hM hirr haffords).val.val =
      (representationOfFactorOne M hM).brauerCharacterOfRootEmbedding root := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
