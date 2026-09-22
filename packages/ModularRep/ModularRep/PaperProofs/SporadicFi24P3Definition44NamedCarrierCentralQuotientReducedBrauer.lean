import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

/-! The exact central kernel and the associated quotient Brauer character.
The whole representation kernel is not identified with the centre. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauer

open ModularRep ModularRep.FDRepSimpleClassKZero
open EvenFieldFLZBAWGoodFamily CentralEllPrimeIBrFibreTransport
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance quotientFintype (H : Subgroup X) [H.Normal] : Fintype (X ⧸ H) := Fintype.ofFinite _
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))

section CentralSubgroup
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
variable (hcentral : Z ≤ Subgroup.center X)

theorem trivialBrauerFibre_le_chosen_kernel
    (phi : trivialBrauerFibre iota R Z hcentral) :
    Z ≤ (chosenIBrRepresentation iota phi.val).ρ.ker := by
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  let V := chosenIBrRepresentation iota phi.val
  let _ : Representation.IsIrreducible V.ρ := (Classical.choose_spec phi.val.property).1
  have hscalar : Representation.centralCharacter V.ρ Z hcentral = 1 := by
    calc
      Representation.centralCharacter V.ρ Z hcentral =
          blockCentralCharacter iota R.1.operations.ambientBlockData.blocks
            (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral phi.val :=
        (blockCentralCharacter_eq_of_affords iota R.1.operations.ambientBlockData.blocks
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral phi.val V
          (chosenIBrRepresentation_character iota phi.val)).symm
      _ = 1 := phi.property
  exact le_ker_of_centralCharacter_eq_one (Z := Z) hcentral V.ρ hscalar

theorem trivialBrauerFibre_central_kernel
    (phi : trivialBrauerFibre iota R Z hcentral) :
    Z ⊓ (chosenIBrRepresentation iota phi.val).ρ.ker = Z :=
  inf_eq_left.mpr (trivialBrauerFibre_le_chosen_kernel iota R Z hcentral phi)

theorem canonicalBrauerEquiv_symm_unique
    (phi : trivialBrauerFibre iota R Z hcentral)
    (chi : IBr (quotientRoot iota Z))
    (hchi : PrimeRegularClassFunction.pullback (QuotientGroup.mk' Z) chi.val = phi.val.val) :
    chi = (canonicalBrauerEquiv iota R Z hcentral).symm phi := by
  apply Subtype.ext
  apply QuotientRealisationSource.pullback_injective
    iota (quotientRoot iota Z) (canonicalQuotientRealisation iota Z)
  exact hchi.trans (canonicalBrauerEquiv_symm_pullback iota R Z hcentral phi).symm

theorem canonicalBrauerEquiv_symm_eq_deflate
    (phi : trivialBrauerFibre iota R Z hcentral) :
    let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
    (canonicalBrauerEquiv iota R Z hcentral).symm phi =
      deflateIBr iota (quotientRoot iota Z) R.1.operations.ambientBlockData.blocks
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral phi := by
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  dsimp only
  symm
  apply canonicalBrauerEquiv_symm_unique iota R Z hcentral phi
  exact congrArg (fun chi : IBr iota => chi.val)
    (inflate_deflate iota (quotientRoot iota Z) (canonicalQuotientRealisation iota Z)
      R.1.operations.ambientBlockData.blocks
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) hcentral phi)
end CentralSubgroup

theorem fullCenter_trivialBrauerFibre_kernel
    [Invertible (Fintype.card (Subgroup.center X) : k)]
    (phi : trivialBrauerFibre iota R (Subgroup.center X) le_rfl) :
    Subgroup.center X ⊓ (chosenIBrRepresentation iota phi.val).ρ.ker = Subgroup.center X :=
  trivialBrauerFibre_central_kernel iota R (Subgroup.center X) le_rfl phi

def centralKernelQuotientEquiv
    [Invertible (Fintype.card (Subgroup.center X) : k)]
    (phi : trivialBrauerFibre iota R (Subgroup.center X) le_rfl) :
    X ⧸ (Subgroup.center X ⊓ (chosenIBrRepresentation iota phi.val).ρ.ker) ≃*
      X ⧸ Subgroup.center X :=
  QuotientGroup.quotientMulEquivOfEq (fullCenter_trivialBrauerFibre_kernel iota R phi)

theorem centralKernelQuotientEquiv_mk
    [Invertible (Fintype.card (Subgroup.center X) : k)]
    (phi : trivialBrauerFibre iota R (Subgroup.center X) le_rfl) (x : X) :
    centralKernelQuotientEquiv iota R phi
      (QuotientGroup.mk' (Subgroup.center X ⊓ (chosenIBrRepresentation iota phi.val).ρ.ker) x) =
      QuotientGroup.mk' (Subgroup.center X) x := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBrauer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
