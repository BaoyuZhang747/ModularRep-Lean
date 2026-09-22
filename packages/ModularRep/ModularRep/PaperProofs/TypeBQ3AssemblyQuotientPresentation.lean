import ModularRep.PaperProofs.TypeBQ3AssemblyCriterionData
import ModularRep.PaperProofs.TypeBQ3B2CentralQuotient
import ModularRep.PaperProofs.TypeBQ3PrincipalInertiaQuotient

/-!
# A specified criterion on the natural common central quotient

This is an output witness for a specified finite presentation Y of the common
central quotient of an actual block of X. The final construction supplies its
fields from the fixed branch deductions. The witness is not a published
source interface.

The common quotient equivalence and every own-character quotient equivalence
are constructed from the same projection. Their natural squares and character
values are deductions. The criterion remains on Y; no criterion on a different
syntactic quotient carrier is asserted without its specified transport.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyQuotientPresentation

open ModularRep
open TypeBQ3TripleCoverCarrier TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalCriterionDominatedBlock TypeBQ3PrincipalWeightInflation
open IrreducibleBrauerCharacterSurjectiveDescent
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
variable [Finite X]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

/-- Centrelessness proves the central-faithfulness precondition on every block. -/
theorem centralFaithful_of_center_eq_bot
    {Z : Type} [Group Z] [Finite Z]
    (rootZ : PrimeRegularRootEmbedding 2 k K Z)
    (bZ : LiteralPrimitiveBlock k Z) (centreless : Subgroup.center Z = ⊥) :
    ∀ phi : BrauerFibre rootZ bZ,
      TypeBBSCentralCharacterQuotient.centralKernel rootZ phi.val = ⊥ :=
  fun phi => TypeBBSCentralCharacterQuotient.centralKernel_eq_bot
    rootZ phi.val centreless

include matrixSource in
/-- The actual matrix G3 is centreless, so its supported characters meet that precondition. -/
theorem centralFaithful_G3
    (rootG3 : PrimeRegularRootEmbedding 2 k K G3)
    (bG3 : LiteralPrimitiveBlock k G3) :
    ∀ phi : BrauerFibre rootG3 bG3,
      TypeBBSCentralCharacterQuotient.centralKernel rootG3 phi.val = ⊥ :=
  centralFaithful_of_center_eq_bot rootG3 bG3
    (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource)

/-- The kernel of the common block sector, embedded in the original group. -/
def commonKernel (bX : LiteralPrimitiveBlock k X) : Subgroup X :=
  (centralSector matrixSource freeSource bX).ker.map (Subgroup.center X).subtype

theorem commonKernel_le_center (bX : LiteralPrimitiveBlock k X) :
    commonKernel matrixSource freeSource bX ≤ Subgroup.center X := by
  rintro x ⟨z, hz, rfl⟩
  exact z.property

variable (rootX : PrimeRegularRootEmbedding 2 k K X)
  (bX : LiteralPrimitiveBlock k X)
  {Y : Type} [Group Y] [Finite Y]
  (f : X →* Y) (rootY : PrimeRegularRootEmbedding 2 k K Y)
  (R : CoverWeightSource (k := k) (K := K) Y)

/-- Complete output on the specified natural quotient presentation. -/
structure Witness where
  surjective : Function.Surjective f
  kernel_eq_common : f.ker = commonKernel matrixSource freeSource bX
  downBlock : LiteralPrimitiveBlock k Y
  block_image : algebraMapOf f bX.val = downBlock.val
  deflation : BrauerFibre rootX bX ≃ BrauerFibre rootY downBlock
  deflation_pullback : ∀ phi : BrauerFibre rootX bX,
    PrimeRegularClassFunction.pullback f (deflation phi).val.val = phi.val.val
  ownKernel_eq : ∀ phi : BrauerFibre rootX bX,
    TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val = f.ker
  centralFaithful : ∀ phi : BrauerFibre rootY downBlock,
    TypeBBSCentralCharacterQuotient.centralKernel rootY phi.val = ⊥
  matching : BrauerFibre rootY downBlock ≃ CoverWeight R downBlock
  clauses : TypeBQ3AssemblyCriterionData.CompleteClauses rootY R downBlock matching

variable (W : Witness matrixSource freeSource rootX bX f rootY R)

include W

/-- Normality of the common kernel follows from its equality with the kernel. -/
def commonKernelNormal : (commonKernel matrixSource freeSource bX).Normal :=
  W.kernel_eq_common ▸ MonoidHom.normal_ker f

/-- The common quotient is identified by the same surjective homomorphism. -/
def commonQuotientEquiv :
    letI := commonKernelNormal matrixSource freeSource rootX bX f rootY R W
    X ⧸ commonKernel matrixSource freeSource bX ≃* Y := by
  letI := commonKernelNormal matrixSource freeSource rootX bX f rootY R W
  exact (QuotientGroup.quotientMulEquivOfEq W.kernel_eq_common.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f W.surjective)

@[simp] theorem commonQuotientEquiv_mk (x : X) :
    letI := commonKernelNormal matrixSource freeSource rootX bX f rootY R W
    commonQuotientEquiv matrixSource freeSource rootX bX f rootY R W
      (QuotientGroup.mk' (commonKernel matrixSource freeSource bX) x) = f x := rfl

/-- This is the common central kernel of every displayed supported character. -/
theorem ownKernel_eq_common (phi : BrauerFibre rootX bX) :
    TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val =
      commonKernel matrixSource freeSource bX :=
  (W.ownKernel_eq phi).trans W.kernel_eq_common

/-- The central order-three carrier gives the prime-to-two kernel guard. -/
theorem kernel_primeToTwo : ¬ 2 ∣ Nat.card f.ker := by
  intro divides
  have leCenter : f.ker ≤ Subgroup.center X := by
    rw [W.kernel_eq_common]
    exact commonKernel_le_center matrixSource freeSource bX
  have bad : 2 ∣ Nat.card (Subgroup.center X) :=
    divides.trans (Subgroup.card_dvd_of_le leCenter)
  rw [center_X_card matrixSource freeSource] at bad
  exact (by decide : ¬ 2 ∣ 3) bad

/-- Each character's own central quotient uses the same projection. -/
def ownQuotientEquiv (phi : BrauerFibre rootX bX) :
    TypeBQ3PrincipalExtensionCentralQuotient.CentralQuotient rootX bX phi ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq (W.ownKernel_eq phi)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f W.surjective)

@[simp] theorem ownQuotientEquiv_mk (phi : BrauerFibre rootX bX) (x : X) :
    ownQuotientEquiv matrixSource freeSource rootX bX f rootY R W phi
      (QuotientGroup.mk'
        (TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val) x) = f x := rfl

/-- The unchanged own quotient character equals the deflated character's pullback. -/
theorem ownQuotientBrauer_eq_pullback (phi : BrauerFibre rootX bX) :
    (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer rootX bX phi).val =
      PrimeRegularClassFunction.pullback
        (ownQuotientEquiv matrixSource freeSource rootX bX f rootY R W phi).toMonoidHom
        (W.deflation phi).val.val := by
  let pi := QuotientGroup.mk'
    (TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val)
  have hprime : (Nat.card pi.ker).Coprime 2 := by
    rw [QuotientGroup.ker_mk', W.ownKernel_eq phi]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr
      (kernel_primeToTwo matrixSource freeSource rootX bX f rootY R W)).symm
  apply primeRegularClassFunction_pullback_injective_of_ker_card_coprime
    pi (QuotientGroup.mk'_surjective _) hprime
  calc
    (PrimeRegularClassFunction.pullback pi
      (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer rootX bX phi).val :
        PrimeRegularClassFunction K X 2) = phi.val.val :=
      TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer_inflation rootX bX phi
    _ = _ := by
      apply PrimeRegularClassFunction.ext
      intro x
      have values := congrArg (fun eta : PrimeRegularClassFunction K X 2 => eta x)
        (W.deflation_pullback phi)
      exact values.symm

/-- The inverse equivalence has literal inflation values on the full lower fibre. -/
theorem deflation_symm_pullback (phi : BrauerFibre rootY W.downBlock) :
    (W.deflation.symm phi).val.val = PrimeRegularClassFunction.pullback f phi.val.val := by
  have values := W.deflation_pullback (W.deflation.symm phi)
  rw [W.deflation.apply_symm_apply] at values
  exact values.symm

end ModularRep.PaperProofs.TypeBQ3AssemblyQuotientPresentation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
