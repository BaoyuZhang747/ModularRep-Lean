import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding
import ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

/-!
# The identity prime-to-two cover of actual matrix Omega

The full-cover hypothesis is indexed by the constructed Clifford Spin
projection onto the independently defined matrix Omega carrier. Its kernel
has order two by the existing actual kernel/centre equation. The generic
`identityEllPrimeCover_of_fullCover_twoKernel` is applied directly; no
maximality proof or source record is copied here.

This is a conditional group-theoretic adapter for rank at least three.
Malle--Testerman, Theorem 24.17, Remark 24.19 and Tables 24.2--24.3, together
with the standard Schur/free-presentation universal-cover interpretation,
supply the intended E1 background. Matching those facts to this literal
field, norm and projection remains E1/U. At rank three that interpretation
requires `Nat.card F ≠ 3`; the kernel-order calculation alone includes q=3
and does not supply the missing full-cover hypothesis there.

The output is an `EllPrimeCoverSource 2` on actual matrix Omega, with that
same simple group and identity quotient. No character, block, matching,
triple or BAW/iBAW conclusion is an input or output.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBMatrixOmegaPrimeToTwoCover

open TypeBCliffordCarriers
open TypeBCliffordOrthogonalSourceBinding
open EvenFieldFLZ318FixedTheoremGate EvenFieldFLZSourceConditions

local instance finiteGroupFintype (H : Type) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

variable (n : ℕ) (F : Type) [Field F] [Finite F]
variable {p f : ℕ} [CharP F p]
variable (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
variable (N : NormSource n F)
variable (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)
variable (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)

include centre in
/-- The kernel cardinality concerns the actual map to derived matrix SO. -/
theorem spinProjection_kernel_card :
    Nat.card (spinProjection n F parameters rank N C).ker = 2 := by
  rw [spin_kernel_eq_center n F N parameters rank C centre]
  exact centre.centre_order parameters rank

include centre in
/-- The same actual projection has a two-group kernel. -/
theorem spinProjection_kernel_isTwoGroup :
    IsPGroup 2 (spinProjection n F parameters rank N C).ker := by
  apply IsPGroup.of_card (n := 1)
  simpa only [pow_one] using
    spinProjection_kernel_card n F parameters rank N C centre

variable (fullCover : IsUniversalCentralExtension
  (spinProjection n F parameters rank N C))
variable (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F))
variable (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F))

/-- Direct application of the existing generic cover constructor. -/
def identityEllPrimeCover :
    EllPrimeCoverSource 2 (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  OddTwoUniversalPrimeToTwoSelfCover.identityEllPrimeCover_of_fullCover_twoKernel
    (spinProjection n F parameters rank N C) fullCover
    (spinProjection_kernel_isTwoGroup n F parameters rank N C centre)
    simple nonabelian

/-- The simple quotient is literally the current matrix Omega carrier. -/
@[simp] theorem identityEllPrimeCover_simpleGroup :
    (identityEllPrimeCover n F parameters rank N C centre fullCover simple nonabelian).S =
      TypeBOrthogonalOmegaCarriers.Omega n F := rfl

/-- The quotient homomorphism is literally the identity of matrix Omega. -/
@[simp] theorem identityEllPrimeCover_quotient :
    (identityEllPrimeCover n F parameters rank N C centre fullCover simple nonabelian).quotient =
      MonoidHom.id (TypeBOrthogonalOmegaCarriers.Omega n F) := rfl

end ModularRep.PaperProofs.TypeBMatrixOmegaPrimeToTwoCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
