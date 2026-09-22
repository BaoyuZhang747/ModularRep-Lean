import ModularRep.PaperProofs.TypeBCurrentOddCertificate

/-!
# Boxed sources for the retained odd-prime proof

The matrix Omega group and its prime divisor are fixed before the modular
system and independent branch sources are supplied. The quotient-order
divisor is transported through the constructed Clifford quotient map.
The generic Spin and exceptional sixfold-cover branches remain exactly
those of the retained uniform application.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCurrentOddInputs

open ModularRep TypeBCliffordCarriers
open TypeBCurrentCertificate

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  (parameters : OddFieldParameters F p f) (rank : 3 ≤ n) (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)
  (ell : ℕ) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
  (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F))

include parameters rank C divides in
/-- The actual matrix order and Spin/centre quotient order agree by the
first isomorphism theorem for the constructed Clifford vector action. -/
theorem quotient_divides
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N) :
    ell ∣ Nat.card (TypeBSpinCoverSource.Omega N) := by
  have order := Nat.card_congr
    (TypeBCliffordOrthogonalSourceBinding.matrixOmegaEquiv n F N parameters rank C centre).toEquiv
  exact order.symm ▸ divides

/-- Only the coefficient system, actual centre source and retained raw
branch inputs are boxed. The uniform theorem constructs its complete
normalized family witness internally. -/
structure Inputs where
  k : Type
  K : Type
  O : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O K]
  [chark : CharP k ell]
  [algClosedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  Msys : ModularSystem ell K O k
  centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N
  oldInputs : TypeBProposition44UniformInstantiation.Inputs parameters N Msys
    rank odd nondefining (quotient_divides parameters rank N C ell divides centre)

attribute [instance] Inputs.fieldk Inputs.fieldK Inputs.ringO Inputs.domainO
  Inputs.algebraO Inputs.chark Inputs.algClosedk Inputs.charZeroK

/-- The accepted uniform odd-prime deduction gives a fixed complete
certificate on the actual matrix group, preserving its selected cover,
coefficient roots, block families and matching. -/
theorem Inputs.complete
    (source : Inputs parameters rank N C ell odd nondefining divides) :
    Nonempty (IBAWCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) ell) :=
  TypeBCurrentOddCertificate.matrixCertificate parameters N source.Msys rank odd nondefining
    (quotient_divides parameters rank N C ell divides source.centre) C source.centre source.oldInputs

end ModularRep.PaperProofs.TypeBCurrentOddInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
