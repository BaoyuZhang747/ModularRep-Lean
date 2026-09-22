import ManuscriptIBAW.FamilyCertificate
import ManuscriptIBAW.TypeB.OddUniform
import ModularRep.PaperProofs.TypeBCurrentOddInputs

/-!
# Inputs for the matrix Omega group at odd primes

Divisibility of the quotient order is transported along the specified
identification. The source assumptions use the central character argument
and Conlon's theorem on the special Clifford group. The generic or
exceptional target is fixed before the corresponding conclusion is chosen.
-/

noncomputable section
namespace ManuscriptIBAW.TypeB.OddInputs
open ModularRep ModularRep.PaperProofs TypeBCliffordCarriers TypeBCurrentCertificate

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  (parameters : OddFieldParameters F p f) (rank : 3 ≤ n) (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)
  (ell : ℕ) (odd : Odd ell) (nondefining : ¬ ell ∣ Nat.card F)
  (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F))

/-- The coefficient system and specified geometry precede the source assumptions
for each case. -/
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
  sources : OddUniform.Inputs parameters N Msys rank odd nondefining
    (TypeBCurrentOddInputs.quotient_divides parameters rank N C ell divides centre)

attribute [instance] Inputs.fieldk Inputs.fieldK Inputs.ringO Inputs.domainO
  Inputs.algebraO Inputs.chark Inputs.algClosedk Inputs.charZeroK

/-- The complete result at odd primes for the independently defined matrix
group. -/
theorem Inputs.complete
    (source : Inputs parameters rank N C ell odd nondefining divides) :
    Nonempty (FamilyCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) ell) := by
  obtain ⟨certificate⟩ := OddUniform.certificate parameters N source.Msys rank odd nondefining
    (TypeBCurrentOddInputs.quotient_divides parameters rank N C ell divides source.centre)
    source.sources
  exact ⟨certificate.along
    (TypeBCliffordOrthogonalSourceBinding.matrixOmegaEquiv n F N parameters rank C source.centre)⟩

end ManuscriptIBAW.TypeB.OddInputs

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
