import ModularRep.BrauerCharacterCommonRootCompatibility
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Canonical quotient root conventions obtained by restricting the given
ambient convention. The original ambient root embedding is retained. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot

open ModularRep

universe u v w
variable {p : ℕ} {k : Type u} {K : Type v} {X : Type w}
variable [Field k] [Field K] [Group X] [Finite X]

theorem commonRoot_self (iota : PrimeRegularRootEmbedding p k K X) :
    PrimeRegularRootEmbedding.ofCommonRoot iota.prime iota.toMulEquiv
      (dvd_refl (primeRegularExponent p X)) = iota := by
  cases iota with
  | mk hp e =>
    congr 1

theorem quotientExponent_dvd (N : Subgroup X) [N.Normal] :
    primeRegularExponent p (X ⧸ N) ∣ primeRegularExponent p X := by
  simpa only [primeRegularExponent] using
    Nat.ordCompl_dvd_ordCompl_of_dvd N.card_quotient_dvd_card p

def quotientRoot (iota : PrimeRegularRootEmbedding p k K X)
    (N : Subgroup X) [N.Normal] : PrimeRegularRootEmbedding p k K (X ⧸ N) :=
  PrimeRegularRootEmbedding.ofCommonRoot iota.prime iota.toMulEquiv (quotientExponent_dvd N)

theorem quotientRoot_compatible
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K X) (N : Subgroup X) [N.Normal]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k (X ⧸ N) V) :
    Representation.BrauerRootLiftCompatibleAlong rho (quotientRoot iota N) iota
      (QuotientGroup.mk' N) := by
  simpa only [quotientRoot, commonRoot_self] using
    Representation.brauerRootLiftCompatibleAlong_of_commonRoot rho (QuotientGroup.mk' N)
      iota.prime iota.toMulEquiv (quotientExponent_dvd N)
      (dvd_refl (primeRegularExponent p X))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
