import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
import Mathlib.GroupTheory.Index

/-! Restrict the given root convention along an actual finite surjection. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot

open ModularRep
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot

universe u v w x
variable {p : ℕ} {k : Type u} {K : Type v} {A : Type w} {B : Type x}
variable [Field k] [Field K] [Group A] [Finite A] [Group B] [Finite B]

theorem surjectiveExponent_dvd (f : A →* B) (hf : Function.Surjective f) :
    primeRegularExponent p B ∣ primeRegularExponent p A := by
  simpa only [primeRegularExponent] using
    Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_dvd_of_surjective f hf) p

def surjectiveRoot (iota : PrimeRegularRootEmbedding p k K A)
    (f : A →* B) (hf : Function.Surjective f) : PrimeRegularRootEmbedding p k K B :=
  PrimeRegularRootEmbedding.ofCommonRoot iota.prime iota.toMulEquiv (surjectiveExponent_dvd f hf)

theorem surjectiveRoot_compatible [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K A)
    (f : A →* B) (hf : Function.Surjective f)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k B V) :
    Representation.BrauerRootLiftCompatibleAlong rho (surjectiveRoot iota f hf) iota f := by
  simpa only [surjectiveRoot, commonRoot_self] using
    Representation.brauerRootLiftCompatibleAlong_of_commonRoot rho f
      iota.prime iota.toMulEquiv (surjectiveExponent_dvd f hf)
      (dvd_refl (primeRegularExponent p A))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
