import ModularRep.RegularRestriction
import Mathlib.Data.Nat.Factorization.Basic
import ModularRep.PaperProofs.TypeBCentralKernelBrauerInflation

/-! Prime regular lifting is a deduction for every surjective homomorphism
from a finite group. No kernel restriction or lifting source is needed. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeRegularLifting

open ModularRep

universe u v

theorem primeRegularElement_map_surjective_of_surjective
    {p : ℕ} (hp : p.Prime) {A : Type u} {B : Type v}
    [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) :
    Function.Surjective (PrimeRegularElement.map (p := p) f) := by
  classical
  intro y
  obtain ⟨x, hx⟩ := hf y.1
  let e := (orderOf x).factorization p
  have hdiv : p ^ e ∣ orderOf x := Nat.ordProj_dvd (orderOf x) p
  have hxregular : IsPrimeRegular p (x ^ (p ^ e)) := by
    change (orderOf (x ^ (p ^ e))).Coprime p
    rw [orderOf_pow_of_dvd (x := x) (pow_ne_zero e hp.ne_zero) hdiv]
    exact (Nat.coprime_ordCompl hp (orderOf_pos x).ne').symm
  have hycoprime : (p ^ e).Coprime (orderOf y.1) :=
    (show (orderOf y.1).Coprime p from y.2).symm.pow_left e
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := y.1) hycoprime
  refine ⟨⟨(x ^ (p ^ e)) ^ m, hxregular.pow m⟩, ?_⟩
  apply Subtype.ext
  change f ((x ^ (p ^ e)) ^ m) = y.1
  rw [map_pow, map_pow, hx]
  exact hm

theorem primeRegularQuotientLiftPrinciple (p : ℕ) :
    TypeBCentralKernelBrauerInflation.PrimeRegularQuotientLiftPrinciple.{u} p := by
  intro X _ _ R _ hp _hR
  exact primeRegularElement_map_surjective_of_surjective hp
    (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeRegularLifting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
