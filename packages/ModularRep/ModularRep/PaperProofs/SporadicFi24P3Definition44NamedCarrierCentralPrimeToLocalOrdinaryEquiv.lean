import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryEquiv
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

/-!
# The literal local quotient character equivalence

The normalizer quotient map retains its central prime-to-p kernel.
Its surjectivity is obtained from the internally proved radical/normalizer
packet, and the ordinary equivalence uses its actual kernel.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToLocalOrdinaryEquiv

open ModularRep
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryEquiv
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicals
open CentralEllPrimeWeightLocalQuotient

universe u

def qWDefectZeroEquiv
    {p : Nat} {K X : Type u}
    [Field K] [CharZero K] [Group X] [Finite X] [Fact p.Prime]
    (Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
    (Q : Subgroup X) (hQ : IsRadicalSubgroup p Q) :
    KernelConstantDefectZeroIrr (p := p) (K := K) (qW Z Q) ≃
      DefectZeroIrr p K (NormalizerQuotient (Q.map (QuotientGroup.mk' Z))) :=
  defectZeroInflationDescentEquiv (qW Z Q)
    (qW_surjective_ofNavarroTiep Z hcentral hprimeTo Q hQ
      (fixedCentralQuotientSource Z hcentral hprimeTo Q hQ))
    (qW_ker_card_not_dvd Z Q hcentral hprimeTo)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToLocalOrdinaryEquiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
