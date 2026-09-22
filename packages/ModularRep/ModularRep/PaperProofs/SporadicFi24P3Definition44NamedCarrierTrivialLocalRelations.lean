import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLocalRelations

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLocalRelations

open SporadicFi24P3Definition44NamedCarrierSparseCyclotomicCertificate

variable {K : Type*} [Field K] [CharZero K]

def phi13 (w : K) : K :=
  1 + w + w^2 + w^3 + w^4 + w^5 + w^6 +
    w^7 + w^8 + w^9 + w^10 + w^11 + w^12

theorem phi13_zero {w : K} (hw : IsPrimitiveRoot w 13) : phi13 w = 0 := by
  have h := ratEval_geometric_zero (by norm_num : 0 < 13) hw
    (by norm_num : 1 < 13) (by norm_num : 13 ∣ 13)
  simpa [phi13, ratEval, geometricPolynomial, Finset.sum_range_succ] using h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialLocalRelations


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
