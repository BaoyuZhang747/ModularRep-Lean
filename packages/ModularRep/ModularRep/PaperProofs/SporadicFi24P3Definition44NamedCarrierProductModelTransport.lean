import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

/-! Reindex the SAME associated models along proved equal base subgroups.
The product-denominator quotient map remains induced by the original inclusion. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierProductModelTransport

open ModularRep
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

universe u

section Factors
variable {k H J H' J' : Type u} [Field k]
variable [Group H] [Group J] [Group H'] [Group J']

theorem factorSet_ext {a b : ScalarFactorSet k H}
    (h : ∀ x y, a x y = b x y) : a = b := by
  cases a with
  | mk af al ar ac =>
    cases b with
    | mk bf bl br bc =>
      have hf : af = bf := funext fun x => funext fun y => h x y
      cases hf
      rfl

theorem factorSet_reindex_eq (eL : H' ≃* H) (eG : J' ≃* J) (qE : H ≃* J)
    (a : ScalarFactorSet k H) (b : ScalarFactorSet k J)
    (h : a = ScalarFactorSet.pullback qE b) :
    ScalarFactorSet.pullback eL a =
      ScalarFactorSet.pullback (eL.trans (qE.trans eG.symm))
        (ScalarFactorSet.pullback eG b) := by
  rw [h]
  apply factorSet_ext
  intro x y
  change b (qE (eL x)) (qE (eL y)) =
    b (eG (eG.symm (qE (eL x)))) (eG (eG.symm (qE (eL y))))
  rw [eG.apply_symm_apply, eG.apply_symm_apply]

theorem factorSet_reindex_cohomologous
    (eL : H' ≃* H) (eG : J' ≃* J) (qE : H ≃* J)
    (a : ScalarFactorSet k H) (b : ScalarFactorSet k J)
    (h : ScalarFactorSet.Cohomologous a (ScalarFactorSet.pullback qE b)) :
    ScalarFactorSet.Cohomologous (ScalarFactorSet.pullback eL a)
      (ScalarFactorSet.pullback (eL.trans (qE.trans eG.symm))
        (ScalarFactorSet.pullback eG b)) := by
  obtain ⟨c, hc, hfactor⟩ := h
  refine ⟨fun x => c (eL x), ?_, ?_⟩
  · simpa only [map_one] using hc
  · intro x y
    change b (eG (eG.symm (qE (eL x)))) (eG (eG.symm (qE (eL y)))) =
      c (eL x) * c (eL y) * (c (eL (x * y)))⁻¹ * a (eL x) (eL y)
    rw [eG.apply_symm_apply, eG.apply_symm_apply, map_mul]
    exact hfactor (eL x) (eL y)

end Factors

section Model
variable {k A U : Type u} [Field k] [Group A]
variable [AddCommGroup U] [Module k U]
variable (B B' : Subgroup A) [B.Normal] [B'.Normal]
variable (hB : B' = B) (rho : Representation k B U)

def representationOnEqualBase : Representation k B' U :=
  rho.pullback (MulEquiv.subgroupCongr hB).toMonoidHom

def modelOnEqualBase (M : AssociatedProjectiveModel B rho) :
    AssociatedProjectiveModel B' (representationOnEqualBase B B' hB rho) := by
  subst B'
  exact M

theorem modelOnEqualBase_operator (M : AssociatedProjectiveModel B rho) (a : A) :
    (modelOnEqualBase B B' hB rho M).operator a = M.operator a := by
  subst B'
  rfl

theorem modelOnEqualBase_factorSet (M : AssociatedProjectiveModel B rho) :
    (modelOnEqualBase B B' hB rho M).factorSet =
      ScalarFactorSet.pullback (QuotientGroup.quotientMulEquivOfEq hB) M.factorSet := by
  subst B'
  apply factorSet_ext
  intro x y
  refine Quotient.inductionOn x ?_
  intro a
  refine Quotient.inductionOn y ?_
  intro b
  rfl

end Model

section Quotient
variable {A D : Type u} [Group A] [Group D]
variable (B B' : Subgroup A) [B.Normal] [B'.Normal]
variable (L L' : Subgroup D) [L.Normal] [L'.Normal]
variable (hB : B' = B) (hL : L' = L) (qE : D ⧸ L ≃* A ⧸ B)

def productQuotientEquiv : D ⧸ L' ≃* A ⧸ B' :=
  (QuotientGroup.quotientMulEquivOfEq hL).trans
    (qE.trans (QuotientGroup.quotientMulEquivOfEq hB).symm)

theorem productQuotientEquiv_mk (f : D →* A)
    (hq : ∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B (f d))
    (d : D) :
    productQuotientEquiv B B' L L' hB hL qE (QuotientGroup.mk' L' d) =
      QuotientGroup.mk' B' (f d) := by
  change (QuotientGroup.quotientMulEquivOfEq hB).symm
    (qE (QuotientGroup.mk' L d)) = _
  rw [hq d]
  rfl

end Quotient

section Comparison
variable {k A D U W : Type u} [Field k] [Group A] [Group D]
variable [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
variable (B B' : Subgroup A) [B.Normal] [B'.Normal]
variable (L L' : Subgroup D) [L.Normal] [L'.Normal]
variable (hB : B' = B) (hL : L' = L)
variable (rhoG : Representation k B U) (rhoL : Representation k L W)
variable (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL)
variable (qE : D ⧸ L ≃* A ⧸ B)

theorem product_factor_equality
    (hfactor : ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet) :
    (modelOnEqualBase L L' hL rhoL ML).factorSet =
      ScalarFactorSet.pullback (productQuotientEquiv B B' L L' hB hL qE)
        (modelOnEqualBase B B' hB rhoG MG).factorSet := by
  rw [modelOnEqualBase_factorSet, modelOnEqualBase_factorSet]
  exact factorSet_reindex_eq _ _ qE ML.factorSet MG.factorSet hfactor

theorem product_cohomology
    (hcohom : ScalarFactorSet.Cohomologous ML.factorSet
      (ScalarFactorSet.pullback qE MG.factorSet)) :
    ScalarFactorSet.Cohomologous (modelOnEqualBase L L' hL rhoL ML).factorSet
      (ScalarFactorSet.pullback (productQuotientEquiv B B' L L' hB hL qE)
        (modelOnEqualBase B B' hB rhoG MG).factorSet) := by
  rw [modelOnEqualBase_factorSet, modelOnEqualBase_factorSet]
  exact factorSet_reindex_cohomologous _ _ qE ML.factorSet MG.factorSet hcohom

/-- The actual product models keep the original operators and quotient square. -/
def ProductModelOutput (f : D →* A) : Prop :=
  (∀ a : A, (modelOnEqualBase B B' hB rhoG MG).operator a = MG.operator a) ∧
  (∀ d : D, (modelOnEqualBase L L' hL rhoL ML).operator d = ML.operator d) ∧
  (∀ d : D, productQuotientEquiv B B' L L' hB hL qE (QuotientGroup.mk' L' d) =
    QuotientGroup.mk' B' (f d)) ∧
  (modelOnEqualBase L L' hL rhoL ML).factorSet =
    ScalarFactorSet.pullback (productQuotientEquiv B B' L L' hB hL qE)
      (modelOnEqualBase B B' hB rhoG MG).factorSet ∧
  ScalarFactorSet.Cohomologous (modelOnEqualBase L L' hL rhoL ML).factorSet
    (ScalarFactorSet.pullback (productQuotientEquiv B B' L L' hB hL qE)
      (modelOnEqualBase B B' hB rhoG MG).factorSet)

theorem product_model_output (f : D →* A)
    (hq : ∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B (f d))
    (hf : ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet)
    (hc : ScalarFactorSet.Cohomologous ML.factorSet (ScalarFactorSet.pullback qE MG.factorSet)) :
    ProductModelOutput B B' L L' hB hL rhoG rhoL MG ML qE f :=
  ⟨modelOnEqualBase_operator B B' hB rhoG MG,
    modelOnEqualBase_operator L L' hL rhoL ML,
    productQuotientEquiv_mk B B' L L' hB hL qE f hq,
    product_factor_equality B B' L L' hB hL rhoG rhoL MG ML qE hf,
    product_cohomology B B' L L' hB hL rhoG rhoL MG ML qE hc⟩

end Comparison
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierProductModelTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
