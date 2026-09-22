import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms

/-! The full Brauer automorphism stabilizer is a literal ambient group for
a centreless group. This construction needs neither a block census nor
a splitting of the outer automorphism group. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms

universe u

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)

local instance mulAutFinite : Finite (MulAut G) :=
  Finite.of_injective (fun alpha : MulAut G => (alpha : G → G)) DFunLike.coe_injective

abbrev ActualAutAmbient := MulAction.stabilizer (MulAut G)ᵐᵒᵖ phi

instance actualAmbientFinite : Finite (ActualAutAmbient iota phi) :=
  Finite.of_injective (fun a : ActualAutAmbient iota phi => a.1.unop)
    (MulOpposite.unop_injective.comp Subtype.val_injective)

def innerEmbedding : G →* ActualAutAmbient iota phi :=
  (inverseOpHom (MulAut.conj : G →* MulAut G)).codRestrict _ (by
    intro x
    change MulOpposite.op (MulAut.conj x⁻¹) • phi = phi
    apply Subtype.ext
    exact PrimeRegularClassFunction.twist_conj phi.1 x⁻¹)

def actualConjugation : ActualAutAmbient iota phi →* MulAut G :=
  (MulEquiv.inv' (MulAut G)).symm.toMonoidHom.comp
    (MulAction.stabilizer (MulAut G)ᵐᵒᵖ phi).subtype

theorem actualConjugation_injective :
    Function.Injective (actualConjugation iota phi) :=
  (MulEquiv.inv' (MulAut G)).symm.injective.comp Subtype.val_injective

theorem actualConjugation_inner (x : G) :
    actualConjugation iota phi (innerEmbedding iota phi x) = MulAut.conj x := by
  change (MulAut.conj x⁻¹)⁻¹ = MulAut.conj x
  rw [map_inv, inv_inv]

theorem innerEmbedding_conjugation (a : ActualAutAmbient iota phi) (x : G) :
    innerEmbedding iota phi (actualConjugation iota phi a x) =
      a * innerEmbedding iota phi x * a⁻¹ := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  ext y
  simp [innerEmbedding, actualConjugation, inverseOpHom, MulEquiv.inv', mul_assoc]

def actualBase : Subgroup (ActualAutAmbient iota phi) := (innerEmbedding iota phi).range

instance actualBaseNormal : (actualBase iota phi).Normal := by
  constructor
  intro b hb a
  obtain ⟨x, rfl⟩ := hb
  exact ⟨actualConjugation iota phi a x, innerEmbedding_conjugation iota phi a x⟩

theorem innerEmbedding_injective (hcenter : Subgroup.center G = ⊥) :
    Function.Injective (innerEmbedding iota phi) := by
  have hconj : Function.Injective (MulAut.conj : G →* MulAut G) :=
    (MonoidHom.ker_eq_bot_iff (MulAut.conj : G →* MulAut G)).mp
      ((conj_ker_eq_center (X := G)).trans hcenter)
  intro x y h
  apply hconj
  simpa only [actualConjugation_inner] using congrArg (actualConjugation iota phi) h

def actualBaseEquiv (hcenter : Subgroup.center G = ⊥) : G ≃* actualBase iota phi :=
  MulEquiv.ofBijective (innerEmbedding iota phi).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (innerEmbedding_injective iota phi hcenter),
      MonoidHom.rangeRestrict_surjective _⟩

theorem actualBase_centralizer_eq_bot (hcenter : Subgroup.center G = ⊥) :
    Subgroup.centralizer (actualBase iota phi : Set (ActualAutAmbient iota phi)) = ⊥ := by
  apply bot_unique
  intro a ha
  have hcomm : ∀ x : G,
      actualConjugation iota phi a * MulAut.conj x =
        MulAut.conj x * actualConjugation iota phi a := by
    intro x
    have h := Subgroup.mem_centralizer_iff.mp ha (innerEmbedding iota phi x) ⟨x, rfl⟩
    have hm := congrArg (actualConjugation iota phi) h.symm
    simpa only [map_mul, actualConjugation_inner] using hm
  have htrivial := mulAut_eq_one_of_commutes_inner hcenter (actualConjugation iota phi a) hcomm
  apply Subgroup.mem_bot.mpr
  apply actualConjugation_injective iota phi
  exact htrivial.trans (map_one _).symm

theorem actualAmbient_center_eq_bot (hcenter : Subgroup.center G = ⊥) :
    Subgroup.center (ActualAutAmbient iota phi) = ⊥ := by
  apply bot_unique
  exact (Subgroup.center_le_centralizer _).trans
    (actualBase_centralizer_eq_bot iota phi hcenter).le

def actualAutomorphismQuotientEquiv (hcenter : Subgroup.center G = ⊥) :
    ActualAutAmbient iota phi ⧸ Subgroup.center (ActualAutAmbient iota phi) ≃*
      ActualAutAmbient iota phi :=
  (QuotientGroup.quotientMulEquivOfEq (actualAmbient_center_eq_bot iota phi hcenter)).trans
    QuotientGroup.quotientBot

theorem actualAutomorphismQuotientEquiv_mk (hcenter : Subgroup.center G = ⊥)
    (a : ActualAutAmbient iota phi) :
    actualAutomorphismQuotientEquiv iota phi hcenter
      (QuotientGroup.mk' (Subgroup.center (ActualAutAmbient iota phi)) a) = a := by
  change QuotientGroup.quotientBot
    (QuotientGroup.quotientMulEquivOfEq (actualAmbient_center_eq_bot iota phi hcenter)
      (QuotientGroup.mk a)) = a
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem actualAutomorphismQuotientEquiv_natural (hcenter : Subgroup.center G = ⊥)
    (a : ActualAutAmbient iota phi) :
    (actualAutomorphismQuotientEquiv iota phi hcenter
      (QuotientGroup.mk' (Subgroup.center (ActualAutAmbient iota phi)) a)).1 =
        inverseOpHom (actualConjugation iota phi) a := by
  rw [actualAutomorphismQuotientEquiv_mk]
  change a.1 = MulOpposite.op (a.1.unop⁻¹)⁻¹
  simp only [inv_inv, MulOpposite.op_unop]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
