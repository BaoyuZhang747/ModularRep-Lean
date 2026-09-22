import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement
import Mathlib.GroupTheory.GroupExtension.Basic

/-! The original, possibly nonsplit, extension in the centre-two replacement
argument. Its centralizer is derived from the faithful outer action, and its
Brauer stabilizer retains the original group as an injective subgroup. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms

universe u
variable {G T C : Type u} [Group G] [Group T] [Group C]
variable (E : GroupExtension G T C)

theorem conjAct_inl (x : G) : E.conjAct (E.inl x) = MulAut.conj x := by
  apply MulEquiv.ext
  intro y
  apply E.inl_injective
  rw [E.inl_conjAct_comm]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem inverseOp_conjAct_inl (x : G) :
    inverseOpHom E.conjAct (E.inl x) = RepresentationWeight.innerInverseOpHom x := by
  change MulOpposite.op (E.conjAct ((E.inl x)⁻¹)) =
    MulOpposite.op (MulAut.conj x⁻¹)
  rw [← map_inv, conjAct_inl]

def extensionOuterMap : T ⧸ E.inl.range →* LiteralOuterQuotient G :=
  QuotientGroup.lift E.inl.range
    ((QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range).comp
      (inverseOpHom E.conjAct)) (by
        rintro _ ⟨x, rfl⟩
        change QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range
          (inverseOpHom E.conjAct (E.inl x)) = 1
        rw [inverseOp_conjAct_inl]
        exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩)

theorem extensionOuterMap_surjective (hAut : Function.Surjective E.conjAct) :
    Function.Surjective (extensionOuterMap E) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    (RepresentationWeight.innerInverseOpHom (G := G)).range q
  obtain ⟨t, ht⟩ := hAut a.unop⁻¹
  refine ⟨QuotientGroup.mk' E.inl.range t, ?_⟩
  change QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range
    (inverseOpHom E.conjAct t) = QuotientGroup.mk' _ a
  congr 1
  apply MulOpposite.unop_injective
  change E.conjAct t⁻¹ = a.unop
  rw [map_inv, ht, inv_inv]

theorem extensionOuterMap_injective
    (hC : Nat.card C = 2) (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (hAut : Function.Surjective E.conjAct) :
    Function.Injective (extensionOuterMap E) := by
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; decide)
  let : Finite (T ⧸ E.inl.range) :=
    Finite.of_equiv C E.quotientRangeInlEquivRight.symm.toEquiv
  have hcard : Nat.card (T ⧸ E.inl.range) = Nat.card (LiteralOuterQuotient G) :=
    (Nat.card_congr E.quotientRangeInlEquivRight.toEquiv).trans (hC.trans hOuter.symm)
  exact ((Nat.bijective_iff_surjective_and_card (extensionOuterMap E)).mpr
    ⟨extensionOuterMap_surjective E hAut, hcard⟩).1

theorem conjAct_ker_le_base
    (hC : Nat.card C = 2) (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (hAut : Function.Surjective E.conjAct) : E.conjAct.ker ≤ E.inl.range := by
  intro a ha
  apply (QuotientGroup.eq_one_iff _).mp
  apply extensionOuterMap_injective E hC hOuter hAut
  change QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range
    (inverseOpHom E.conjAct a) = extensionOuterMap E 1
  rw [map_one]
  have h : inverseOpHom E.conjAct a = 1 := by
    change MulOpposite.op (E.conjAct a⁻¹) = 1
    rw [map_inv, show E.conjAct a = 1 from ha, inv_one]
    rfl
  rw [h, map_one]

theorem aut_fixes_center_of_card_two (hZ : Nat.card (Subgroup.center G) = 2)
    (alpha : MulAut G) (z : Subgroup.center G) : alpha z.1 = z.1 := by
  classical
  by_cases hz : z = 1
  · subst z
    exact alpha.map_one
  let az : Subgroup.center G := ⟨alpha z.1, by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := alpha.surjective y
    simpa only [map_mul] using congrArg alpha (Subgroup.mem_center_iff.mp z.2 x)⟩
  have haz : az ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply alpha.injective
    exact (congrArg Subtype.val h).trans alpha.map_one.symm
  exact congrArg Subtype.val
    (((Nat.card_eq_two_iff' (1 : Subgroup.center G)).mp hZ).unique haz hz)

include E in
theorem extension_finite [Finite G] (hC : Nat.card C = 2) : Finite T := by
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; decide)
  have hf : Finite E.inl.range := Finite.of_surjective
    E.inl.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have hk : Finite E.rightHom.ker := E.range_inl_eq_ker_rightHom ▸ hf
  exact (MonoidHom.finite_iff_finite_ker_range E.rightHom).mpr ⟨hk, inferInstance⟩

variable {p : ℕ} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [Finite G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)

abbrev brauerAmbient : Subgroup T :=
  (MulAction.stabilizer (MulAut G)ᵐᵒᵖ phi).comap (inverseOpHom E.conjAct)

def brauerEmbedding : G →* brauerAmbient E iota phi :=
  E.inl.codRestrict _ (by
    intro x
    change inverseOpHom E.conjAct (E.inl x) • phi = phi
    rw [inverseOp_conjAct_inl]
    exact (innerEmbedding iota phi x).2)

theorem brauerEmbedding_injective : Function.Injective (brauerEmbedding E iota phi) := by
  intro x y h
  exact E.inl_injective (congrArg Subtype.val h)

def brauerAction : brauerAmbient E iota phi →* ActualAutAmbient iota phi :=
  ((inverseOpHom E.conjAct).comp (brauerAmbient E iota phi).subtype).codRestrict _
    (fun a => a.2)

theorem brauerAction_surjective (hAut : Function.Surjective E.conjAct) :
    Function.Surjective (brauerAction E iota phi) := by
  intro a
  obtain ⟨t, ht⟩ := hAut a.1.unop⁻¹
  have hop : inverseOpHom E.conjAct t = a.1 := by
    apply MulOpposite.unop_injective
    change E.conjAct t⁻¹ = a.1.unop
    rw [map_inv, ht, inv_inv]
  have htA : t ∈ brauerAmbient E iota phi := by
    change inverseOpHom E.conjAct t • phi = phi
    rw [hop]
    exact a.2
  refine ⟨⟨t, htA⟩, ?_⟩
  apply Subtype.ext
  exact hop

theorem brauerAction_conjugation (a : brauerAmbient E iota phi) :
    actualConjugation iota phi (brauerAction E iota phi a) = E.conjAct a.1 := by
  change (E.conjAct a.1⁻¹)⁻¹ = E.conjAct a.1
  rw [map_inv, inv_inv]

theorem brauerEmbedding_conjugation (a : brauerAmbient E iota phi) (x : G) :
    brauerEmbedding E iota phi
        (actualConjugation iota phi (brauerAction E iota phi a) x) =
      a * brauerEmbedding E iota phi x * a⁻¹ := by
  apply Subtype.ext
  rw [brauerAction_conjugation]
  exact E.inl_conjAct_comm

def brauerProjection : brauerAmbient E iota phi →* C :=
  E.rightHom.comp (brauerAmbient E iota phi).subtype

theorem brauerEmbedding_range :
    (brauerEmbedding E iota phi).range = (brauerProjection E iota phi).ker := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact E.rightHom_inl x
  · intro ha
    obtain ⟨x, hx⟩ := E.range_inl_eq_ker_rightHom.ge ha
    exact ⟨x, Subtype.ext hx⟩

instance brauerBaseNormal : (brauerEmbedding E iota phi).range.Normal := by
  rw [brauerEmbedding_range]
  infer_instance

theorem brauerQuotient_cyclic (hC : Nat.card C = 2) :
    IsCyclic (brauerAmbient E iota phi ⧸ (brauerEmbedding E iota phi).range) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic C := isCyclic_of_prime_card hC
  let : IsCyclic (brauerAmbient E iota phi ⧸ (brauerProjection E iota phi).ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift (brauerProjection E iota phi))
      (QuotientGroup.kerLift_injective _)
  let e := QuotientGroup.quotientMulEquivOfEq (brauerEmbedding_range E iota phi)
  exact isCyclic_of_injective e.toMonoidHom e.injective

theorem brauerCentralizer_eq_center_map
    (hC : Nat.card C = 2) (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (hAut : Function.Surjective E.conjAct) :
    Subgroup.centralizer ((brauerEmbedding E iota phi).range : Set _) =
      (Subgroup.center G).map (brauerEmbedding E iota phi) := by
  ext a
  constructor
  · intro ha
    have hc : E.conjAct a.1 = 1 := by
      apply MulEquiv.ext
      intro x
      apply E.inl_injective
      rw [E.inl_conjAct_comm]
      have hx := Subgroup.mem_centralizer_iff.mp ha
        (brauerEmbedding E iota phi x) ⟨x, rfl⟩
      have hx' := congrArg Subtype.val hx
      change E.inl x * a.1 = a.1 * E.inl x at hx'
      change a.1 * E.inl x * a.1⁻¹ = E.inl x
      rw [← hx', mul_inv_cancel_right]
    obtain ⟨x, hx⟩ := conjAct_ker_le_base E hC hOuter hAut (show a.1 ∈ E.conjAct.ker from hc)
    have hxz : x ∈ Subgroup.center G := by
      rw [← conj_ker_eq_center]
      change MulAut.conj x = 1
      rw [← conjAct_inl E, hx, hc]
    exact ⟨x, hxz, Subtype.ext hx⟩
  · rintro ⟨z, hz, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro b ⟨x, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]

theorem brauerCenterMap_central (hZ : Nat.card (Subgroup.center G) = 2) :
    (Subgroup.center G).map (brauerEmbedding E iota phi) ≤
      Subgroup.center (brauerAmbient E iota phi) := by
  rintro _ ⟨z, hz, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro a
  have h := brauerEmbedding_conjugation E iota phi a z
  rw [aut_fixes_center_of_card_two hZ _ ⟨z, hz⟩] at h
  exact (eq_mul_inv_iff_mul_eq.mp h).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
