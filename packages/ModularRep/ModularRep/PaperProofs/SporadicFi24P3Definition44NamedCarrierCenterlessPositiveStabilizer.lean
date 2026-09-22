import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

/-! Spath's automorphism quotient with the positive conjugation action.
Membership is proved equivalent to literal Brauer twist-fixedness. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessPositiveStabilizer
open ModularRep
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)

def positiveBrauerStabilizer : Subgroup (MulAut G) := (actualConjugation iota phi).range

theorem mem_positiveBrauerStabilizer (alpha : MulAut G) :
    alpha ∈ positiveBrauerStabilizer iota phi ↔
      IrreducibleBrauerCharacter.twist iota phi alpha = phi := by
  constructor
  · rintro ⟨a, rfl⟩
    change MulOpposite.op (a.val.unop⁻¹) • phi = phi
    exact (a⁻¹).property
  · intro hfixed
    have hop : MulOpposite.op alpha • phi = phi := hfixed
    let a : ActualAutAmbient iota phi :=
      ⟨(MulOpposite.op alpha)⁻¹,
        (MulAction.stabilizer (MulAut G)ᵐᵒᵖ phi).inv_mem hop⟩
    refine ⟨a, ?_⟩
    change (alpha⁻¹)⁻¹ = alpha
    exact inv_inv alpha

def actualPositiveStabilizerEquiv :
    ActualAutAmbient iota phi ≃* positiveBrauerStabilizer iota phi :=
  MulEquiv.ofBijective (actualConjugation iota phi).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (actualConjugation_injective iota phi),
      MonoidHom.rangeRestrict_surjective _⟩

theorem actualPositiveStabilizerEquiv_apply (a : ActualAutAmbient iota phi) :
    (actualPositiveStabilizerEquiv iota phi a).val = actualConjugation iota phi a := rfl

local notation "A" => ActualAutAmbient iota phi
local notation "B" => actualBase iota phi
local notation "C" => Subgroup.centralizer (B : Set A)

def centralizerPositiveStabilizerEquiv (hcenter : Subgroup.center G = ⊥) :
    A ⧸ C ≃* positiveBrauerStabilizer iota phi :=
  ((QuotientGroup.quotientMulEquivOfEq (actualBase_centralizer_eq_bot iota phi hcenter)).trans
    QuotientGroup.quotientBot).trans (actualPositiveStabilizerEquiv iota phi)

theorem centralizerPositiveStabilizerEquiv_mk (hcenter : Subgroup.center G = ⊥) (a : A) :
    centralizerPositiveStabilizerEquiv iota phi hcenter (QuotientGroup.mk' C a) =
      actualPositiveStabilizerEquiv iota phi a := by
  change actualPositiveStabilizerEquiv iota phi
    (QuotientGroup.quotientBot
      (QuotientGroup.quotientMulEquivOfEq (actualBase_centralizer_eq_bot iota phi hcenter)
        (QuotientGroup.mk a))) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem centralizerPositiveStabilizerEquiv_conjugation
    (hcenter : Subgroup.center G = ⊥) (a : A) (x : G) :
    innerEmbedding iota phi
      ((centralizerPositiveStabilizerEquiv iota phi hcenter (QuotientGroup.mk' C a)).val x) =
      a * innerEmbedding iota phi x * a⁻¹ := by
  rw [centralizerPositiveStabilizerEquiv_mk]
  exact innerEmbedding_conjugation iota phi a x

theorem centerless_ambient_geometry (hcenter : Subgroup.center G = ⊥) :
    (B).Normal ∧ C = Subgroup.center A ∧ ¬ p ∣ Nat.card (Subgroup.center A) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [actualBase_centralizer_eq_bot iota phi hcenter,
      actualAmbient_center_eq_bot iota phi hcenter]
  · rw [actualAmbient_center_eq_bot iota phi hcenter, Subgroup.card_bot]
    exact iota.prime.not_dvd_one

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessPositiveStabilizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
