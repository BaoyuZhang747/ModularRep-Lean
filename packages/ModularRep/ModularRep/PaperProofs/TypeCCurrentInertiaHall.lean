import ModularRep.PaperProofs.TypeCOddPrimeConformalCriterionCarriers
import Mathlib.GroupTheory.Index

/-!
The original subgroup and same-weight inertia proof is retained with its
actual characteristic-zero coefficient hypotheses. No algebraic closure of
the ordinary fraction field and no inertia-product source are introduced.

# Actual Type C inertia / Hall products at odd coefficient primes

Both inertias below are the criterion's OWN actual M-inertias for the
computed CSp/Sp/field action. Inner Sp and central CSp elements fix Brauer
characters and weight CONJUGACY CLASSES. Hence both inertias contain the
actual Sp range joined with the centre.

The only new structural E1 input is that this subgroup's index divides
two, from the multiplier and scalar-square dictionary. The actual Hall
preimage has ell-power index and is normal because CSp/Sp is cyclic.
Coprime indices then prove both products equal the whole CSp group.
No J_G equality, matching, covering relation or product conclusion is a
source input. This is the K subgroup argument behind Li Remark 2.2(1).
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeCCurrentInertiaHall

open ModularRep
open TypeBCriterionHypotheses TypeCOddPrimeConformalCriterionCarriers
open OddTwoConformalProjectiveRealisation (CSp)
open CyclicOuterLemma37Concrete

section IndexArgument

variable {A : Type*} [Group A]

/-- A generic coprime-index calculation, independent of a classical group. -/
theorem join_eq_top_of_index_dvd_two {ell a : ℕ} (hOdd : Odd ell)
    (base inertia hall : Subgroup A) (hbase : base.index ∣ 2)
    (hcontains : base ≤ inertia) (hhall : hall.index = ell ^ a) :
    inertia ⊔ hall = ⊤ := by
  apply Subgroup.index_eq_one.mp
  have htwo : (inertia ⊔ hall).index ∣ 2 :=
    (Subgroup.index_dvd_of_le (hcontains.trans le_sup_left)).trans hbase
  have hpower : (inertia ⊔ hall).index ∣ ell ^ a := by
    rw [← hhall]
    exact Subgroup.index_dvd_of_le le_sup_right
  exact Nat.eq_one_of_dvd_coprimes (hOdd.coprime_two_left.pow_right a) htwo hpower

end IndexArgument

variable (n : ℕ) (F : Type) [Field F] [Finite F]
variable [(SpSubgroup n F).Normal]

/-- Restrict the actual criterion action to its CSp factor. -/
theorem conjugation_on_M :
    (inverseOpHom (naturalAction n F).hom).comp SemidirectProduct.inl =
      inverseOpHom (MulAut.conjNormal (H := SpSubgroup n F)) := by
  apply MonoidHom.ext
  intro m
  change MulOpposite.op (ambientAutomorphism n F
      ((SemidirectProduct.inl m)⁻¹)) =
    MulOpposite.op (MulAut.conjNormal (H := SpSubgroup n F) m⁻¹)
  rw [← map_inv]
  exact congrArg MulOpposite.op (ambientAutomorphism_inl n F m⁻¹)

/-- Central ambient elements induce the identity on the same actual Sp
range. This is a group calculation, not a sourced action statement. -/
theorem central_conjNormal_eq_one {g : CSp n F}
    (hg : g ∈ Subgroup.center (CSp n F)) :
    MulAut.conjNormal (H := SpSubgroup n F) g = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change g * (x : CSp n F) * g⁻¹ = x
  have hc : g * (x : CSp n F) = (x : CSp n F) * g :=
    ((Subgroup.mem_center_iff.mp hg) (x : CSp n F)).symm
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

section Characters

variable {ell : ℕ} {k K : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k]
variable [CharZero K]
variable (iota : PrimeRegularRootEmbedding ell k K (SpSubgroup n F))

/-- The actual generic criterion inertia; no second action is defined. -/
abbrev BrauerInertia (phi : IBr iota) : Subgroup (CSp n F) :=
  brauerMInertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iota phi

/-- Weight inertia is on the ambient conjugacy class, not the raw pair. -/
abbrev WeightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := SpSubgroup n F)) : Subgroup (CSp n F) :=
  weightMInertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W

theorem mem_BrauerInertia (phi : IBr iota) (g : CSp n F) :
    g ∈ BrauerInertia n F iota phi ↔
      IrreducibleBrauerCharacter.twist iota phi
        (MulAut.conjNormal (H := SpSubgroup n F) g⁻¹) = phi := by
  change ((inverseOpHom (naturalAction n F).hom).comp
    SemidirectProduct.inl) g • phi = phi ↔ _
  rw [conjugation_on_M n F]
  rfl

theorem mem_WeightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := SpSubgroup n F)) (g : CSp n F) :
    g ∈ WeightInertia n F W ↔
      CharacterWeight.rightTwistConjugacyClass
        (MulAut.conjNormal (H := SpSubgroup n F) g⁻¹) W = W := by
  change ((inverseOpHom (naturalAction n F).hom).comp
    SemidirectProduct.inl) g • W = W ↔ _
  rw [conjugation_on_M n F]
  rfl

theorem sp_le_BrauerInertia (phi : IBr iota) :
    SpSubgroup n F ≤ BrauerInertia n F iota phi := by
  intro g hg
  rw [mem_BrauerInertia]
  let h : SpSubgroup n F := ⟨g, hg⟩
  have hc : MulAut.conjNormal (H := SpSubgroup n F) g⁻¹ =
      MulAut.conj h⁻¹ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  rw [hc]
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact PrimeRegularClassFunction.twist_conj phi.1 h⁻¹

theorem center_le_BrauerInertia (phi : IBr iota) :
    Subgroup.center (CSp n F) ≤ BrauerInertia n F iota phi := by
  intro g hg
  rw [mem_BrauerInertia,
    central_conjNormal_eq_one n F ((Subgroup.center (CSp n F)).inv_mem hg)]
  exact IrreducibleBrauerCharacter.twist_refl iota phi

theorem sp_center_le_BrauerInertia (phi : IBr iota) :
    SpSubgroup n F ⊔ Subgroup.center (CSp n F) ≤ BrauerInertia n F iota phi :=
  sup_le (sp_le_BrauerInertia n F iota phi) (center_le_BrauerInertia n F iota phi)

theorem sp_le_WeightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := SpSubgroup n F)) :
    SpSubgroup n F ≤ WeightInertia n F W := by
  intro g hg
  rw [mem_WeightInertia]
  let h : SpSubgroup n F := ⟨g, hg⟩
  have hc : MulAut.conjNormal (H := SpSubgroup n F) g⁻¹ =
      MulAut.conj h⁻¹ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  rw [hc]
  have hfixed := inner_fixes_weightClass (p := ell) (K := K)
    (H := SpSubgroup n F) h W
  change CharacterWeight.rightTwistConjugacyClass (MulAut.conj h⁻¹) W = W at hfixed
  exact hfixed

theorem center_le_WeightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := SpSubgroup n F)) :
    Subgroup.center (CSp n F) ≤ WeightInertia n F W := by
  intro g hg
  rw [mem_WeightInertia,
    central_conjNormal_eq_one n F ((Subgroup.center (CSp n F)).inv_mem hg)]
  exact CharacterWeight.rightTwistConjugacyClass_one W

theorem sp_center_le_WeightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := SpSubgroup n F)) :
    SpSubgroup n F ⊔ Subgroup.center (CSp n F) ≤ WeightInertia n F W :=
  sup_le (sp_le_WeightInertia n F W) (center_le_WeightInertia n F W)

end Characters

section Hall

variable {ell : ℕ}
variable (cyclic : IsCyclic (CSp n F ⧸ SpSubgroup n F))
variable (hall : HallData (SpSubgroup n F) ell)

include cyclic in
/-- Normality is derived for the criterion's same Hall preimage. -/
theorem hallPreimage_normal : hall.preimage.Normal := by
  letI := cyclic
  change (hall.hall.comap (QuotientGroup.mk' (SpSubgroup n F))).Normal
  infer_instance

theorem hallPreimage_index : hall.preimage.index = ell ^ hall.exponent := by
  exact (hall.hall.index_comap_of_surjective
    (f := QuotientGroup.mk' (SpSubgroup n F))
    (QuotientGroup.mk'_surjective (SpSubgroup n F))).trans hall.index

theorem sp_le_hallPreimage : SpSubgroup n F ≤ hall.preimage := by
  intro g hg
  change (g : CSp n F ⧸ SpSubgroup n F) ∈ hall.hall
  rw [(QuotientGroup.eq_one_iff g).mpr hg]
  exact hall.hall.one_mem

end Hall

section Products

variable {ell : ℕ} {k K : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k]
variable [CharZero K]
variable (iota : PrimeRegularRootEmbedding ell k K (SpSubgroup n F))
variable (hOdd : Odd ell)
variable (index_dvd_two :
  (SpSubgroup n F ⊔ Subgroup.center (CSp n F)).index ∣ 2)
variable (cyclic : IsCyclic (CSp n F ⧸ SpSubgroup n F))
variable (hall : HallData (SpSubgroup n F) ell)

include hOdd index_dvd_two in
theorem brauerInertia_sup_hall_eq_top (phi : IBr iota) :
    BrauerInertia n F iota phi ⊔ hall.preimage = ⊤ :=
  join_eq_top_of_index_dvd_two hOdd
    (SpSubgroup n F ⊔ Subgroup.center (CSp n F))
    (BrauerInertia n F iota phi) hall.preimage index_dvd_two
    (sp_center_le_BrauerInertia n F iota phi) (hallPreimage_index n F hall)

include hOdd index_dvd_two in
theorem weightInertia_sup_hall_eq_top
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := SpSubgroup n F)) :
    WeightInertia n F W ⊔ hall.preimage = ⊤ :=
  join_eq_top_of_index_dvd_two hOdd
    (SpSubgroup n F ⊔ Subgroup.center (CSp n F))
    (WeightInertia n F W) hall.preimage index_dvd_two
    (sp_center_le_WeightInertia n F W) (hallPreimage_index n F hall)

include hOdd index_dvd_two cyclic in
theorem brauerInertia_mul_hall_eq_univ (phi : IBr iota) :
    (BrauerInertia n F iota phi : Set (CSp n F)) *
      (hall.preimage : Set (CSp n F)) = Set.univ := by
  letI := hallPreimage_normal n F cyclic hall
  rw [← Subgroup.mul_normal,
    brauerInertia_sup_hall_eq_top n F iota hOdd index_dvd_two hall phi]
  rfl

include hOdd index_dvd_two cyclic in
theorem weightInertia_mul_hall_eq_univ
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K)
      (G := SpSubgroup n F)) :
    (WeightInertia n F W : Set (CSp n F)) *
      (hall.preimage : Set (CSp n F)) = Set.univ := by
  letI := hallPreimage_normal n F cyclic hall
  rw [← Subgroup.mul_normal,
    weightInertia_sup_hall_eq_top n F hOdd index_dvd_two hall W]
  rfl

include hOdd index_dvd_two cyclic in
/-- Both products are the whole CSp group for EVERY actual character and
weight class. No matching or published J_G conclusion is assumed. -/
theorem allPairsJG :
    AllPairsJG (SpSubgroup n F) (fieldAction n F) (naturalAction n F)
      iota hall := by
  intro phi W
  exact (brauerInertia_mul_hall_eq_univ n F iota hOdd index_dvd_two cyclic hall phi).trans
    (weightInertia_mul_hall_eq_univ n F hOdd index_dvd_two cyclic hall W).symm

end Products

end ModularRep.PaperProofs.TypeCCurrentInertiaHall


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
