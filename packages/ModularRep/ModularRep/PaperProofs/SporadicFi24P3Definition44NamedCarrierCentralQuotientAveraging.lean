import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
import ModularRep.CentralCharacterBlockSector
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Averaging recovers the trivial sector from the quotient image

An internal linear lift of quotient group algebra elements recovers the
product with the trivial central idempotent. In particular every nonzero
primitive in that sector has nonzero quotient image.
-/

noncomputable section
open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientAveraging

open ModularRep
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

universe u
variable {k G : Type u} [Field k] [Group G]

theorem single_mul_trivialCentralIdempotent
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)] (z : Z) :
    MonoidAlgebra.single (z : G) (1 : k) * centralCharacterIdempotent Z (1 : Z →* kˣ) =
      centralCharacterIdempotent Z (1 : Z →* kˣ) := by
  classical
  have hs : MonoidAlgebra.single (z : G) (1 : k) *
      linearCharacterWeightedSum Z (1 : Z →* kˣ) =
        linearCharacterWeightedSum Z (1 : Z →* kˣ) := by
    simpa [linearCharacterWeightedSum, Finset.mul_sum] using
      Equiv.sum_comp (Equiv.mulLeft z)
        (fun w : Z => MonoidAlgebra.single (w : G) (1 : k))
  simpa only [centralCharacterIdempotent, mul_smul_comm] using
    congrArg (fun b : k[G] => ⅟(Fintype.card Z : k) • b) hs

theorem mul_trivialCentralIdempotent_eq_zero_of_quotient_image_eq_zero
    (Z : Subgroup G) [Z.Normal] [Fintype Z] [Invertible (Fintype.card Z : k)]
    {a : k[G]} (ha : algebraMapOf (QuotientGroup.mk' Z) a = 0) :
    a * centralCharacterIdempotent Z (1 : Z →* kˣ) = 0 := by
  classical
  let q := QuotientGroup.mk' Z
  let e : k[G] := centralCharacterIdempotent Z (1 : Z →* kˣ)
  have hcoset (x y : G) (h : q x = q y) :
      MonoidAlgebra.single x (1 : k) * e = MonoidAlgebra.single y (1 : k) * e := by
    obtain ⟨z, hz, rfl⟩ := (QuotientGroup.mk'_eq_mk' Z).mp h
    have hzfix : MonoidAlgebra.single z (1 : k) * e = e :=
      single_mul_trivialCentralIdempotent Z ⟨z, hz⟩
    calc
      MonoidAlgebra.single x (1 : k) * e =
          MonoidAlgebra.single x (1 : k) * (MonoidAlgebra.single z (1 : k) * e) := by
        rw [hzfix]
      _ = MonoidAlgebra.single (x * z) (1 : k) * e := by
        rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]
  let r : G ⧸ Z → G := fun x => Classical.choose (QuotientGroup.mk'_surjective Z x)
  have hr (x : G ⧸ Z) : q (r x) = x :=
    Classical.choose_spec (QuotientGroup.mk'_surjective Z x)
  let T : k[G ⧸ Z] →+ k[G] :=
    MonoidAlgebra.liftNC (algebraMap k k[G]).toAddMonoidHom
      (fun x => MonoidAlgebra.single (r x) (1 : k) * e)
  have hT (b : k[G]) : T (algebraMapOf q b) = b * e := by
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc => simp only [map_add, add_mul, hb, hc]
    | single g c =>
        calc
          T (algebraMapOf q (MonoidAlgebra.single g c)) =
              algebraMap k k[G] c * (MonoidAlgebra.single (r (q g)) (1 : k) * e) := by
            simp only [algebraMapOf_single, T, MonoidAlgebra.liftNC_single]
            rfl
          _ = algebraMap k k[G] c * (MonoidAlgebra.single g (1 : k) * e) := by
            rw [hcoset (r (q g)) g (hr (q g))]
          _ = MonoidAlgebra.single g c * e := by
            rw [← mul_assoc]
            exact congrArg (fun x : k[G] => x * e)
              (MonoidAlgebra.single_eq_algebraMap_mul_of g c).symm
  have h := hT a
  rw [ha, map_zero] at h
  exact h.symm

theorem quotient_image_ne_zero_of_trivial_sector
    (Z : Subgroup G) [Z.Normal] [Fintype Z] [Invertible (Fintype.card Z : k)]
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (hsector : IsCentralCharacterSector Z b (1 : Z →* kˣ)) :
    algebraMapOf (QuotientGroup.mk' Z) b ≠ 0 := by
  intro hzero
  have havg := mul_trivialCentralIdempotent_eq_zero_of_quotient_image_eq_zero Z hzero
  exact hb.ne_zero (hsector.mul_eq_self.symm.trans havg)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientAveraging


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
