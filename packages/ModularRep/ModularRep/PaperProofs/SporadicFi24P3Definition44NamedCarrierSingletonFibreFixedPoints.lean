import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNumericalOrbitAssembly

/-! Fixed points are derived from invariant singleton intersections of
two equivariant labels. Two such intersections determine the fixed count
of an actual three-point involution fibre. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingletonFibreFixedPoints

open ModularRep.BlockFibreRestriction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNumericalOrbitAssembly

universe u

variable {A B R W : Type u}
variable [Group A] [MulAction A B] [MulAction A R] [MulAction A W]

theorem exists_fixed_of_singleton_joint_fibre
    (block : W → B) (label : W → R)
    (hblock : ∀ (a : A) (w : W), block (a • w) = a • block w)
    (hlabel : ∀ (a : A) (w : W), label (a • w) = a • label w)
    (t : A) (b : B) (r : R)
    (hb : t • b = b) (hr : t • r = r)
    (hcard : Nat.card {w : W // block w = b ∧ label w = r} = 1) :
    ∃ w : W, block w = b ∧ label w = r ∧ t • w = w := by
  obtain ⟨w, hunique⟩ := Nat.card_eq_one_iff_exists.mp hcard
  refine ⟨w.1, w.2.1, w.2.2, ?_⟩
  let w' : {w : W // block w = b ∧ label w = r} := ⟨t • w.1, by
    constructor
    · rw [hblock, w.2.1, hb]
    · rw [hlabel, w.2.2, hr]⟩
  exact congrArg Subtype.val (hunique w')

theorem fixed_card_three_of_two_singleton_labels
    (block : W → B) (label : W → R)
    (hblock : ∀ (a : A) (w : W), block (a • w) = a • block w)
    (hlabel : ∀ (a : A) (w : W), label (a • w) = a • label w)
    (t : A) (ht : Function.Involutive (fun w : W => t • w))
    (b : B) (ra rb : R)
    (hb : t • b = b) (hra : t • ra = ra) (hrb : t • rb = rb)
    (hne : ra ≠ rb)
    (hrowa : Nat.card {w : W // block w = b ∧ label w = ra} = 1)
    (hrowb : Nat.card {w : W // block w = b ∧ label w = rb} = 1)
    (htotal : Nat.card (BlockFibre block b) = 3) :
    Nat.card {w : W // block w = b ∧ t • w = w} = 3 := by
  classical
  obtain ⟨wa, hwaB, hwaR, hwaT⟩ :=
    exists_fixed_of_singleton_joint_fibre block label hblock hlabel t b ra hb hra hrowa
  obtain ⟨wb, hwbB, hwbR, hwbT⟩ :=
    exists_fixed_of_singleton_joint_fibre block label hblock hlabel t b rb hb hrb hrowb
  let : Finite (BlockFibre block b) :=
    Nat.finite_of_card_ne_zero (by rw [htotal]; decide)
  let : Fintype (BlockFibre block b) := Fintype.ofFinite _
  let sigma := fibrePerm block hblock t b hb
  have hsigma : Function.Involutive sigma := by
    intro w
    apply Subtype.ext
    exact ht w.1
  let x : Function.fixedPoints sigma := ⟨⟨wa, hwaB⟩, Subtype.ext hwaT⟩
  let y : Function.fixedPoints sigma := ⟨⟨wb, hwbB⟩, Subtype.ext hwbT⟩
  have hxy : x ≠ y := by
    intro h
    have hw : wa = wb := congrArg (fun v : Function.fixedPoints sigma => v.1.1) h
    exact hne (hwaR.symm.trans ((congrArg label hw).trans hwbR))
  have htwo : 1 < Fintype.card (Function.fixedPoints sigma) :=
    Fintype.one_lt_card_iff.mpr ⟨x, y, hxy⟩
  have hthree : Fintype.card (BlockFibre block b) = 3 := by
    simpa only [Nat.card_eq_fintype_card] using htotal
  have hformula := Formalisation.C2Cancellation.card_eq_fixed_add_twice_cycleCount sigma hsigma
  have hfixed : Fintype.card (Function.fixedPoints sigma) = 3 := by omega
  calc
    Nat.card {w : W // block w = b ∧ t • w = w} =
        Nat.card (Function.fixedPoints sigma) :=
      (Nat.card_congr (fixedFibreActionEquiv block hblock t b hb)).symm
    _ = 3 := by simpa only [Nat.card_eq_fintype_card] using hfixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingletonFibreFixedPoints


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
