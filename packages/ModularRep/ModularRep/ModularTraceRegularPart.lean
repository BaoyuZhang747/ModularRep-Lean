import ModularRep.PrimeRegularPart
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.RepresentationTheory.Character

/-!
# Modular traces and prime regular parts

For a finite group representation over a field of characteristic `p`, the
trace of an element is the trace of its canonical `p`-regular part.  The
`p`-primary factor acts as a unipotent endomorphism.  Since it commutes with
the regular factor, its nilpotent part does not change the trace of their
product.

This is the characteristic-`p` trace calculation used in Navarro,
*Characters and Blocks of Finite Groups*, Lemma (2.4), printed p. 19.
-/

noncomputable section

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V]
variable {p : ℕ} [CharP k p]

/-- In characteristic `p`, the character of a finite-order representation
depends only on the canonical `p`-regular part of the group element. -/
theorem character_eq_character_primeRegularPart
    (hp : p.Prime) (rho : Representation k G V) (g : G) :
    rho.character g =
      rho.character (ModularRep.primeRegularPart hp g) := by
  by_cases hV : Nontrivial V
  swap
  · let _ : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    unfold character
    rw [show rho g = rho (ModularRep.primeRegularPart hp g) from
      Subsingleton.elim _ _]
  let _ : Nontrivial V := hV
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let _ : CharP (Module.End k V) p := Module.charP_end
    ⟨v, (Ideal.torsionOf_eq_bot_iff_of_noZeroSMulDivisors k v).2 hv⟩
  let P : Module.End k V :=
    rho (ModularRep.primePart hp g)
  let R : Module.End k V :=
    rho (ModularRep.primeRegularPart hp g)
  have hPR : Commute P R :=
    (ModularRep.commute_primePart_primeRegularPart hp g).map rho
  have hPpow : P ^ ModularRep.primaryOrderPart p g = 1 := by
    have hgroup := ModularRep.primePart_pow_primaryOrderPart hp g
    have hend := congrArg (fun x : G ↦ rho x) hgroup
    simpa [P] using hend
  have hnil : IsNilpotent (P - 1) := by
    refine ⟨ModularRep.primaryOrderPart p g, ?_⟩
    have hfresh := sub_pow_char_pow_of_commute p
      ((orderOf g).factorization p) (Commute.one_right P)
    rw [← ModularRep.primaryOrderPart] at hfresh
    rw [hPpow, one_pow, sub_self] at hfresh
    exact hfresh
  have htrace := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent
    (R := k) (M := V) (1 : k) hPR.symm (by simpa using hnil)
  have hdecomp :
      ModularRep.primeRegularPart hp g * ModularRep.primePart hp g = g := by
    calc
      ModularRep.primeRegularPart hp g * ModularRep.primePart hp g =
          ModularRep.primePart hp g * ModularRep.primeRegularPart hp g :=
        (ModularRep.commute_primePart_primeRegularPart hp g).eq.symm
      _ = g := ModularRep.primePart_mul_primeRegularPart hp g
  calc
    rho.character g = rho.character
        (ModularRep.primeRegularPart hp g * ModularRep.primePart hp g) :=
      congrArg rho.character hdecomp.symm
    _ = rho.character (ModularRep.primeRegularPart hp g) := by
      rw [character, map_mul]
      simpa [P, R, Module.End.mul_eq_comp, character] using htrace

end Representation



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
