import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientSignAlgebra
import ModularRep.BrauerCharacter

/-! Negating an operator negates its characteristic-polynomial roots,
including their multiplicities. This supplies the eigenvalue calculation
for the actual quotient-sign representation. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNegatedCharpoly

theorem charpoly_neg
    {k V : Type*} [Field k] [Infinite k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : Module.End k V) :
    (-f).charpoly = (-1 : k) ^ Module.finrank k V • f.charpoly.comp (-Polynomial.X) := by
  apply Polynomial.funext
  intro x
  have h : algebraMap k (Module.End k V) x - -f =
      (-1 : k) • (algebraMap k (Module.End k V) (-x) - f) := by
    simp [add_comm]
  simp only [LinearMap.eval_charpoly, Polynomial.eval_smul, Polynomial.eval_comp,
    Polynomial.eval_neg, Polynomial.eval_X, smul_eq_mul]
  rw [h, LinearMap.det_smul]

theorem roots_charpoly_neg
    {k V : Type*} [Field k] [Infinite k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : Module.End k V) :
    (-f).charpoly.roots = f.charpoly.roots.map (fun a => -a) := by
  rw [charpoly_neg, Polynomial.roots_smul_nonzero _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
    Polynomial.roots_comp_neg_X]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNegatedCharpoly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
