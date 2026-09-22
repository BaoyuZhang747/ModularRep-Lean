import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Modular systems

This file packages the coefficient-ring data of a complete `p`-modular
system.  It does not assert that either field is a splitting field for a
particular group, and it does not construct the cross-characteristic
correspondence between roots of unity.  Those are separate mathematical
inputs.
-/

namespace ModularRep

universe uK uO uk

/-- A complete `p`-modular system `(K, O, k)` at the coefficient-ring level.

Here `O` is a complete discrete valuation ring, `K` is its fraction field of
characteristic zero, and `k` is an identified residue field of characteristic
`p`.  Splitting hypotheses for finite groups are deliberately not fields of
this structure. -/
structure ModularSystem
    (p : ℕ) (K : Type uK) (O : Type uO) (k : Type uk)
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K] where
  prime : p.Prime
  [isDiscreteValuationRing : IsDiscreteValuationRing O]
  [isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [isFractionRing : IsFractionRing O K]
  [charZero : CharZero K]
  [charP : CharP k p]
  residueEquiv : IsLocalRing.ResidueField O ≃+* k

namespace ModularSystem

variable {p : ℕ} {K : Type uK} {O : Type uO} {k : Type uk}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]

/-- The maximal ideal determined by the local-ring structure stored in a
modular system. -/
def maximalIdeal (M : ModularSystem p K O k) : Ideal O :=
  @IsLocalRing.maximalIdeal O _ M.isDiscreteValuationRing.toIsLocalRing

/-- The reduction homomorphism `O → k` of a modular system. -/
noncomputable def residue (M : ModularSystem p K O k) : O →+* k := by
  letI := M.isDiscreteValuationRing
  exact M.residueEquiv.toRingHom.comp (IsLocalRing.residue O)

/-- The `O`-algebra structure on `k` induced by the residue homomorphism.

This is the scalar structure that must be used when reducing an integral
lattice.  An unrelated `Algebra O k` instance need not describe reduction
modulo the maximal ideal. -/
@[instance_reducible]
noncomputable def residueAlgebra (M : ModularSystem p K O k) : Algebra O k :=
  M.residue.toAlgebra

/-- Under `residueAlgebra`, the algebra map is the residue homomorphism. -/
theorem algebraMap_residueAlgebra (M : ModularSystem p K O k) :
    @algebraMap O k _ _ M.residueAlgebra = M.residue :=
  RingHom.algebraMap_toAlgebra M.residue

@[simp]
theorem residue_apply (M : ModularSystem p K O k) (x : O) :
    M.residue x = M.residueEquiv (Ideal.Quotient.mk M.maximalIdeal x) := by
  rfl

/-- Reduction onto the residue field is surjective. -/
theorem residue_surjective (M : ModularSystem p K O k) :
    Function.Surjective M.residue := by
  let _ := M.isDiscreteValuationRing
  exact M.residueEquiv.surjective.comp
    (IsLocalRing.residue_surjective (R := O))

/-- The kernel of reduction is exactly the maximal ideal of `O`. -/
theorem ker_residue (M : ModularSystem p K O k) :
    RingHom.ker M.residue = M.maximalIdeal := by
  let _ := M.isDiscreteValuationRing
  rw [residue, RingHom.ker_comp_of_injective _ M.residueEquiv.injective,
    IsLocalRing.ker_residue]
  rfl

/-- An element reduces to zero exactly when it belongs to the maximal ideal. -/
theorem residue_eq_zero_iff (M : ModularSystem p K O k) (x : O) :
    M.residue x = 0 ↔ x ∈ M.maximalIdeal := by
  simpa only [RingHom.mem_ker] using
    (SetLike.ext_iff.mp M.ker_residue x)

end ModularSystem

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
