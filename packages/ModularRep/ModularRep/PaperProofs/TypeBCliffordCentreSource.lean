import ModularRep.PaperProofs.TypeBCliffordScalarNorm
import ModularRep.PaperProofs.TypeBSplitQuadraticGeometry

/-!
# The centre of the literal finite odd-dimensional special Clifford group

FLZ Section 2.5, p. 540 identifies the centre of its even-unit vector
normalizer with the scalar units when the orthogonal dimension is odd.
Section 3.1, p. 541 restates this for the actual finite groups over F_q,
with q odd and n positive. Here the dimension and nondegeneracy of the
literal split form are checked; the remaining one-way centre-to-scalar
statement is an exact E1 certificate on this carrier and source scope.

Scalar centrality is already proved. The two subgroup inclusions therefore
give equality with the actual scalar range. No source inhabitant is declared;
no norm, diagonal quotient, index, automorphism, or character conclusion is
an input. In particular, the separate generated Spin/Lipschitz carrier is
not substituted for the normalizer used in the source.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordCentreSource

open TypeBCliffordCarriers TypeBCliffordScalarNorm

universe u
variable (n : ℕ) (F : Type u) [Field F]

/-- The exact odd-dimensional orthogonal geometry is a deduction. -/
theorem source_geometry {p f : ℕ} [Finite F] [CharP F p]
    (parameters : OddFieldParameters F p f) :
    Module.finrank F (Vector n F) = 2 * n + 1 ∧
      (splitForm n F).Nondegenerate :=
  ⟨TypeBOrthogonalOmegaCarriers.vector_finrank n F,
    TypeBSplitQuadraticGeometry.splitForm_nondegenerate_of_oddFieldParameters
      n F parameters⟩

/-- The literal scalar range is central without a structural source. -/
theorem scalarRange_le_center :
    (scalar n F).range ≤ Subgroup.center (SpecialClifford n F) := by
  rintro _ ⟨z, rfl⟩
  exact scalar_mem_center n F z

/-- E1, FLZ Section 2.5 p. 540 and finite-point specialization Section 3.1
p. 541. The finite odd-field and positive-rank indices are explicit. The
only field gives the actual scalar value of an actual central element.
Its published realization remains U; no certificate inhabitant is supplied. -/
structure CentreSource {p f : ℕ} [Finite F] [CharP F p]
    (parameters : OddFieldParameters F p f) (rank : 1 ≤ n) : Prop where
  central_scalar : ∀ g : SpecialClifford n F,
    g ∈ Subgroup.center (SpecialClifford n F) →
      ∃ z : Fˣ, toClifford n F g = algebraMap F (Clifford n F) (z : F)

namespace CentreSource

variable {n F} {p f : ℕ} [Finite F] [CharP F p]
  {parameters : OddFieldParameters F p f} {rank : 1 ≤ n}

/-- The source value equation gives membership in the SAME actual range. -/
theorem center_le_scalarRange (C : CentreSource n F parameters rank) :
    Subgroup.center (SpecialClifford n F) ≤ (scalar n F).range := by
  intro g hg
  obtain ⟨z, hz⟩ := C.central_scalar g hg
  refine ⟨z, ?_⟩
  apply toClifford_injective n F
  exact (toClifford_scalar n F z).trans hz.symm

/-- Centre equality is deduced from the one-way certificate and checked
scalar centrality; it is not a diagonal-kernel or index input. -/
theorem center_eq_scalarRange (C : CentreSource n F parameters rank) :
    Subgroup.center (SpecialClifford n F) = (scalar n F).range :=
  le_antisymm C.center_le_scalarRange (scalarRange_le_center n F)

end CentreSource
end ModularRep.PaperProofs.TypeBCliffordCentreSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
