import ModularRep.PaperProofs.TypeBSpinOrdinaryRestriction
import ModularRep.PaperProofs.TypeBSpinRationalUnipotentClassBinding
import ModularRep.PaperProofs.TypeBGGGRRankProposition412Relative

/-!
# Actual restriction scalar products for the nonabelian GGGR argument

The constituents are the actual occurrence subtype for the literal inclusion
of Spin into special Clifford.  Multiplicity-free restriction and its
compatibility with normalized duality are the ordinary E1/E2 source inputs.
The natural lower multiplicities are extracted from the actual scalar
products; the specified application supplies nonnegativity from the existing
odd-induction PIM expansion.  No lower column sum or matrix is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankGGGREntries

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinOrdinaryRestriction TypeBSpinPrincipalProjectiveBinding
open TypeBSpinRationalUnipotentClassBinding
open scoped BigOperators

variable {n r : ℕ} {F K : Type} [Field F] [Finite F] [CharP F r]
  [Field K] [CharZero K] {N : NormSource n F} [Finite (Spin n F N)]
  [Finite (Irr K (Spin n F N))]

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- The carrier records literal ordinary restriction occurrence. -/
abbrev Constituent (Phi : Irr K (SpecialClifford n F)) :=
  {theta : Irr K (Spin n F N) // occurs N Phi theta}

/-- Published restriction statements on one specified upper Taylor family.
The duality equation is the composed consequence of multiplicity-free
restriction and Taylor's Lemma 5.2/Corollary 5.3 for normalized duality. A
redundant before-duality function expansion is not an additional field.
The nonempty clause is ordinary restriction of an irreducible representation
over the indicated splitting field. -/
structure RestrictionSource
    (family : Set (Irr K (SpecialClifford n F)))
    (upperDual : Irr K (SpecialClifford n F) → Irr K (SpecialClifford n F))
    (lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N)) where
  nonempty : ∀ Phi ∈ family, Nonempty (Constituent (N := N) Phi)
  dualityRestriction : ∀ Phi ∈ family,
    restrictionClassFunction N (upperDual Phi) =
      ∑ theta : Constituent (N := N) Phi, (lowerDual theta.val).val
  cliffordTransitive : ∀ Phi ∈ family,
    ∀ theta psi : Constituent (N := N) Phi,
      ∃ g : SpecialClifford n F,
        twist K (Spin n F N) theta.val
          (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) = psi.val
  dualityConjugation : ∀ Phi ∈ family,
    ∀ theta : Constituent (N := N) Phi, ∀ g : SpecialClifford n F,
      lowerDual (twist K (Spin n F N) theta.val
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)) =
      twist K (Spin n F N) (lowerDual theta.val)
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)

variable (gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K)
  (nonnegative : ∀ (theta : Irr K (Spin n F N)) (c : UnipotentClass (r := r) (N := N)),
    ∃ a : ℕ, scalarProductRight theta.val (gamma c) = (a : K))

/-- A natural number chosen from the specified scalar product equality. -/
def multiplicity (theta : Irr K (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)) : ℕ :=
  Classical.choose (nonnegative theta c)

theorem multiplicity_cast (theta : Irr K (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)) :
    (multiplicity gamma nonnegative theta c : K) =
      scalarProductRight theta.val (gamma c) :=
  (Classical.choose_spec (nonnegative theta c)).symm

variable {gamma nonnegative}
  {family : Set (Irr K (SpecialClifford n F))}
  {upperDual : Irr K (SpecialClifford n F) → Irr K (SpecialClifford n F)}
  {lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N)}

/-- The actual restriction scalar product is the sum of the natural
constituent entries.  Frobenius reciprocity can now identify the right side
with the upper GGGR scalar product. -/
theorem lower_column_sum_cast
    (source : RestrictionSource (N := N) family upperDual lowerDual)
    (Phi : Irr K (SpecialClifford n F)) (hPhi : Phi ∈ family)
    (c : UnipotentClass (r := r) (N := N)) :
    ((∑ theta : Constituent (N := N) Phi,
        multiplicity gamma nonnegative (lowerDual theta.val) c : ℕ) : K) =
      scalarProductRight (restrictionClassFunction N (upperDual Phi)) (gamma c) := by
  classical
  rw [source.dualityRestriction Phi hPhi, scalarProductRight_comm]
  simp only [Nat.cast_sum, map_sum]
  apply Finset.sum_congr rfl
  intro theta htheta
  rw [multiplicity_cast, scalarProductRight_comm]

/-- If an upper pairing vanishes, every actual constituent pairing vanishes.
This uses the nonnegative sum, rather than a sourced cross-fibre matrix. -/
theorem lower_entry_zero_of_restriction_zero
    (source : RestrictionSource (N := N) family upperDual lowerDual)
    (Phi : Irr K (SpecialClifford n F)) (hPhi : Phi ∈ family)
    (c : UnipotentClass (r := r) (N := N))
    (hzero : scalarProductRight (restrictionClassFunction N (upperDual Phi))
      (gamma c) = 0) (theta : Constituent (N := N) Phi) :
    multiplicity gamma nonnegative (lowerDual theta.val) c = 0 := by
  have hcast := lower_column_sum_cast (gamma := gamma) (nonnegative := nonnegative)
    source Phi hPhi c
  rw [hzero] at hcast
  have hsum : (∑ psi : Constituent (N := N) Phi,
      multiplicity gamma nonnegative (lowerDual psi.val) c) = 0 :=
    Nat.cast_eq_zero.mp hcast
  exact Finset.sum_eq_zero_iff.mp hsum theta (Finset.mem_univ theta)

/-- A restriction pairing of one gives the natural column-sum equation. -/
theorem lower_column_sum_one
    (source : RestrictionSource (N := N) family upperDual lowerDual)
    (Phi : Irr K (SpecialClifford n F)) (hPhi : Phi ∈ family)
    (c : UnipotentClass (r := r) (N := N))
    (hone : scalarProductRight (restrictionClassFunction N (upperDual Phi))
      (gamma c) = 1) :
    (∑ theta : Constituent (N := N) Phi,
      multiplicity gamma nonnegative (lowerDual theta.val) c) = 1 := by
  apply Nat.cast_injective (R := K)
  simpa only [Nat.cast_one] using
    (lower_column_sum_cast (gamma := gamma) (nonnegative := nonnegative)
      source Phi hPhi c).trans hone

end ModularRep.PaperProofs.TypeBAllRankGGGREntries


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
