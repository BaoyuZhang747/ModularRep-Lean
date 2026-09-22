import ModularRep.NormalizerQuotient
import ModularRep.RadicalSubgroup
import ModularRep.DefectZeroRepresentation
import Mathlib.RepresentationTheory.FDRep

/-!
# A representation theoretic weight interface

For a finite group `G` and a subgroup `Q`, this file uses the quotient
`N_G(Q) / Q`.  It then packages a `p`-radical subgroup together with a simple
finite-dimensional characteristic-zero representation of that quotient whose
degree has the full `p`-part.

Over a splitting field, the simple representation determines the irreducible
ordinary defect-zero character used in the usual definition of a weight.
That splitting-field and character-realisation theorem is not asserted here.
Block induction, conjugacy classes of weights, and automorphism actions are
also separate layers.
-/

open CategoryTheory Module

namespace ModularRep

universe u v

variable {G : Type v} [Group G]



/-- A representation theoretic `p`-weight.

The local object is a simple representation rather than a character.  Its
identification with the conventional irreducible ordinary weight character
requires a compatible splitting field. -/
structure RepresentationWeight
    (p : ℕ) (K : Type u) (G : Type v)
    [Field K] [CharZero K] [Group G] [Finite G] where
  prime : p.Prime
  subgroup : Subgroup G
  radical : IsRadicalSubgroup p subgroup
  localRepresentation : FDRep K (NormalizerQuotient subgroup)
  irreducible : Simple localRepresentation
  defectZero : IsDefectZeroRepresentation p localRepresentation

namespace RepresentationWeight

variable {p : ℕ} {K : Type u} [Field K] [CharZero K]
variable [Finite G]

/-- The subgroup of a representation theoretic weight is a `p`-group. -/
theorem subgroup_isPGroup (W : RepresentationWeight p K G) :
    IsPGroup p W.subgroup :=
  W.radical.isPGroup

/-- The stored irreducibility proof can be installed as the categorical
`Simple` instance for the local representation. -/
instance (W : RepresentationWeight p K G) : Simple W.localRepresentation :=
  W.irreducible

end RepresentationWeight

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
