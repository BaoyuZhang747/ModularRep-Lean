import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.RepresentationTheory.FDRep

/-!
# Defect zero for finite-dimensional representations

This neutral predicate compares the prime parts of the representation
dimension and the finite monoid order. It makes no irreducibility,
character-realisation, or weight assertion.
-/

open CategoryTheory Module

namespace ModularRep

universe u v

/-- A finite-dimensional representation has defect zero at `p` when the
`p`-part of its dimension equals the `p`-part of the group order. -/
def IsDefectZeroRepresentation
    (p : ℕ) {K : Type u} [Field K] {H : Type v} [Monoid H] [Finite H]
    (V : FDRep K H) : Prop :=
  ordProj[p] (finrank K V) = ordProj[p] (Nat.card H)

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
