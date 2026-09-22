import ModularRep.StableLattice

/-!
# A decomposition-map interface

`ExactGrothendieckGroup` constructs the relevant exact `K₀` presentations,
but the classical decomposition map between them still requires the
lattice-independence theorem from modular representation theory.  This file
therefore gives an explicit class-valued interface.  Its compatibility field
states exactly that reduction of every stable lattice represents the image of
the ordinary class.  Lattice independence is consequently an input to the
interface, not an axiom or an accidental consequence of tensor reduction.
-/

namespace ModularRep

universe uO uK uk uG uV uM uS uT

variable {O : Type uO} {K : Type uK} {k : Type uk} {G : Type uG}
variable [CommRing O] [CommRing K] [Semiring k]
variable [Algebra O K] [Algebra O k] [Group G]

/-- An abstract class-valued decomposition map realised by stable-lattice
reduction.  The source and target class groups are explicit because their
representation theoretic constructions remain to be formalised. -/
structure DecompositionMapInterface
    (OrdinaryClass : Type uS) (ModularClass : Type uT)
    [AddCommGroup OrdinaryClass] [AddCommGroup ModularClass] where
  ordinaryClass :
    {V : Type uV} → [AddCommGroup V] → [Module O V] →
      [Module K V] → [IsScalarTower O K V] →
      Representation K G V → OrdinaryClass
  modularClass :
    {M : Type (max uk uV)} → [AddCommMonoid M] → [Module k M] →
      Representation k G M → ModularClass
  toAddMonoidHom : OrdinaryClass →+ ModularClass
  map_ordinaryClass_eq_reductionClass :
    ∀ {V : Type uV} [AddCommGroup V] [Module O V] [Module K V]
      [IsScalarTower O K V] (rho : Representation K G V)
      (L : StableLattice O K rho),
      toAddMonoidHom (ordinaryClass rho) = modularClass (L.reduction k)

namespace DecompositionMapInterface

variable {OrdinaryClass : Type uS} {ModularClass : Type uT}
variable [AddCommGroup OrdinaryClass] [AddCommGroup ModularClass]

/-- The compatibility field of a decomposition-map interface implies that
the modular class is independent of the selected stable lattice.  This does
not claim that the two reduced representations are isomorphic. -/
theorem reductionClass_eq
    (D : DecompositionMapInterface (O := O) (K := K) (k := k) (G := G)
      OrdinaryClass ModularClass)
    {V : Type uV} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] (rho : Representation K G V)
    (L₁ L₂ : StableLattice O K rho) :
    D.modularClass (L₁.reduction k) = D.modularClass (L₂.reduction k) := by
  rw [← D.map_ordinaryClass_eq_reductionClass rho L₁,
    ← D.map_ordinaryClass_eq_reductionClass rho L₂]

end DecompositionMapInterface

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
