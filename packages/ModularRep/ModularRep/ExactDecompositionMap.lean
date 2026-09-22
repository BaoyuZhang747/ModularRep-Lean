import ModularRep.ExactGrothendieckGroup
import ModularRep.ModularSystem
import ModularRep.StableLattice

/-!
# Exact decomposition-map data

This file specializes the universal property of the exact Grothendieck-group
presentation to finite-dimensional representations.  A rule on isomorphism
classes of ordinary representations that is additive on short exact
sequences induces an additive homomorphism to the modular `K₀` presentation.

The classical modular decomposition map requires more: its value must be the
class of the reduction of every stable integral lattice.  That requirement is
defined below as an explicit predicate.  No lattice-independence or exactness
theorem from modular representation theory is assumed silently.
-/

open CategoryTheory

namespace ModularRep

universe u v

/-- Data sufficient to define a homomorphism from the ordinary exact `K₀`
presentation to the modular exact `K₀` presentation.

The field `reductionClass` is indexed by the skeleton, so invariance under
isomorphism is built into its type.  Additivity on short exact complexes is
the remaining relation needed to descend to `K₀`. -/
structure ExactDecompositionMapData
    (K : Type u) (k : Type u) (G : Type v)
    [Field K] [Field k] [Monoid G] where
  reductionClass :
    Skeleton (FDRep K G) → ExactGrothendieckGroup.FDRepKZero k G
  map_shortExact :
    ∀ (S : ShortComplex (FDRep K G)), S.ShortExact →
      reductionClass (toSkeleton S.X₂) =
        reductionClass (toSkeleton S.X₁) +
          reductionClass (toSkeleton S.X₃)

namespace ExactDecompositionMapData

variable {K : Type u} {k : Type u} {G : Type v}
variable [Field K] [Field k] [Monoid G]

/-- The homomorphism induced by the exact-additivity data. -/
noncomputable def toAddMonoidHom (D : ExactDecompositionMapData K k G) :
    ExactGrothendieckGroup.FDRepKZero K G →+
      ExactGrothendieckGroup.FDRepKZero k G :=
  ExactGrothendieckGroup.lift (FDRep K G)
    D.reductionClass D.map_shortExact

@[simp]
theorem toAddMonoidHom_classOf (D : ExactDecompositionMapData K k G)
    (V : FDRep K G) :
    D.toAddMonoidHom (ExactGrothendieckGroup.classOf (FDRep K G) V) =
      D.reductionClass (toSkeleton V) :=
  ExactGrothendieckGroup.lift_classOf
    (FDRep K G) D.reductionClass D.map_shortExact V

end ExactDecompositionMapData

section StableLatticeCompatibility

variable {p : ℕ} {K O k : Type u} {G : Type v}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [Group G]

/-- The exact compatibility required of decomposition-map data: for every
finite-dimensional ordinary representation and every stable integral
lattice, the assigned modular class is the exact `K₀` class of its tensor
reduction along the residue map.

This predicate is the present unformalised lattice-independence and exactness
bridge.  It is not inhabited by this library. -/
def RealisesStableLatticeReduction
    (Msys : ModularSystem p K O k)
    (D : ExactDecompositionMapData K k G) : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L : StableLattice O K rho),
    letI := Msys.residueAlgebra
    D.reductionClass (toSkeleton (FDRep.of rho)) =
      ExactGrothendieckGroup.classOf (FDRep k G)
        (FDRep.of (L.reduction k))

/-- Compatibility identifies the induced `K₀` homomorphism with reduction of
every chosen stable lattice. -/
theorem ExactDecompositionMapData.map_classOf_eq_reduction
    (Msys : ModularSystem p K O k)
    (D : ExactDecompositionMapData K k G)
    (hD : RealisesStableLatticeReduction Msys D)
    {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    D.toAddMonoidHom
        (ExactGrothendieckGroup.classOf (FDRep K G) (FDRep.of rho)) =
      ExactGrothendieckGroup.classOf (FDRep k G)
        (FDRep.of (L.reduction k)) := by
  let _ := Msys.residueAlgebra
  rw [D.toAddMonoidHom_classOf]
  exact hD rho L

/-- Under the compatibility predicate, two stable lattices in the same
ordinary representation have the same class in modular exact `K₀`.

This is equality of composition-factor classes, not an isomorphism between
the reduced representations. -/
theorem ExactDecompositionMapData.reductionClass_eq
    (Msys : ModularSystem p K O k)
    (D : ExactDecompositionMapData K k G)
    (hD : RealisesStableLatticeReduction Msys D)
    {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L₁ L₂ : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    ExactGrothendieckGroup.classOf (FDRep k G) (FDRep.of (L₁.reduction k)) =
      ExactGrothendieckGroup.classOf (FDRep k G)
        (FDRep.of (L₂.reduction k)) := by
  let _ := Msys.residueAlgebra
  rw [← hD rho L₁, ← hD rho L₂]

end StableLatticeCompatibility

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
