import Mathlib.Algebra.Module.Lattice
import Mathlib.RepresentationTheory.Subrepresentation
import ModularRep.RepresentationScalarChange

/-!
# Stable integral lattices

This file defines a stable lattice in a representation, constructs one from a
finite basis when the acting group is finite, and defines its reduction by
tensor extension.  `ModularRep.ReductionModulo` identifies the underlying
scalar module of that tensor product with a quotient by the maximal ideal.
Neither file asserts lattice independence of the resulting composition-factor
class.
-/

universe uO uK uk uG uV

open scoped TensorProduct
open Module

namespace ModularRep

section StableLattice

variable (O : Type uO) (K : Type uK) {G : Type uG} {V : Type uV}
variable [CommRing O] [CommRing K] [Algebra O K] [Group G]
variable [AddCommGroup V] [Module O V] [Module K V] [IsScalarTower O K V]

/-- An `O`-lattice in a `K`-representation that is stable under the group
action. -/
structure StableLattice (rho : Representation K G V)
    extends Subrepresentation (rho.restrictScalars O) where
  isLattice : toSubrepresentation.toSubmodule.IsLattice K

namespace StableLattice

variable {O K}
variable {rho : Representation K G V}

instance (L : StableLattice O K rho) :
    L.toSubrepresentation.toSubmodule.IsLattice K :=
  L.isLattice

/-- The sum of all translates of an `O`-submodule under a representation. -/
noncomputable def orbitSpan (rho : Representation K G V) (L : Submodule O V) :
    Submodule O V :=
  ⨆ g : G, L.map ((rho g).restrictScalars O)

/-- A submodule is contained in its orbit span. -/
theorem le_orbitSpan (rho : Representation K G V) (L : Submodule O V) :
    L ≤ orbitSpan rho L := by
  refine le_iSup_of_le (1 : G) ?_
  intro v hv
  exact ⟨v, hv, by simp⟩

/-- The orbit span is stable under the group action. -/
theorem orbitSpan_stable (rho : Representation K G V) (L : Submodule O V)
    (h : G) :
    orbitSpan rho L ≤ (orbitSpan rho L).comap ((rho h).restrictScalars O) := by
  unfold orbitSpan
  apply iSup_le
  intro g v hv
  change rho h v ∈ ⨆ q : G, L.map ((rho q).restrictScalars O)
  obtain ⟨w, hw, rfl⟩ := hv
  apply (le_iSup (fun q : G ↦ L.map ((rho q).restrictScalars O)) (h * g))
  refine ⟨w, hw, ?_⟩
  simp [← Module.End.mul_apply]

/-- The orbit span of a finitely generated submodule under a finite group is
finitely generated. -/
theorem orbitSpan_fg [Finite G] (rho : Representation K G V)
    (L : Submodule O V) (hL : L.FG) :
    (orbitSpan rho L).FG := by
  unfold orbitSpan
  apply Submodule.fg_iSup
  intro g
  exact Submodule.FG.map (f := (rho g).restrictScalars O) hL

/-- Taking the orbit span of a lattice preserves the lattice property when
the acting group is finite. -/
theorem orbitSpan_isLattice [Finite G] (rho : Representation K G V)
    (L : Submodule O V) [L.IsLattice K] :
    (orbitSpan rho L).IsLattice K :=
  Submodule.IsLattice.of_le_of_isLattice_of_fg K
    (le_orbitSpan rho L) (orbitSpan_fg rho L Submodule.IsLattice.fg)

/-- For a finite group, the orbit span turns any lattice into a stable
lattice. -/
noncomputable def stableClosure [Finite G] (rho : Representation K G V)
    (L : Submodule O V) [L.IsLattice K] : StableLattice O K rho where
  toSubrepresentation :=
    { toSubmodule := orbitSpan rho L
      apply_mem_toSubmodule := fun g _ hv ↦ orbitSpan_stable rho L g hv }
  isLattice := orbitSpan_isLattice rho L

section BasisLattice

variable {ι : Type*} [Finite ι]

/-- The `O`-span of a finite `K`-basis. -/
noncomputable def basisLattice (b : Basis ι K V) : Submodule O V :=
  Submodule.span O (Set.range b)

/-- The `O`-span of a finite `K`-basis is a lattice. -/
theorem basisLattice_isLattice (b : Basis ι K V) :
    (basisLattice (O := O) b).IsLattice K where
  fg := Submodule.fg_span (Set.toFinite (Set.range b))
  span_eq_top := by
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_mono Submodule.subset_span

/-- A representation of a finite group with a finite basis has an explicit
stable lattice, obtained from the orbit span of the basis lattice. -/
noncomputable def ofBasis [Finite G] (rho : Representation K G V)
    (b : Basis ι K V) : StableLattice O K rho := by
  letI : (basisLattice (O := O) b).IsLattice K := basisLattice_isLattice b
  exact stableClosure rho (basisLattice (O := O) b)

end BasisLattice

/-- The integral representation carried by a stable lattice. -/
def integralRepresentation (L : StableLattice O K rho) :
    Representation O G L.toSubrepresentation.toSubmodule :=
  L.toSubrepresentation.toRepresentation

@[simp]
theorem integralRepresentation_apply (L : StableLattice O K rho)
    (g : G) (v : L.toSubrepresentation.toSubmodule) :
    L.integralRepresentation g v =
      ⟨rho g v.1, L.toSubrepresentation.apply_mem_toSubmodule g v.2⟩ :=
  rfl

variable (k : Type uk) [Semiring k] [Algebra O k]

/-- Base change of a stable lattice along `O → k`.

For the residue map of a modular system this is `k ⊗[O] L`.  Its
identification with `L / mL` is supplied separately by
`ReductionModulo.stableLatticeReductionCarrierQuotientEquiv`. -/
def reduction (L : StableLattice O K rho) :
    Representation k G (k ⊗[O] L.toSubrepresentation.toSubmodule) :=
  L.integralRepresentation.baseChange k

@[simp]
theorem reduction_apply_tmul (L : StableLattice O K rho)
    (g : G) (a : k) (v : L.toSubrepresentation.toSubmodule) :
    L.reduction k g (a ⊗ₜ[O] v) =
      a ⊗ₜ[O]
        (⟨rho g v.1, L.toSubrepresentation.apply_mem_toSubmodule g v.2⟩ :
          L.toSubrepresentation.toSubmodule) :=
  rfl

/-- Reduction of a stable lattice is a finite module over the target
coefficient ring. -/
instance reduction_moduleFinite (L : StableLattice O K rho) :
    Module.Finite k (k ⊗[O] L.toSubrepresentation.toSubmodule) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin
    (R := O) (M := L.toSubrepresentation.toSubmodule)
  rw [Module.finite_def, Submodule.fg_iff_exists_fin_generating_family]
  refine ⟨n, fun i ↦ (1 : k) ⊗ₜ[O] s i, ?_⟩
  apply top_unique
  intro x hx
  clear hx
  induction x with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a m =>
      have hm : m ∈ Submodule.span O (Set.range s) := by
        rw [hs]
        trivial
      revert a
      induction hm using Submodule.span_induction with
      | mem m hm =>
          intro a
          obtain ⟨i, rfl⟩ := hm
          rw [TensorProduct.tmul_eq_smul_one_tmul]
          exact Submodule.smul_mem
            (Submodule.span k (Set.range fun i ↦ (1 : k) ⊗ₜ[O] s i)) a
            (Submodule.subset_span (Set.mem_range_self i))
      | zero => intro a; simp
      | add x y hx hy ihx ihy =>
          intro a
          simpa [TensorProduct.tmul_add] using
            Submodule.add_mem _ (ihx a) (ihy a)
      | smul r m hm ih =>
          intro a
          rw [TensorProduct.tmul_smul]
          exact ih (r • a)

end StableLattice

end StableLattice

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
