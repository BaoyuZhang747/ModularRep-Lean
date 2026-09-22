import ModularRep.BrauerCharacter
import ModularRep.CharpolyInvariantSubmodule
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Exact additivity of Brauer characters

Brauer characters defined from an explicit prime regular root embedding are
additive on invariant subspaces and quotients.  Consequently they are
additive on every short exact sequence of finite dimensional
representations.  The proof is internal: it factors characteristic
polynomials and does not assume Jordan--Hölder additivity.
-/

noncomputable section

open CategoryTheory

namespace Representation

universe u v w x y

variable {p : ℕ} {k : Type u} {K : Type v} {G : Type w} {V : Type x}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The Brauer character of a representation is the sum of the Brauer
characters on an invariant subspace and on the corresponding quotient. -/
theorem brauerCharacterOfRootEmbedding_subrepresentation_quotient
    (rho : Representation k G V)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (W : Submodule k V) (hW : ∀ g, W ≤ W.comap (rho g)) :
    rho.brauerCharacterOfRootEmbedding iota =
      (rho.subrepresentation W hW).brauerCharacterOfRootEmbedding iota +
        (rho.quotient W hW).brauerCharacterOfRootEmbedding iota := by
  apply ModularRep.PrimeRegularClassFunction.ext
  intro (g : ModularRep.PrimeRegularElement (G := G) p)
  let a : G := g.1
  change ((rho a).charpoly.roots.map iota.lift).sum =
    (((rho a).restrict (hW a)).charpoly.roots.map iota.lift).sum +
      ((W.mapQ W (rho a) (hW a)).charpoly.roots.map iota.lift).sum
  rw [LinearMap.charpoly_eq_restrict_mul_mapQ W (rho a) (hW a)]
  rw [Polynomial.roots_mul]
  · simp
  · exact mul_ne_zero
      ((rho a).restrict (hW a)).charpoly_monic.ne_zero
      (W.mapQ W (rho a) (hW a)).charpoly_monic.ne_zero

variable {W : Type y}
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Brauer characters are additive on products of finite dimensional
representations. -/
@[simp]
theorem brauerCharacterOfRootEmbedding_prod
    (rho : Representation k G V) (sigma : Representation k G W)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G) :
    (rho.prod sigma).brauerCharacterOfRootEmbedding iota =
      rho.brauerCharacterOfRootEmbedding iota +
        sigma.brauerCharacterOfRootEmbedding iota := by
  apply ModularRep.PrimeRegularClassFunction.ext
  intro (g : ModularRep.PrimeRegularElement (G := G) p)
  let a : G := g.1
  change ((((rho a).prodMap (sigma a)).charpoly.roots.map
    iota.lift).sum) =
      ((rho a).charpoly.roots.map iota.lift).sum +
        ((sigma a).charpoly.roots.map iota.lift).sum
  rw [LinearMap.charpoly_prodMap, Polynomial.roots_mul]
  · simp
  · exact mul_ne_zero (rho a).charpoly_monic.ne_zero
      (sigma a).charpoly_monic.ne_zero

end Representation

namespace FDRep

universe u v w

section UnderlyingExactness

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- A categorical short exact sequence in `FDRep` is an exact sequence of
the underlying linear maps, whose first map is injective and whose second
map is surjective. -/
theorem shortExact_underlying_functions
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    Function.Injective S.f.hom.hom.hom ∧
      Function.Surjective S.g.hom.hom.hom ∧
      Function.Exact S.f.hom.hom.hom S.g.hom.hom.hom := by
  let F := forget₂ (FDRep k G) (Rep k G)
  let T := S.map F
  have hT : T.ShortExact := hS.map_of_exact F
  refine ⟨?_, ?_, ?_⟩
  · have h := (Rep.mono_iff_injective T.f).mp hT.mono_f
    change Function.Injective S.f.hom.hom.hom at h
    exact h
  · have h := (Rep.epi_iff_surjective T.g).mp hT.epi_g
    change Function.Surjective S.g.hom.hom.hom at h
    exact h
  · let U := forget₂ (Rep k G) (ModuleCat k)
    let Q := T.map U
    have hQ : Q.Exact :=
      (T.exact_map_iff_of_faithful U).mpr hT.exact
    have h :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp hQ
    change Function.Exact S.f.hom.hom.hom S.g.hom.hom.hom at h
    exact h

end UnderlyingExactness

section BrauerCharacter

variable {p : ℕ} {k : Type u} {K : Type v} {G : Type w}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Brauer characters formed using an explicit prime regular root embedding
are additive on short exact sequences in `FDRep`. -/
theorem brauerCharacterOfRootEmbedding_shortExact
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    Representation.brauerCharacterOfRootEmbedding S.X₂.ρ iota =
      Representation.brauerCharacterOfRootEmbedding S.X₁.ρ iota +
        Representation.brauerCharacterOfRootEmbedding S.X₃.ρ iota := by
  let f : S.X₁ →ₗ[k] S.X₂ := S.f.hom.hom.hom
  let q : S.X₂ →ₗ[k] S.X₃ := S.g.hom.hom.hom
  obtain ⟨hf, hq, hexact⟩ := shortExact_underlying_functions S hS
  change Function.Injective f at hf
  change Function.Surjective q at hq
  change Function.Exact f q at hexact
  have hker : LinearMap.ker q = LinearMap.range f :=
    LinearMap.exact_iff.mp hexact
  have hfcomm (a : G) (x : S.X₁) :
      f (S.X₁.ρ a x) = S.X₂.ρ a (f x) := by
    have h := ConcreteCategory.congr_hom (S.f.comm a) x
    change f (S.X₁.ρ a x) = S.X₂.ρ a (f x) at h
    exact h
  have hqcomm (a : G) (x : S.X₂) :
      q (S.X₂.ρ a x) = S.X₃.ρ a (q x) := by
    have h := ConcreteCategory.congr_hom (S.g.comm a) x
    change q (S.X₂.ρ a x) = S.X₃.ρ a (q x) at h
    exact h
  let W := LinearMap.range f
  have hW (a : G) : W ≤ W.comap (S.X₂.ρ a) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨S.X₁.ρ a x, hfcomm a x⟩
  let ef : S.X₁ ≃ₗ[k] W := LinearEquiv.ofInjective f hf
  have hconjf (a : G) :
      ef.conj (S.X₁.ρ a) = (S.X₂.ρ a).restrict (hW a) := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := ef.surjective y
    apply Subtype.ext
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change f (S.X₁.ρ a x) = S.X₂.ρ a (f x)
    exact hfcomm a x
  have hcharf (a : G) :
      ((S.X₂.ρ a).restrict (hW a)).charpoly =
        (S.X₁.ρ a).charpoly := by
    rw [← hconjf a]
    exact LinearEquiv.charpoly_conj ef (S.X₁.ρ a)
  let eqv : (S.X₂ ⧸ W) ≃ₗ[k] S.X₃ :=
    (Submodule.quotEquivOfEq W (LinearMap.ker q) hker.symm).trans
      (q.quotKerEquivOfSurjective hq)
  have heqv_mk (x : S.X₂) :
      eqv (Submodule.Quotient.mk x) = q x := by
    simp [eqv]
  have heqv_intertwines (a : G) (x : S.X₂ ⧸ W) :
      eqv (W.mapQ W (S.X₂.ρ a) (hW a) x) =
        S.X₃.ρ a (eqv x) := by
    induction x using Submodule.Quotient.induction_on with
    | _ x => simp [heqv_mk, hqcomm]
  have hconjq (a : G) :
      eqv.conj (W.mapQ W (S.X₂.ρ a) (hW a)) = S.X₃.ρ a := by
    apply LinearMap.ext
    intro x
    simpa [LinearEquiv.conj_apply_apply] using
      heqv_intertwines a (eqv.symm x)
  have hcharq (a : G) :
      (W.mapQ W (S.X₂.ρ a) (hW a)).charpoly =
        (S.X₃.ρ a).charpoly := by
    rw [← hconjq a]
    exact (LinearEquiv.charpoly_conj eqv
      (W.mapQ W (S.X₂.ρ a) (hW a))).symm
  rw [Representation.brauerCharacterOfRootEmbedding_subrepresentation_quotient
    S.X₂.ρ iota W hW]
  congr 1
  · ext a
    change (((S.X₂.ρ a.1).restrict (hW a.1)).charpoly.roots.map
      iota.lift).sum =
        ((S.X₁.ρ a.1).charpoly.roots.map iota.lift).sum
    rw [hcharf]
  · ext a
    change ((W.mapQ W (S.X₂.ρ a.1) (hW a.1)).charpoly.roots.map
      iota.lift).sum =
        ((S.X₃.ρ a.1).charpoly.roots.map iota.lift).sum
    rw [hcharq]

end BrauerCharacter

end FDRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
