import ModularRep.CharpolyInvariantSubmodule
import ModularRep.ExactGrothendieckGroup
import ModularRep.PrimeRegularClassFunction
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Ordinary characters on the exact Grothendieck group

Ordinary trace characters are additive on short exact sequences of finite
dimensional representations.  This file proves that additivity directly and
uses it to define an additive homomorphism from the exact Grothendieck group
to the `K`-valued class functions on the `p`-regular elements.

The target is also the ambient group for Brauer characters formed from an
explicit prime regular root embedding.  Thus these two homomorphisms can be
compared in the stable-lattice compatibility theorem underlying the classical
decomposition map.
-/

noncomputable section

open CategoryTheory

universe u v

namespace LinearMap

variable {K V : Type u} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The trace of a finite dimensional endomorphism is minus the next
coefficient of its characteristic polynomial. -/
theorem trace_eq_neg_charpoly_nextCoeff (f : V →ₗ[K] V) :
    trace K V f = -f.charpoly.nextCoeff := by
  let b := Module.Free.chooseBasis K V
  rw [trace_eq_matrix_trace K b,
    Matrix.trace_eq_neg_charpoly_nextCoeff,
    charpoly_toMatrix]

/-- The trace of an endomorphism preserving a subspace is the sum of the
traces on that subspace and on the corresponding quotient. -/
theorem trace_eq_restrict_add_mapQ
    (W : Submodule K V) (f : V →ₗ[K] V) (hf : W ≤ W.comap f) :
    trace K V f =
      trace K W (f.restrict hf) +
        trace K (V ⧸ W) (W.mapQ W f hf) := by
  rw [trace_eq_neg_charpoly_nextCoeff,
    trace_eq_neg_charpoly_nextCoeff,
    trace_eq_neg_charpoly_nextCoeff,
    charpoly_eq_restrict_mul_mapQ W f hf,
    (f.restrict hf).charpoly_monic.nextCoeff_mul
      (W.mapQ W f hf).charpoly_monic]
  abel

end LinearMap

namespace FDRep

variable {K : Type u} {G : Type v} [Field K]

section Character

variable [Monoid G]

/-- Ordinary trace characters are additive on categorical short exact
sequences of finite dimensional representations. -/
theorem character_shortExact
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    S.X₂.character = S.X₁.character + S.X₃.character := by
  let F := forget₂ (FDRep K G) (Rep K G)
  let T := S.map F
  have hT : T.ShortExact := hS.map_of_exact F
  have hf : Function.Injective S.f.hom.hom.hom :=
    (Rep.mono_iff_injective T.f).mp hT.mono_f
  have hq : Function.Surjective S.g.hom.hom.hom :=
    (Rep.epi_iff_surjective T.g).mp hT.epi_g
  have hexact :
      Function.Exact S.f.hom.hom.hom S.g.hom.hom.hom := by
    let U := forget₂ (Rep K G) (ModuleCat K)
    let Q := T.map U
    have hQ : Q.Exact :=
      (T.exact_map_iff_of_faithful U).mpr hT.exact
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp hQ
  let f : S.X₁ →ₗ[K] S.X₂ := S.f.hom.hom.hom
  let q : S.X₂ →ₗ[K] S.X₃ := S.g.hom.hom.hom
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
  let ef : S.X₁ ≃ₗ[K] W := LinearEquiv.ofInjective f hf
  have hconjf (a : G) :
      ef.conj (S.X₁.ρ a) = (S.X₂.ρ a).restrict (hW a) := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := ef.surjective y
    apply Subtype.ext
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change f (S.X₁.ρ a x) = S.X₂.ρ a (f x)
    exact hfcomm a x
  let eqv : (S.X₂ ⧸ W) ≃ₗ[K] S.X₃ :=
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
  funext a
  change LinearMap.trace K S.X₂ (S.X₂.ρ a) =
    LinearMap.trace K S.X₁ (S.X₁.ρ a) +
      LinearMap.trace K S.X₃ (S.X₃.ρ a)
  rw [LinearMap.trace_eq_restrict_add_mapQ W (S.X₂.ρ a) (hW a),
    ← LinearMap.trace_conj' (S.X₁.ρ a) ef,
    hconjf a,
    ← LinearMap.trace_conj'
      (W.mapQ W (S.X₂.ρ a) (hW a)) eqv,
    hconjq a]

end Character

section RegularClassFunction

variable [Group G]

/-- Restriction of the ordinary trace character to the `p`-regular elements
is invariant under isomorphism of finite dimensional representations. -/
theorem regularTraceClassFunction_iso (p : ℕ)
    {V W : FDRep K G} (e : V ≅ W) :
    Representation.regularTraceClassFunction V.ρ p =
      Representation.regularTraceClassFunction W.ρ p := by
  ext g
  exact congrFun (char_iso e) g.1

/-- Ordinary trace class functions restricted to the `p`-regular elements
are additive on short exact sequences. -/
theorem regularTraceClassFunction_shortExact (p : ℕ)
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    Representation.regularTraceClassFunction S.X₂.ρ p =
      Representation.regularTraceClassFunction S.X₁.ρ p +
        Representation.regularTraceClassFunction S.X₃.ρ p := by
  ext g
  exact congrFun (character_shortExact S hS) g.1

end RegularClassFunction

end FDRep

namespace ModularRep

variable {K : Type u} {G : Type v} [Field K] [Group G]

/-- The ordinary trace class function attached to a skeletal
representative. -/
noncomputable def ordinaryCharacterSkeleton (p : ℕ)
    (X : Skeleton (FDRep K G)) : PrimeRegularClassFunction K G p :=
  Representation.regularTraceClassFunction
    ((fromSkeleton (FDRep K G)).obj X).ρ p

/-- Ordinary trace class functions on skeletal representatives respect
every short exact relation. -/
theorem ordinaryCharacterSkeleton_shortExact (p : ℕ)
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    ordinaryCharacterSkeleton p (toSkeleton S.X₂) =
      ordinaryCharacterSkeleton p (toSkeleton S.X₁) +
        ordinaryCharacterSkeleton p (toSkeleton S.X₃) := by
  dsimp only [ordinaryCharacterSkeleton]
  rw [FDRep.regularTraceClassFunction_iso p
      (fromSkeletonToSkeletonIso S.X₂),
    FDRep.regularTraceClassFunction_iso p
      (fromSkeletonToSkeletonIso S.X₁),
    FDRep.regularTraceClassFunction_iso p
      (fromSkeletonToSkeletonIso S.X₃)]
  exact FDRep.regularTraceClassFunction_shortExact p S hS

/-- Restriction of ordinary characters to the `p`-regular elements defines
an additive homomorphism on the exact Grothendieck group. -/
noncomputable def ordinaryCharacterKZero (p : ℕ) :
    ExactGrothendieckGroup.FDRepKZero K G →+
      PrimeRegularClassFunction K G p :=
  ExactGrothendieckGroup.lift (FDRep K G)
    (ordinaryCharacterSkeleton p)
    (ordinaryCharacterSkeleton_shortExact p)

/-- The ordinary-character homomorphism sends the class of a representation
to its ordinary trace character restricted to the `p`-regular elements. -/
@[simp]
theorem ordinaryCharacterKZero_classOf (p : ℕ) (V : FDRep K G) :
    ordinaryCharacterKZero p
        (ExactGrothendieckGroup.classOf (FDRep K G) V) =
      Representation.regularTraceClassFunction V.ρ p := by
  rw [ordinaryCharacterKZero, ExactGrothendieckGroup.lift_classOf]
  exact FDRep.regularTraceClassFunction_iso p
    (fromSkeletonToSkeletonIso V)

/-- Pointwise form of `ordinaryCharacterKZero_classOf`: evaluation on a
`p`-regular element is the ordinary trace of that element. -/
@[simp]
theorem ordinaryCharacterKZero_classOf_apply (p : ℕ) (V : FDRep K G)
    (g : PrimeRegularElement (G := G) p) :
    ordinaryCharacterKZero p
        (ExactGrothendieckGroup.classOf (FDRep K G) V) g =
      V.character g.1 := by
  rw [ordinaryCharacterKZero_classOf]
  rfl

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
