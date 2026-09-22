import ModularRep.ModularTraceFunction
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Separation of irreducible representations by modular traces

This file formalises the pairwise trace-separation argument underlying
Navarro, *Characters and Blocks of Finite Groups*, Theorem (1.19), printed
pp. 12--13.  Schur's lemma and Jacobson density show that two nonisomorphic
finite dimensional simple modules are separated by the trace of an algebra
element.  The result is then specialised to irreducible group
representations and bundled objects of `FDRep`.

No representation theoretic theorem is introduced as an axiom.  The proof
uses the corresponding algebraic results already proved in Mathlib.
-/

noncomputable section

open scoped MonoidAlgebra

universe u

namespace ModularRep.ModularTraceSeparation

variable {k A V : Type u}
variable [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [AddCommGroup V] [Module k V] [Module A V]
variable [IsScalarTower k A V]
variable [FiniteDimensional k V] [IsSimpleModule A V]

/-- Navarro's Theorem 1.19, surjectivity clause: a finite dimensional
irreducible representation of an algebra over an algebraically closed field
has full endomorphism algebra as its image. -/
theorem irreducible_algebraRepresentation_surjective : Function.Surjective
    (Module.toModuleEnd k V : A →+* Module.End k V) := by
  let E := Module.End A V
  have hE : Function.Surjective (algebraMap k E) :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2
  have hfinite : Module.Finite E V := by
    refine Module.Finite.of_fg_top ?_
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := V)
    exact ⟨s, Submodule.span_eq_top_of_span_eq_top k E (s : Set V) hs⟩
  let _ : Module.Finite E V := hfinite
  intro f
  let fE : Module.End E V :=
    { f with
      map_smul' := by
        intro e x
        obtain ⟨c, rfl⟩ := hE e
        simp }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) fE
  refine ⟨a, ?_⟩
  ext x
  exact congr($ha x)

omit [IsAlgClosed k] in
/-- The ordinary linear trace is onto on a nonzero finite dimensional vector
space.  This avoids using the trace of the identity, which can vanish in
positive characteristic. -/
theorem linearMap_trace_surjective
    {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [Nontrivial W] :
    Function.Surjective (LinearMap.trace k W) := by
  let b := Module.Free.chooseBasis k W
  let _ : Nonempty (Module.Free.ChooseBasisIndex k W) :=
    Fintype.card_pos_iff.mp (by
      rw [← Module.finrank_eq_card_basis b]
      exact Module.finrank_pos)
  intro c
  obtain ⟨M, hM⟩ :=
    (Matrix.trace_surjective
      (n := Module.Free.ChooseBasisIndex k W) (R := k)) c
  refine ⟨Matrix.toLin b b M, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace k b]
  simpa using hM

section TwoSimpleModules

variable {W : Type u}
variable [AddCommGroup W] [Module k W] [Module A W]
variable [IsScalarTower k A W]
variable [FiniteDimensional k W] [IsSimpleModule A W]

/-- An endomorphism of a sum of two nonisomorphic simple modules is scalar
on each summand. -/
theorem moduleEnd_prod_apply_eq_smul
    (hVW : ¬ Nonempty (V ≃ₗ[A] W))
    (e : Module.End A (V × W)) :
    ∃ c d : k, ∀ v w, e (v, w) = (c • v, d • w) := by
  let eVV : Module.End A V :=
    (LinearMap.fst A V W).comp (e.comp (LinearMap.inl A V W))
  let eWW : Module.End A W :=
    (LinearMap.snd A V W).comp (e.comp (LinearMap.inr A V W))
  let eVW : V →ₗ[A] W :=
    (LinearMap.snd A V W).comp (e.comp (LinearMap.inl A V W))
  let eWV : W →ₗ[A] V :=
    (LinearMap.fst A V W).comp (e.comp (LinearMap.inr A V W))
  obtain ⟨c, hc⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := A) (V := V) k).2 eVV
  obtain ⟨d, hd⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := A) (V := W) k).2 eWW
  have hVWzero : eVW = 0 := by
    rcases LinearMap.bijective_or_eq_zero eVW with h | h
    · exact (hVW ⟨LinearEquiv.ofBijective eVW h⟩).elim
    · exact h
  have hWVzero : eWV = 0 := by
    rcases LinearMap.bijective_or_eq_zero eWV with h | h
    · exact (hVW ⟨(LinearEquiv.ofBijective eWV h).symm⟩).elim
    · exact h
  refine ⟨c, d, fun v w ↦ ?_⟩
  apply Prod.ext
  · have hc' : eVV v = c • v := by
      rw [← hc]
      simp
    have hzero := congr($hWVzero w)
    change eWV w = 0 at hzero
    change (e (v, w)).1 = c • v
    rw [show (v, w) = (v, 0) + (0, w) by simp, map_add]
    change eVV v + eWV w = c • v
    rw [hc', hzero, add_zero]
  · have hd' : eWW w = d • w := by
      rw [← hd]
      simp
    have hzero := congr($hVWzero v)
    change eVW v = 0 at hzero
    change (e (v, w)).2 = d • w
    rw [show (v, w) = (v, 0) + (0, w) by simp, map_add]
    change eVW v + eWW w = d • w
    rw [hzero, hd', zero_add]

/-- Two nonisomorphic finite dimensional simple modules are separated by the
trace of the action of some algebra element.  This is the pairwise content of
the linear independence clause in Navarro's Theorem 1.19. -/
theorem exists_trace_action_ne_of_not_linearEquiv
    (hVW : ¬ Nonempty (V ≃ₗ[A] W)) :
    ∃ a : A,
      LinearMap.trace k V
          ((Module.toModuleEnd k V : A →+* Module.End k V) a) ≠
        LinearMap.trace k W
          ((Module.toModuleEnd k W : A →+* Module.End k W) a) := by
  let _ : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨T, hT⟩ :=
    linearMap_trace_surjective (k := k) (W := V) 1
  let E := Module.End A (V × W)
  let _ : IsSemisimpleModule A (V × W) := by
    let p := LinearMap.range (LinearMap.inl A V W)
    let q := LinearMap.range (LinearMap.inr A V W)
    have hp : IsSemisimpleModule A p :=
      IsSemisimpleModule.range (LinearMap.inl A V W)
    have hq : IsSemisimpleModule A q :=
      IsSemisimpleModule.range (LinearMap.inr A V W)
    have hpq : IsSemisimpleModule A ↑(p ⊔ q) :=
      IsSemisimpleModule.sup hp hq
    have heq : p ⊔ q = ⊤ := LinearMap.sup_range_inl_inr
    rw [heq] at hpq
    exact hpq.congr Submodule.topEquiv.symm
  have hfinite : Module.Finite E (V × W) := by
    refine Module.Finite.of_fg_top ?_
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := V × W)
    exact ⟨s,
      Submodule.span_eq_top_of_span_eq_top k E (s : Set (V × W)) hs⟩
  let _ : Module.Finite E (V × W) := hfinite
  let F : Module.End E (V × W) :=
    { LinearMap.prodMap T (0 : Module.End k W) with
      map_smul' := by
        intro e x
        obtain ⟨c, d, he⟩ :=
          moduleEnd_prod_apply_eq_smul (k := k) (A := A)
            (V := V) (W := W) hVW e
        rcases x with ⟨v, w⟩
        change (T (e (v, w)).1, 0) = e (T v, 0)
        rw [he v w, he (T v) 0]
        simp }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective
      (R := A) (M := V × W) F
  refine ⟨a, ?_⟩
  have hVaction :
      (Module.toModuleEnd k V : A →+* Module.End k V) a = T := by
    ext v
    have hv := congr($ha (v, 0))
    exact congrArg Prod.fst hv
  have hWaction :
      (Module.toModuleEnd k W : A →+* Module.End k W) a = 0 := by
    ext w
    have hw := congr($ha (0, w))
    exact congrArg Prod.snd hw
  rw [hVaction, hWaction, hT, map_zero]
  exact one_ne_zero

/-- Equality of trace functions on an algebra forces finite dimensional
simple modules over an algebraically closed field to be isomorphic. -/
theorem nonempty_linearEquiv_of_trace_action_eq
    (htrace : ∀ a : A,
      LinearMap.trace k V
          ((Module.toModuleEnd k V : A →+* Module.End k V) a) =
        LinearMap.trace k W
          ((Module.toModuleEnd k W : A →+* Module.End k W) a)) :
    Nonempty (V ≃ₗ[A] W) := by
  by_contra hVW
  obtain ⟨a, ha⟩ :=
    exists_trace_action_ne_of_not_linearEquiv
      (k := k) (A := A) (V := V) (W := W) hVW
  exact ha (htrace a)

end TwoSimpleModules

section GroupRepresentation

variable {G : Type u} [Group G]

/-- The group representation form of the surjectivity clause in Navarro's
Theorem 1.19. -/
theorem irreducible_representation_asAlgebraHom_surjective
    (ρ : Representation k G V) (hρ : Representation.IsIrreducible ρ) :
    Function.Surjective ρ.asAlgebraHom := by
  let _ : IsSimpleModule k[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
  exact irreducible_algebraRepresentation_surjective
    (k := k) (A := k[G]) (V := ρ.asModule)

/-- Equality of the trace functions of irreducible group representations
implies equivalence of the representations. -/
theorem representation_equiv_of_character_eq
    {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    (hρ : Representation.IsIrreducible ρ)
    (hσ : Representation.IsIrreducible σ)
    (hchar : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  let _ : IsSimpleModule k[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
  let _ : IsSimpleModule k[G] σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  have htrace : ∀ a : k[G],
      LinearMap.trace k ρ.asModule
          ((Module.toModuleEnd k ρ.asModule :
            k[G] →+* Module.End k ρ.asModule) a) =
        LinearMap.trace k σ.asModule
          ((Module.toModuleEnd k σ.asModule :
            k[G] →+* Module.End k σ.asModule) a) := by
    intro a
    change LinearMap.trace k V (ρ.asAlgebraHom a) =
      LinearMap.trace k W (σ.asAlgebraHom a)
    exact LinearMap.congr_fun
      ((Representation.algebraTraceFunction_eq_iff_character_eq ρ σ).2 hchar) a
  obtain ⟨e⟩ := nonempty_linearEquiv_of_trace_action_eq
    (k := k) (A := k[G])
    (V := ρ.asModule) (W := σ.asModule) htrace
  let f : ρ.IntertwiningMap σ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm
      e.toLinearMap
  have hfun : (f : V → W) = e := by rfl
  refine ⟨f.ofBijective ?_⟩
  rw [hfun]
  exact e.bijective

open CategoryTheory in
/-- The bundled FDRep formulation: irreducible finite dimensional
representations with equal trace functions are isomorphic objects. -/
theorem fdRep_nonempty_iso_of_character_eq
    (X Y : FDRep k G)
    (hX : Representation.IsIrreducible X.ρ)
    (hY : Representation.IsIrreducible Y.ρ)
    (hchar : Representation.character X.ρ =
      Representation.character Y.ρ) :
    Nonempty (X ≅ Y) := by
  obtain ⟨e⟩ := representation_equiv_of_character_eq
    (k := k) X.ρ Y.ρ hX hY hchar
  refine ⟨Action.mkIso
    (LinearEquiv.toFGModuleCatIso e.toLinearEquiv) (fun g ↦ ?_)⟩
  ext x
  exact Representation.IntertwiningMap.isIntertwining
    X.ρ Y.ρ e.toIntertwiningMap g x

end GroupRepresentation

end ModularRep.ModularTraceSeparation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
