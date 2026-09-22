import ModularRep.FDRepSimpleClassKZero

/-!
# Finiteness of the set of simple module classes

If the left regular module of a ring has finite length, every simple module
is isomorphic to a factor of any composition series of that regular module.
Thus there are only finitely many isomorphism classes of simple modules,
without a choice of matrix representations.

For a finite group `G` and a field `k`, the group algebra `k[G]` is finite
dimensional over `k`, so the result applies to its simple modules.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.FDRepSimpleClassKZero

universe u

open JordanHolderCoordinates

/-- Every simple-module class occurs among the factors of any full
composition series of the regular module. -/
theorem simpleClass_appears_in_compositionSeries
    (R : Type u) [Ring R]
    (s : CompositionSeries (Submodule R R))
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (X : SimpleModuleClass R) :
    ∃ i : Fin s.length, compositionFactorSimpleClass R s i = X := by
  let M := (fromSkeleton (ModuleCat.{u} R)).obj X.1
  have hSimple : Simple M := X.2
  have hModule : IsSimpleModule R M :=
    simple_iff_isSimpleModule.mp hSimple
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hModule
  have hm : I ⋖ s.last := by
    rw [hslast]
    exact (Ideal.isMaximal_def.mp hI).covBy_top
  have hb : s.head ≤ I := by
    rw [hshead]
    exact bot_le
  obtain ⟨t, _hthead, _htlength, htx, hequiv⟩ :=
    CompositionSeries.exists_last_eq_snoc_equivalent s I hm hb
  let hcov : t.last ⋖ s.last := htx.symm ▸ hm
  let t' := t.snoc s.last hcov
  have hequiv' : CompositionSeries.Equivalent s t' := by
    simpa [t', hcov] using hequiv
  let hlen := RelSeries.snoc_length t s.last hcov
  let j : Fin t'.length := Fin.cast hlen.symm (Fin.last t.length)
  let i : Fin s.length := hequiv'.choose.symm j
  refine ⟨i, ?_⟩
  apply Subtype.ext
  rw [← toSkeleton_fromSkeleton_obj X.1]
  apply congr_toSkeleton_of_iso
  have hij : hequiv'.choose i = j := hequiv'.choose.apply_symm_apply j
  have hfactor := hequiv'.choose_spec i
  rw [hij] at hfactor
  let eJH := JordanHolderLattice.Iso.linearEquiv hfactor
  have hlow : t' (Fin.castSucc j) = I := by
    rw [← htx]
    change (t.snoc s.last hcov) (Fin.castSucc j) = t.last
    have hindex : Fin.castSucc j = (Fin.last t.length).castSucc := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact RelSeries.snoc_castSucc t s.last hcov (Fin.last t.length)
  have hupp : t' (Fin.succ j) = (⊤ : Submodule R R) := by
    change (t.snoc s.last hcov) (Fin.succ j) = ⊤
    have hindex : Fin.succ j = Fin.last (t.snoc s.last hcov).length := by
      apply Fin.ext
      simp [j, t']
    rw [hindex, RelSeries.apply_last, RelSeries.last_snoc, hslast]
  let eLast : compositionFactor t' j ≃ₗ[R] R ⧸ I := by
    change
      (t' (Fin.succ j) ⧸
          (t' (Fin.castSucc j)).comap (t' (Fin.succ j)).subtype) ≃ₗ[R]
        R ⧸ I
    rw [hlow, hupp]
    let eTop : (⊤ : Submodule R R) ≃ₗ[R] R := Submodule.topEquiv
    let Isub : Submodule R R := I
    exact Submodule.Quotient.equiv
      (Isub.comap (⊤ : Submodule R R).subtype) Isub eTop (by
        ext x
        simp [eTop, Isub])
  exact (eJH.trans eLast |>.trans e.symm).toModuleIso

/-- A full composition series of the regular module is a finite source
surjecting onto all simple-module classes. -/
theorem finite_simpleModuleClass_of_compositionSeries
    (R : Type u) [Ring R]
    (s : CompositionSeries (Submodule R R))
    (hshead : s.head = ⊥) (hslast : s.last = ⊤) :
    Finite (SimpleModuleClass R) :=
  Finite.of_surjective (compositionFactorSimpleClass R s)
    (simpleClass_appears_in_compositionSeries R s hshead hslast)

/-- A ring that is Noetherian and Artinian on the left has only finitely
many isomorphism classes of simple left modules. -/
theorem finite_simpleModuleClass_of_isNoetherian_isArtinian
    (R : Type u) [Ring R] [IsNoetherianRing R] [IsArtinianRing R] :
    Finite (SimpleModuleClass R) := by
  obtain ⟨s, hshead, hslast⟩ :=
    exists_compositionSeries_of_isNoetherian_isArtinian R R
  exact finite_simpleModuleClass_of_compositionSeries R s hshead hslast

section GroupAlgebra

variable (k G : Type u) [Field k] [Group G] [Finite G]

/-- The simple modules of the group algebra of a finite group form a finite
set of isomorphism classes. -/
noncomputable instance finiteSimpleModuleClassGroupAlgebra :
    Finite (SimpleModuleClass k[G]) := by
  let hNoetherian : IsNoetherianRing k[G] :=
    IsNoetherianRing.of_finite k k[G]
  let hArtinian : IsArtinianRing k[G] :=
    IsArtinianRing.of_finite k k[G]
  exact @finite_simpleModuleClass_of_isNoetherian_isArtinian
    k[G] inferInstance hNoetherian hArtinian

end GroupAlgebra

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
