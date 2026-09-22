import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Rep.Iso

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.FDRepGroupAlgebraEquivalence

universe u

variable (k G : Type u) [Field k] [Group G] [Finite G]

/-- A finitely generated `k[G]`-module is finite dimensional over `k` when
`G` is finite. -/
theorem restrictScalarsFinite (M : FGModuleCat k[G]) :
    Module.Finite k (RestrictScalars k k[G] M) := by
  let _ : Module k[G] (RestrictScalars k k[G] M) :=
    RestrictScalars.moduleOrig k k[G] M
  let hfinite : Module.Finite k[G] (RestrictScalars k k[G] M) := by
    change Module.Finite k[G] M
    exact M.property
  exact @Module.Finite.trans k k[G] (RestrictScalars k k[G] M)
    _ _ _ _ _ _ _ _ hfinite

/-- The underlying finitely generated group algebra module functor. -/
noncomputable def toFGModule : FDRep k G ⥤ FGModuleCat k[G] :=
  (ModuleCat.isFG k[G]).lift
    (forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra)
    (fun V ↦ Module.Finite.of_restrictScalars_finite k k[G]
      (Representation.asModule V.ρ))

instance : (toFGModule k G).Faithful := by
  let F := forget₂ (FDRep k G) (Rep k G) ⋙
    Rep.toModuleMonoidAlgebra
  constructor
  intro X Y f g h
  apply F.map_injective
  exact congrArg (fun q => q.hom) h

instance : (toFGModule k G).Full := by
  let F := forget₂ (FDRep k G) (Rep k G) ⋙
    Rep.toModuleMonoidAlgebra
  constructor
  intro X Y f
  obtain ⟨g, hg⟩ := F.map_surjective f.hom
  refine ⟨g, ?_⟩
  apply ObjectProperty.hom_ext
  exact hg

/-- Regard a finitely generated `k[G]`-module as a finite-dimensional
representation. -/
noncomputable def ofFGModuleObj (M : FGModuleCat k[G]) : FDRep k G := by
  letI : Module k (RestrictScalars k k[G] M) :=
    RestrictScalars.module k k[G] M
  letI : Module.Finite k (RestrictScalars k k[G] M) :=
    restrictScalarsFinite k G M
  let rho : Representation k G (RestrictScalars k k[G] M) :=
    Representation.ofModule (k := k) (G := G) M
  exact @FDRep.of k G _ _ (RestrictScalars k k[G] M) _
    (RestrictScalars.module k k[G] M)
    (restrictScalarsFinite k G M) rho

/-- The restricted counit of the representation/module equivalence. -/
noncomputable def counitFGIso (M : FGModuleCat k[G]) :
    (toFGModule k G).obj (ofFGModuleObj k G M) ≅ M := by
  letI : Module k (RestrictScalars k k[G] M) :=
    RestrictScalars.module k k[G] M
  letI : Module.Finite k (RestrictScalars k k[G] M) :=
    restrictScalarsFinite k G M
  apply (ModuleCat.isFG k[G]).isoMk
  change
    (Rep.ofModuleMonoidAlgebra ⋙ Rep.toModuleMonoidAlgebra).obj M.obj ≅ M.obj
  exact Rep.counitIso M.obj

noncomputable instance : (toFGModule k G).EssSurj where
  mem_essImage M := ⟨ofFGModuleObj k G M, ⟨counitFGIso k G M⟩⟩

noncomputable instance : (toFGModule k G).IsEquivalence where

/-- For a finite group, finite-dimensional representations are equivalent to
finitely generated modules over the group algebra. -/
noncomputable def equivalenceFGModule : FDRep k G ≌ FGModuleCat k[G] :=
  (toFGModule k G).asEquivalence

end ModularRep.FDRepGroupAlgebraEquivalence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
