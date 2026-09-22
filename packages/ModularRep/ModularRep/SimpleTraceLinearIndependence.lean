import ModularRep.ModularTraceFunction
import ModularRep.ModularTraceSeparation
import ModularRep.SimpleModuleClassFinite
import Mathlib.LinearAlgebra.Pi

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

universe u

namespace ModularRep.SimpleTraceLinearIndependence

open FDRepSimpleClassKZero

variable {k G : Type u}
variable [Field k] [IsAlgClosed k] [Group G] [Finite G]

abbrev SimpleIndex := SimpleModuleClass k[G]

abbrev SimpleRepModule (X : SimpleIndex (k := k) (G := G)) :=
  Representation.asModule (simpleClassFDRep X).ρ

omit [IsAlgClosed k] in
theorem nonempty_linearEquiv_simpleRepModule_iff
    (X Y : SimpleIndex (k := k) (G := G)) :
    Nonempty (SimpleRepModule X ≃ₗ[k[G]] SimpleRepModule Y) ↔ X = Y := by
  constructor
  · rintro ⟨e⟩
    apply Subtype.ext
    rw [← toSkeleton_fromSkeleton_obj X.1,
      ← toSkeleton_fromSkeleton_obj Y.1]
    apply congr_toSkeleton_of_iso
    exact (simpleClassFDRepModuleIso X).symm ≪≫
      LinearEquiv.toModuleIso e ≪≫
      simpleClassFDRepModuleIso Y
  · rintro rfl
    exact ⟨LinearEquiv.refl k[G] (SimpleRepModule X)⟩

noncomputable local instance simpleRepModule_isSimple
    (X : SimpleIndex (k := k) (G := G)) :
    IsSimpleModule k[G] (SimpleRepModule X) :=
  simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple X)

abbrev SimpleRepProduct :=
  (X : SimpleIndex (k := k) (G := G)) → SimpleRepModule X

section

variable [DecidableEq (SimpleIndex (k := k) (G := G))]

noncomputable def endComponent
    (e : Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
    (X Y : SimpleIndex (k := k) (G := G)) :
    SimpleRepModule X →ₗ[k[G]] SimpleRepModule Y :=
  (LinearMap.proj Y).comp
    (e.comp (LinearMap.single k[G] SimpleRepModule X))

omit [IsAlgClosed k] in
@[simp]
theorem endComponent_apply
    (e : Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
    (X Y : SimpleIndex (k := k) (G := G)) (v : SimpleRepModule X) :
    endComponent e X Y v = (e (Pi.single X v)) Y := by
  rfl

omit [IsAlgClosed k] in
theorem endComponent_eq_zero_of_ne
    (e : Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
    {X Y : SimpleIndex (k := k) (G := G)} (hXY : X ≠ Y) :
    endComponent e X Y = 0 := by
  rcases LinearMap.bijective_or_eq_zero (endComponent e X Y) with hbij | hzero
  · exfalso
    apply hXY
    exact (nonempty_linearEquiv_simpleRepModule_iff X Y).mp
      ⟨LinearEquiv.ofBijective (endComponent e X Y) hbij⟩
  · exact hzero

theorem exists_endComponent_eq_smul
    (e : Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
    (X : SimpleIndex (k := k) (G := G)) :
    ∃ c : k, endComponent e X X = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := k[G]) (V := SimpleRepModule X) k).2 (endComponent e X X)
  refine ⟨c, ?_⟩
  rw [← hc]
  rfl

omit [IsAlgClosed k] in
theorem end_apply_coord_eq_smul_of_endComponent_eq
    (e : Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
    (Y : SimpleIndex (k := k) (G := G)) (c : k)
    (hc : endComponent e Y Y = c • LinearMap.id)
    (x : SimpleRepProduct (k := k) (G := G)) :
    (e x) Y = c • x Y := by
  classical
  let _ := Fintype.ofFinite (SimpleIndex (k := k) (G := G))
  calc
    (e x) Y = (e (∑ X, Pi.single X (x X))) Y := by
      rw [LinearMap.sum_single_apply]
    _ = ∑ X, endComponent e X Y (x X) := by simp
    _ = endComponent e Y Y (x Y) := by
      apply Finset.sum_eq_single Y
      · intro X _ hXY
        rw [endComponent_eq_zero_of_ne e hXY]
        rfl
      · simp
    _ = c • x Y := by rw [hc]; simp

omit [DecidableEq (SimpleIndex (k := k) (G := G))] in
theorem exists_end_apply_coord_eq_smul
    (e : Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
    (x : SimpleRepProduct (k := k) (G := G))
    (Y : SimpleIndex (k := k) (G := G)) :
    ∃ c : k, (e x) Y = c • x Y := by
  classical
  let _ := Fintype.ofFinite (SimpleIndex (k := k) (G := G))
  obtain ⟨c, hc⟩ := exists_endComponent_eq_smul e Y
  exact ⟨c, end_apply_coord_eq_smul_of_endComponent_eq e Y c hc x⟩

noncomputable def supportedLinearEnd
    (X : SimpleIndex (k := k) (G := G))
    (T : Module.End k (SimpleRepModule X)) :
    Module.End k (SimpleRepProduct (k := k) (G := G)) :=
  (LinearMap.single k SimpleRepModule X).comp
    (T.comp (LinearMap.proj X))

omit [IsAlgClosed k] in
@[simp]
theorem supportedLinearEnd_apply
    (X : SimpleIndex (k := k) (G := G))
    (T : Module.End k (SimpleRepModule X))
    (x : SimpleRepProduct (k := k) (G := G)) :
    supportedLinearEnd X T x = Pi.single X (T (x X)) := by
  rfl

noncomputable def supportedDoubleCentralizerEnd
    (X : SimpleIndex (k := k) (G := G))
    (T : Module.End k (SimpleRepModule X)) :
    Module.End
      (Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
      (SimpleRepProduct (k := k) (G := G)) := by
  classical
  let E := Module.End k[G] (SimpleRepProduct (k := k) (G := G))
  let F := supportedLinearEnd X T
  exact
    { F with
      map_smul' := by
        intro e x
        change F (e x) = e (F x)
        ext Y
        by_cases hYX : Y = X
        · subst Y
          obtain ⟨c, hc⟩ := exists_endComponent_eq_smul e X
          have hcoord : (e x) X = c • x X :=
            end_apply_coord_eq_smul_of_endComponent_eq e X c hc x
          have hdiag (v : SimpleRepModule X) :
              (e (Pi.single X v)) X = c • v := by
            change endComponent e X X v = c • v
            rw [hc]
            simp
          simp only [F, supportedLinearEnd_apply, Pi.single_eq_same]
          rw [hcoord, hdiag]
          exact T.map_smul c (x X)
        · have hoff (v : SimpleRepModule X) :
              (e (Pi.single X v)) Y = 0 := by
            change endComponent e X Y v = 0
            rw [endComponent_eq_zero_of_ne e (Ne.symm hYX)]
            rfl
          simp only [F, supportedLinearEnd_apply, Pi.single_eq_of_ne hYX]
          exact (hoff (T (x X))).symm }

@[simp]
theorem supportedDoubleCentralizerEnd_apply
    (X : SimpleIndex (k := k) (G := G))
    (T : Module.End k (SimpleRepModule X))
    (x : SimpleRepProduct (k := k) (G := G)) :
    supportedDoubleCentralizerEnd X T x = Pi.single X (T (x X)) := by
  rfl

noncomputable local instance simpleRepProduct_moduleFiniteEnd :
    Module.Finite
      (Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
      (SimpleRepProduct (k := k) (G := G)) := by
  let E := Module.End k[G] (SimpleRepProduct (k := k) (G := G))
  refine Module.Finite.of_fg_top ?_
  obtain ⟨s, hs⟩ := Module.Finite.fg_top
    (R := k) (M := SimpleRepProduct (k := k) (G := G))
  exact ⟨s, Submodule.span_eq_top_of_span_eq_top k E
    (s : Set (SimpleRepProduct (k := k) (G := G))) hs⟩

theorem exists_algebra_element_with_supported_action
    (X : SimpleIndex (k := k) (G := G))
    (T : Module.End k (SimpleRepModule X)) :
    ∃ a : k[G],
      (Module.toModuleEnd
          (Module.End k[G] (SimpleRepProduct (k := k) (G := G)))
          (S := k[G]) (SimpleRepProduct (k := k) (G := G))) a =
        supportedDoubleCentralizerEnd X T := by
  exact Module.Finite.toModuleEnd_moduleEnd_surjective
    (supportedDoubleCentralizerEnd X T)

omit [DecidableEq (SimpleIndex (k := k) (G := G))] in
theorem exists_algebra_element_action_eq_and_zero
    (X : SimpleIndex (k := k) (G := G))
    (T : Module.End k (SimpleRepModule X)) :
    ∃ a : k[G],
      (Module.toModuleEnd k (SimpleRepModule X) :
          k[G] →+* Module.End k (SimpleRepModule X)) a = T ∧
      ∀ Y : SimpleIndex (k := k) (G := G), Y ≠ X →
        (Module.toModuleEnd k (SimpleRepModule Y) :
            k[G] →+* Module.End k (SimpleRepModule Y)) a = 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_algebra_element_with_supported_action X T
  refine ⟨a, ?_, ?_⟩
  · ext v
    have hv := LinearMap.congr_fun ha (Pi.single X v)
    have hvX := congrFun hv X
    simpa using hvX
  · intro Y hYX
    ext v
    have hv := LinearMap.congr_fun ha (Pi.single Y v)
    have hvY := congrFun hv Y
    simpa [Pi.single_eq_of_ne hYX] using hvY

end

section

variable [DecidableEq (SimpleIndex (k := k) (G := G))]

theorem exists_algebra_element_with_delta_trace
    (X : SimpleIndex (k := k) (G := G)) :
    ∃ a : k[G], ∀ Y : SimpleIndex (k := k) (G := G),
      LinearMap.trace k (SimpleRepModule Y)
          ((Module.toModuleEnd k (SimpleRepModule Y) :
            k[G] →+* Module.End k (SimpleRepModule Y)) a) =
        if Y = X then 1 else 0 := by
  classical
  let _ : Nontrivial (SimpleRepModule X) :=
    IsSimpleModule.nontrivial k[G] (SimpleRepModule X)
  obtain ⟨T, hT⟩ :=
    ModularTraceSeparation.linearMap_trace_surjective
      (k := k) (W := SimpleRepModule X) 1
  obtain ⟨a, haX, ha0⟩ :=
    exists_algebra_element_action_eq_and_zero X T
  refine ⟨a, fun Y ↦ ?_⟩
  by_cases hYX : Y = X
  · subst Y
    rw [haX, hT, if_pos rfl]
  · rw [ha0 Y hYX, map_zero, if_neg hYX]

theorem exists_algebra_element_with_delta_algebraTraceFunction
    (X : SimpleIndex (k := k) (G := G)) :
    ∃ a : k[G], ∀ Y : SimpleIndex (k := k) (G := G),
      Representation.algebraTraceFunction (simpleClassFDRep Y).ρ a =
        if Y = X then 1 else 0 := by
  obtain ⟨a, ha⟩ := exists_algebra_element_with_delta_trace X
  refine ⟨a, fun Y ↦ ?_⟩
  exact ha Y

end

theorem simpleModuleClass_algebraTraceFunction_linearIndependent :
    LinearIndependent k (fun X : SimpleIndex (k := k) (G := G) ↦
      Representation.algebraTraceFunction (simpleClassFDRep X).ρ) := by
  classical
  let _ := Fintype.ofFinite (SimpleIndex (k := k) (G := G))
  rw [Fintype.linearIndependent_iff]
  intro c hsum X
  obtain ⟨a, ha⟩ :=
    exists_algebra_element_with_delta_algebraTraceFunction X
  have heval := LinearMap.congr_fun hsum a
  simp only [LinearMap.sum_apply, LinearMap.smul_apply] at heval
  rw [Finset.sum_eq_single X] at heval
  · simpa [ha X] using heval
  · intro Y _ hYX
    simp [ha Y, hYX]
  · simp

def restrictAlgebraFunctionalToGroup :
    (k[G] →ₗ[k] k) →ₗ[k] (G → k) where
  toFun f g := f (MonoidAlgebra.single g 1)
  map_add' f h := by
    ext g
    simp
  map_smul' c f := by
    ext g
    simp

omit [IsAlgClosed k] [Finite G] in
theorem restrictAlgebraFunctionalToGroup_injective :
    Function.Injective
      (restrictAlgebraFunctionalToGroup (k := k) (G := G)) := by
  intro f h hfh
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext
  intro c
  have hg := congrFun hfh g
  change f (MonoidAlgebra.single g 1) =
    h (MonoidAlgebra.single g 1) at hg
  have hsingle : MonoidAlgebra.single g c =
      c • MonoidAlgebra.single g (1 : k) := by
    simp
  change f (MonoidAlgebra.single g c) =
    h (MonoidAlgebra.single g c)
  rw [hsingle, map_smul, map_smul, hg]

omit [IsAlgClosed k] in
theorem restrictAlgebraFunctionalToGroup_algebraTraceFunction
    (X : SimpleIndex (k := k) (G := G)) :
    restrictAlgebraFunctionalToGroup
        (Representation.algebraTraceFunction (simpleClassFDRep X).ρ) =
      Representation.character (simpleClassFDRep X).ρ := by
  funext g
  exact Representation.algebraTraceFunction_single_one
    (simpleClassFDRep X).ρ g

omit [IsAlgClosed k] [Finite G] in
theorem linearIndependent_restrictAlgebraFunctionalToGroup
    {ι : Type*} {v : ι → (k[G] →ₗ[k] k)}
    (hv : LinearIndependent k v) :
    LinearIndependent k (fun i ↦
      restrictAlgebraFunctionalToGroup (v i)) := by
  let L := restrictAlgebraFunctionalToGroup (k := k) (G := G)
  have hLker : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.mpr restrictAlgebraFunctionalToGroup_injective
  exact hv.map' L hLker

theorem simpleModuleClass_character_linearIndependent :
    LinearIndependent k (fun X : SimpleIndex (k := k) (G := G) ↦
      Representation.character (simpleClassFDRep X).ρ) := by
  have h := linearIndependent_restrictAlgebraFunctionalToGroup
    (k := k) (G := G)
    (v := fun X : SimpleIndex (k := k) (G := G) ↦
      Representation.algebraTraceFunction (simpleClassFDRep X).ρ)
    simpleModuleClass_algebraTraceFunction_linearIndependent
  simpa only [restrictAlgebraFunctionalToGroup_algebraTraceFunction] using h

end ModularRep.SimpleTraceLinearIndependence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
