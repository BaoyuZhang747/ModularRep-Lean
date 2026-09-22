import ModularRep.FDRepJordanHolderKZero
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Simple-module coordinates for the exact Grothendieck group of `FDRep`

This file refines the Jordan--Hölder map to the free abelian group on
isomorphism classes of simple group algebra modules.  For a finite group, every
simple group algebra module is finitely generated and hence corresponds to a
finite-dimensional representation.
-/

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators MonoidAlgebra SetRel

namespace ModularRep.FDRepSimpleClassKZero

open ExactGrothendieckGroup FDRepJordanHolderKZero JordanHolderCoordinates

universe u

variable (R : Type u) [Ring R]

/-- Isomorphism classes of simple `R`-modules, represented on a skeleton. -/
abbrev SimpleModuleClass :=
  {X : Skeleton (ModuleCat.{u} R) //
    Simple ((fromSkeleton (ModuleCat.{u} R)).obj X)}

/-- The free abelian group on isomorphism classes of simple `R`-modules. -/
abbrev SimpleModuleClassGroup := FreeAbelianGroup (SimpleModuleClass R)

/-- Forget that a module is simple. -/
def simpleClassForget (X : SimpleModuleClass R) :
    Skeleton (ModuleCat.{u} R) := X.1

/-- Include the free group on simple-module classes in the free group on all
module classes. -/
noncomputable def simpleClassInclusion :
    SimpleModuleClassGroup R →+
      FreeClassGroup (ModuleCat.{u} R) :=
  FreeAbelianGroup.map (simpleClassForget R)

/-- Send a module class to the corresponding simple generator when it is
simple, and to zero otherwise. -/
noncomputable def simpleClassGeneratorProjection
    (X : Skeleton (ModuleCat.{u} R)) : SimpleModuleClassGroup R := by
  classical
  exact if h : Simple ((fromSkeleton (ModuleCat.{u} R)).obj X)
    then FreeAbelianGroup.of ⟨X, h⟩
    else 0

/-- Project the free group on all module classes onto its simple generators. -/
noncomputable def simpleClassProjection :
    FreeClassGroup (ModuleCat.{u} R) →+ SimpleModuleClassGroup R :=
  FreeAbelianGroup.lift (simpleClassGeneratorProjection R)

@[simp]
theorem simpleClassProjection_of_forget (X : SimpleModuleClass R) :
    simpleClassProjection R
        (FreeAbelianGroup.of (simpleClassForget R X)) =
      FreeAbelianGroup.of X := by
  classical
  simp [simpleClassProjection, simpleClassGeneratorProjection,
    simpleClassForget, X.2]

/-- Projection is a left inverse to inclusion. -/
theorem simpleClassProjection_inclusion (x : SimpleModuleClassGroup R) :
    simpleClassProjection R (simpleClassInclusion R x) = x := by
  refine FreeAbelianGroup.induction_on x ?_ ?_ ?_ ?_
  · rfl
  · intro X
    rw [simpleClassInclusion, FreeAbelianGroup.map_of_apply,
      simpleClassProjection_of_forget]
  · intro x hx
    simpa only [map_neg] using congrArg Neg.neg hx
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (.+.) hx hy

section Factors

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The simple-module class of one factor of a composition series. -/
noncomputable def compositionFactorSimpleClass
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    SimpleModuleClass R := by
  let Q := ModuleCat.of R (compositionFactor s i)
  let _ : Simple Q := by
    change Simple (ModuleCat.of R (compositionFactor s i))
    let _ : IsSimpleModule R (compositionFactor s i) :=
      compositionFactor_isSimple s i
    infer_instance
  exact ⟨toSkeleton Q, Simple.of_iso (fromSkeletonToSkeletonIso Q)⟩

/-- The Jordan--Hölder factor sum with generators restricted to simple module
classes. -/
noncomputable def compositionFactorSimpleSum
    (s : CompositionSeries (Submodule R M)) : SimpleModuleClassGroup R :=
  ∑ i : Fin s.length, FreeAbelianGroup.of (compositionFactorSimpleClass R s i)

/-- Including the simple factor sum recovers the factor sum in the free group
on all module classes. -/
theorem simpleClassInclusion_compositionFactorSimpleSum
    (s : CompositionSeries (Submodule R M)) :
    simpleClassInclusion R (compositionFactorSimpleSum R s) =
      compositionFactorIsoSum s := by
  classical
  unfold compositionFactorSimpleSum compositionFactorIsoSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [simpleClassInclusion, FreeAbelianGroup.map_of_apply]
  rfl

/-- Projecting the unrestricted factor sum gives the factor sum on simple
module classes. -/
theorem simpleClassProjection_compositionFactorIsoSum
    (s : CompositionSeries (Submodule R M)) :
    simpleClassProjection R (compositionFactorIsoSum s) =
      compositionFactorSimpleSum R s := by
  apply (congrArg (simpleClassProjection R)
    (simpleClassInclusion_compositionFactorSimpleSum R s)).symm.trans
  exact simpleClassProjection_inclusion R _

/-- A full composition series of a simple module has one factor. -/
theorem compositionSeries_length_eq_one_of_simple
    [IsSimpleModule R M]
    (s : CompositionSeries (Submodule R M))
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    s.length = 1 := by
  rw [← ENat.natCast_inj]
  calc
    (s.length : ENat) = Module.length R M :=
      Module.length_compositionSeries s hhead hlast
    _ = 1 := Module.length_eq_one R M
    _ = (1 : ℕ) := rfl

/-- The unique factor of a full composition series of a simple module is the
module itself. -/
noncomputable def compositionFactorEquivOfSimple
    [IsSimpleModule R M]
    (s : CompositionSeries (Submodule R M))
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    compositionFactor s
        (Fin.cast (compositionSeries_length_eq_one_of_simple R s hhead hlast).symm 0) ≃ₗ[R] M := by
  let hlen := compositionSeries_length_eq_one_of_simple R s hhead hlast
  let i : Fin s.length := Fin.cast hlen.symm 0
  have hlow : s (Fin.castSucc i) = ⊥ := by
    rw [← hhead]
    apply congrArg s
    apply Fin.ext
    rfl
  have hupp : s (Fin.succ i) = ⊤ := by
    rw [← hlast]
    apply congrArg s
    apply Fin.ext
    simpa [i] using hlen.symm
  change
    (s (Fin.succ i) ⧸
      (s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype) ≃ₗ[R] M
  rw [hlow, hupp]
  exact (Submodule.quotEquivOfEqBot _ (by ext; simp)).trans
    Submodule.topEquiv

/-- The simple-class factor sum of a full composition series of a simple
module is its own isomorphism class. -/
theorem compositionFactorSimpleSum_of_simple
    [IsSimpleModule R M]
    (s : CompositionSeries (Submodule R M))
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    compositionFactorSimpleSum R s =
      FreeAbelianGroup.of
        ⟨toSkeleton (ModuleCat.of R M),
          Simple.of_iso (fromSkeletonToSkeletonIso (ModuleCat.of R M))⟩ := by
  classical
  let hlen := compositionSeries_length_eq_one_of_simple R s hhead hlast
  unfold compositionFactorSimpleSum
  calc
    (∑ i : Fin s.length,
        FreeAbelianGroup.of (compositionFactorSimpleClass R s i)) =
        ∑ _j : Fin 1, FreeAbelianGroup.of
          ⟨toSkeleton (ModuleCat.of R M),
            Simple.of_iso (fromSkeletonToSkeletonIso (ModuleCat.of R M))⟩ := by
      apply Fintype.sum_equiv (Fin.castOrderIso hlen).toEquiv
      intro i
      apply congrArg FreeAbelianGroup.of
      apply Subtype.ext
      apply congr_toSkeleton_of_iso
      have hi : i = Fin.cast hlen.symm 0 := by
        apply Fin.ext
        omega
      subst i
      exact (compositionFactorEquivOfSimple R s hhead hlast).toModuleIso
    _ = FreeAbelianGroup.of
          ⟨toSkeleton (ModuleCat.of R M),
            Simple.of_iso (fromSkeletonToSkeletonIso (ModuleCat.of R M))⟩ := by
      rw [Fin.sum_univ_one]

/-- Appending one term appends the class of the final factor to the simple
factor sum. -/
theorem compositionFactorSimpleSum_snoc
    (s : CompositionSeries (Submodule R M))
    (N : Submodule R M) (h : s.last ⋖ N) :
    compositionFactorSimpleSum R (s.snoc N h) =
      compositionFactorSimpleSum R s +
        FreeAbelianGroup.of
          (compositionFactorSimpleClass R (s.snoc N h)
            (Fin.cast (RelSeries.snoc_length s N h).symm (Fin.last s.length))) := by
  classical
  let hlen := RelSeries.snoc_length s N h
  let lastIndex : Fin (s.snoc N h).length :=
    Fin.cast hlen.symm (Fin.last s.length)
  unfold compositionFactorSimpleSum
  calc
    (∑ i : Fin (s.snoc N h).length,
        FreeAbelianGroup.of (compositionFactorSimpleClass R (s.snoc N h) i)) =
        ∑ j : Fin (s.length + 1),
          FreeAbelianGroup.of
            (compositionFactorSimpleClass R (s.snoc N h) (Fin.cast hlen.symm j)) := by
      apply Fintype.sum_equiv (Fin.castOrderIso hlen).toEquiv
      intro i
      congr 2
    _ = (∑ i : Fin s.length,
          FreeAbelianGroup.of (compositionFactorSimpleClass R s i)) +
        FreeAbelianGroup.of
          (compositionFactorSimpleClass R (s.snoc N h) lastIndex) := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      apply Fintype.sum_congr
      intro i
      apply congrArg FreeAbelianGroup.of
      apply Subtype.ext
      let j : Fin (s.snoc N h).length := Fin.cast hlen.symm i.castSucc
      have hlow : (s.snoc N h) (Fin.castSucc j) = s (Fin.castSucc i) := by
        have hj : Fin.castSucc j = (Fin.castSucc i).castSucc := by
          apply Fin.ext
          rfl
        rw [hj]
        exact RelSeries.snoc_castSucc s N h (Fin.castSucc i)
      have hupp : (s.snoc N h) (Fin.succ j) = s (Fin.succ i) := by
        have hj : Fin.succ j = (Fin.succ i).castSucc := by
          apply Fin.ext
          rfl
        rw [hj]
        exact RelSeries.snoc_castSucc s N h (Fin.succ i)
      change
        toSkeleton (ModuleCat.of R (compositionFactor (s.snoc N h) j)) =
          toSkeleton (ModuleCat.of R (compositionFactor s i))
      apply congr_toSkeleton_of_iso
      let e := LinearEquiv.ofEq
        ((s.snoc N h) (Fin.succ j)) (s (Fin.succ i)) hupp
      exact (Submodule.Quotient.equiv
        ((s.snoc N h) (Fin.castSucc j) |>.comap
          ((s.snoc N h) (Fin.succ j)).subtype)
        (s (Fin.castSucc i) |>.comap (s (Fin.succ i)).subtype)
        e (by
          ext y
          constructor
          · intro hy
            rcases Submodule.mem_map.mp hy with ⟨x, hx, hxy⟩
            change (y : M) ∈ s (Fin.castSucc i)
            rw [← hxy]
            change (x : M) ∈ s (Fin.castSucc i)
            rw [← hlow]
            exact hx
          · intro hy
            let x : (s.snoc N h) (Fin.succ j) :=
              ⟨y, by rw [hupp]; exact y.2⟩
            apply Submodule.mem_map.mpr
            refine ⟨x, ?_, ?_⟩
            · change (x : M) ∈ (s.snoc N h) (Fin.castSucc j)
              rw [hlow]
              exact hy
            · apply Subtype.ext
              rfl)).toModuleIso

end Factors

section FGSeries

variable {R M : Type u} [Ring R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A term of a composition series, regarded as a finitely generated module. -/
noncomputable def compositionSeriesTermFGModule
    (s : CompositionSeries (Submodule R M)) (j : Fin (s.length + 1)) :
    FGModuleCat R :=
  FGModuleCat.of R (s j)

/-- A factor of a composition series, regarded as a finitely generated
module. -/
noncomputable def compositionFactorFGModule
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    FGModuleCat R := by
  letI : IsSimpleModule R (compositionFactor s i) :=
    compositionFactor_isSimple s i
  exact FGModuleCat.of R (compositionFactor s i)

/-- The short complex in finitely generated modules attached to one step of a
composition series. -/
noncomputable def compositionStepFGShortComplex
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    ShortComplex (FGModuleCat R) :=
  ShortComplex.mk
    (FGModuleCat.ofHom
      (Submodule.inclusion (s.step i).le))
    (FGModuleCat.ofHom
      ((s (Fin.castSucc i)).comap (s (Fin.succ i)).subtype).mkQ)
    (by
      ext x
      change Submodule.Quotient.mk
        (⟨x.1, (s.step i).le x.2⟩ : s (Fin.succ i)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact x.2)

/-- The complex attached to a composition-series step is short exact in the
category of finitely generated modules. -/
theorem compositionStepFGShortComplex_shortExact
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (compositionStepFGShortComplex s i).ShortExact := by
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
    (S := compositionStepFGShortComplex s i)
  change (compositionStepShortComplex s i).ShortExact
  exact compositionStepShortComplex_shortExact s i

end FGSeries

section FDRep

variable {k G : Type u} [Field k] [Group G] [Finite G]

noncomputable local instance : IsNoetherianRing k[G] :=
  IsNoetherianRing.of_finite k k[G]

noncomputable local instance fdRepGroupAlgebraModuleFinite (V : FDRep k G) :
    Module.Finite k[G] (Representation.asModule V.ρ) :=
  (FDRepGroupAlgebraEquivalence.toFGModule k G).obj V |>.property

/-- A simple module class, regarded as a finitely generated group algebra
module. -/
noncomputable def simpleClassFGModule
    (X : SimpleModuleClass k[G]) : FGModuleCat k[G] := by
  let M := (fromSkeleton (ModuleCat.{u} k[G])).obj X.1
  letI : Simple M := X.2
  letI : IsSimpleModule k[G] M := inferInstance
  exact FGModuleCat.of k[G] M

/-- The finite-dimensional representation corresponding to a simple
group algebra module class. -/
noncomputable def simpleClassFDRep
    (X : SimpleModuleClass k[G]) : FDRep k G :=
  (FDRepGroupAlgebraEquivalence.equivalenceFGModule k G).inverse.obj
    (simpleClassFGModule X)

/-- The group algebra module underlying `simpleClassFDRep X` is isomorphic to
the module represented by `X`. -/
noncomputable def simpleClassFDRepModuleIso
    (X : SimpleModuleClass k[G]) :
    (FDRepFiniteLength.toModuleMonoidAlgebra (k := k) (G := G)).obj
        (simpleClassFDRep X) ≅
      (fromSkeleton (ModuleCat.{u} k[G])).obj X.1 := by
  let e :=
    (FDRepGroupAlgebraEquivalence.equivalenceFGModule k G).counitIso.app
      (simpleClassFGModule X)
  exact (forget₂ (FGModuleCat k[G]) (ModuleCat k[G])).mapIso e

/-- A simple module class determines the exact-`K₀` class of its associated
finite-dimensional representation. -/
noncomputable def simpleClassToFDRepKZeroGenerator
    (X : SimpleModuleClass k[G]) : FDRepKZero k G :=
  ExactGrothendieckGroup.classOf (FDRep k G) (simpleClassFDRep X)

/-- Extend simple generators linearly to the exact Grothendieck group. -/
noncomputable def simpleClassToFDRepKZero :
    SimpleModuleClassGroup k[G] →+ FDRepKZero k G :=
  FreeAbelianGroup.lift simpleClassToFDRepKZeroGenerator

/-- Send a simple module class to its class in the exact Grothendieck group of
finitely generated group algebra modules. -/
noncomputable def simpleClassToFGModuleKZero :
    SimpleModuleClassGroup k[G] →+
      KZero (FGModuleCat k[G]) :=
  FreeAbelianGroup.lift (fun X ↦
    ExactGrothendieckGroup.classOf (FGModuleCat k[G]) (simpleClassFGModule X))

/-- The finitely generated module chosen from the simple class of a
composition factor is isomorphic to that factor. -/
noncomputable def simpleClassFGModuleFactorIso
    {M : Type u} [AddCommGroup M] [Module k[G] M] [Module.Finite k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) :
    simpleClassFGModule (compositionFactorSimpleClass k[G] s i) ≅
      compositionFactorFGModule s i := by
  apply (ModuleCat.isFG k[G]).isoMk
  exact fromSkeletonToSkeletonIso (ModuleCat.of k[G] (compositionFactor s i))

/-- A simple factor generator maps to the exact-`K₀` class of that factor. -/
theorem simpleClassToFGModuleKZero_factor
    {M : Type u} [AddCommGroup M] [Module k[G] M] [Module.Finite k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) :
    simpleClassToFGModuleKZero
        (FreeAbelianGroup.of (compositionFactorSimpleClass k[G] s i)) =
      ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (compositionFactorFGModule s i) := by
  rw [simpleClassToFGModuleKZero, FreeAbelianGroup.lift_apply_of]
  exact ExactGrothendieckGroup.classOf_iso (FGModuleCat k[G])
    (simpleClassFGModuleFactorIso s i)

/-- One composition-series step gives the corresponding relation in the
exact Grothendieck group of finitely generated modules. -/
theorem compositionStepFGKZero_relation
    {M : Type u} [AddCommGroup M] [Module k[G] M] [Module.Finite k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) (i : Fin s.length) :
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (compositionSeriesTermFGModule s (Fin.succ i)) =
      ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionSeriesTermFGModule s (Fin.castSucc i)) +
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionFactorFGModule s i) :=
  ExactGrothendieckGroup.classOf_middle_eq (FGModuleCat k[G])
    (compositionStepFGShortComplex s i)
    (compositionStepFGShortComplex_shortExact s i)

/-- The exact-`K₀` relation for the last step of an appended composition
series. -/
theorem compositionStepFGKZero_relation_snoc
    {M : Type u} [AddCommGroup M] [Module k[G] M] [Module.Finite k[G] M]
    (s : CompositionSeries (Submodule k[G] M))
    (N : Submodule k[G] M) (h : s.last ⋖ N) :
    ExactGrothendieckGroup.classOf (FGModuleCat k[G]) (FGModuleCat.of k[G] N) =
      ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (FGModuleCat.of k[G] s.last) +
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionFactorFGModule (s.snoc N h)
            (Fin.cast (RelSeries.snoc_length s N h).symm (Fin.last s.length))) := by
  let j : Fin (s.snoc N h).length :=
    Fin.cast (RelSeries.snoc_length s N h).symm (Fin.last s.length)
  have hstep := compositionStepFGKZero_relation (s.snoc N h) j
  have hupp : (s.snoc N h) (Fin.succ j) = N := by
    calc
      (s.snoc N h) (Fin.succ j) = (s.snoc N h).last := by
        apply congrArg (s.snoc N h)
        apply Fin.ext
        rfl
      _ = N := RelSeries.last_snoc s N h
  have hlow : (s.snoc N h) (Fin.castSucc j) = s.last := by
    calc
      (s.snoc N h) (Fin.castSucc j) =
          (s.snoc N h) (Fin.last s.length).castSucc := by
        apply congrArg (s.snoc N h)
        apply Fin.ext
        rfl
      _ = s (Fin.last s.length) :=
        RelSeries.snoc_castSucc s N h (Fin.last s.length)
      _ = s.last := rfl
  have hupperClass :
      ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionSeriesTermFGModule (s.snoc N h) (Fin.succ j)) =
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (FGModuleCat.of k[G] N) := by
    apply ExactGrothendieckGroup.classOf_iso
    exact (LinearEquiv.ofEq _ _ hupp).toFGModuleCatIso
  have hlowerClass :
      ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionSeriesTermFGModule (s.snoc N h) (Fin.castSucc j)) =
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (FGModuleCat.of k[G] s.last) := by
    apply ExactGrothendieckGroup.classOf_iso
    exact (LinearEquiv.ofEq _ _ hlow).toFGModuleCatIso
  calc
    ExactGrothendieckGroup.classOf (FGModuleCat k[G]) (FGModuleCat.of k[G] N) =
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionSeriesTermFGModule (s.snoc N h) (Fin.succ j)) :=
      hupperClass.symm
    _ = ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionSeriesTermFGModule (s.snoc N h) (Fin.castSucc j)) +
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionFactorFGModule (s.snoc N h) j) := hstep
    _ = ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (FGModuleCat.of k[G] s.last) +
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (compositionFactorFGModule (s.snoc N h) j) := by
      rw [hlowerClass]

/-- In the exact Grothendieck group of finitely generated modules, the class
of the final term of a composition series is the class of its initial term
plus the sum of its simple factors. -/
theorem compositionSeriesFGKZero_decomposition
    {M : Type u} [AddCommGroup M] [Module k[G] M] [Module.Finite k[G] M]
    (s : CompositionSeries (Submodule k[G] M)) :
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] s.last) =
      ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (FGModuleCat.of k[G] s.head) +
        simpleClassToFGModuleKZero (compositionFactorSimpleSum k[G] s) := by
  induction s using RelSeries.inductionOn' with
  | singleton N =>
      rw [RelSeries.head_singleton, RelSeries.last_singleton]
      change
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
            (FGModuleCat.of k[G] N) =
          ExactGrothendieckGroup.classOf (FGModuleCat k[G])
              (FGModuleCat.of k[G] N) +
            simpleClassToFGModuleKZero 0
      simp
  | snoc s N h ih =>
      rw [RelSeries.last_snoc, RelSeries.head_snoc,
        compositionFactorSimpleSum_snoc, map_add,
        simpleClassToFGModuleKZero_factor]
      calc
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
            (FGModuleCat.of k[G] N) =
            ExactGrothendieckGroup.classOf (FGModuleCat k[G])
                (FGModuleCat.of k[G] s.last) +
              ExactGrothendieckGroup.classOf (FGModuleCat k[G])
                (compositionFactorFGModule (s.snoc N h)
                  (Fin.cast (RelSeries.snoc_length s N h).symm
                    (Fin.last s.length))) :=
          compositionStepFGKZero_relation_snoc s N h
        _ = (ExactGrothendieckGroup.classOf (FGModuleCat k[G])
                (FGModuleCat.of k[G] s.head) +
              simpleClassToFGModuleKZero
                (compositionFactorSimpleSum k[G] s)) +
              ExactGrothendieckGroup.classOf (FGModuleCat k[G])
                (compositionFactorFGModule (s.snoc N h)
                  (Fin.cast (RelSeries.snoc_length s N h).symm
                    (Fin.last s.length))) := by
          rw [ih]
        _ = ExactGrothendieckGroup.classOf (FGModuleCat k[G])
                (FGModuleCat.of k[G] s.head) +
              (simpleClassToFGModuleKZero
                  (compositionFactorSimpleSum k[G] s) +
                ExactGrothendieckGroup.classOf (FGModuleCat k[G])
                  (compositionFactorFGModule (s.snoc N h)
                    (Fin.cast (RelSeries.snoc_length s N h).symm
                      (Fin.last s.length)))) := by
          rw [add_assoc]

/-- The homomorphism on exact Grothendieck groups induced by the inverse of
the representation/group algebra-module equivalence. -/
noncomputable def fgModuleToFDRepKZero :
    KZero (FGModuleCat k[G]) →+ FDRepKZero k G :=
  ExactGrothendieckGroup.map
    (FDRepGroupAlgebraEquivalence.equivalenceFGModule k G).inverse

/-- The induced homomorphism sends a module class to the class of its inverse
image representation. -/
@[simp]
theorem fgModuleToFDRepKZero_classOf (M : FGModuleCat k[G]) :
    fgModuleToFDRepKZero
        (ExactGrothendieckGroup.classOf (FGModuleCat k[G]) M) =
      ExactGrothendieckGroup.classOf (FDRep k G)
        ((FDRepGroupAlgebraEquivalence.equivalenceFGModule k G).inverse.obj M) :=
  ExactGrothendieckGroup.map_classOf
    (FDRepGroupAlgebraEquivalence.equivalenceFGModule k G).inverse M

/-- Mapping simple module generators through the inverse equivalence agrees
with their directly defined representation classes. -/
theorem fgModuleToFDRepKZero_simpleClassToFGModuleKZero
    (x : SimpleModuleClassGroup k[G]) :
    fgModuleToFDRepKZero (simpleClassToFGModuleKZero x) =
      simpleClassToFDRepKZero x := by
  refine FreeAbelianGroup.induction_on x ?_ ?_ ?_ ?_
  · rfl
  · intro X
    rw [simpleClassToFGModuleKZero, simpleClassToFDRepKZero,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      fgModuleToFDRepKZero_classOf]
    rfl
  · intro X hX
    simpa only [map_neg] using congrArg Neg.neg hX
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (.+.) hx hy

/-- A concrete zero object in finitely generated group algebra modules. -/
noncomputable def zeroFGModule : FGModuleCat k[G] :=
  FGModuleCat.of k[G] PUnit.{u + 1}

/-- The all-zero short complex used to prove that the zero-object class
vanishes in exact `K₀`. -/
noncomputable def zeroFGShortComplex : ShortComplex (FGModuleCat k[G]) :=
  ShortComplex.mk
    (0 : zeroFGModule ⟶ zeroFGModule)
    (0 : zeroFGModule ⟶ zeroFGModule)
    (by simp)

/-- The all-zero complex on the zero module is short exact. -/
theorem zeroFGShortComplex_shortExact :
    (zeroFGShortComplex (k := k) (G := G)).ShortExact := by
  let Z : ModuleCat.{u} k[G] := ModuleCat.of k[G] PUnit.{u + 1}
  let T : ShortComplex (ModuleCat.{u} k[G]) :=
    ShortComplex.mk (0 : Z ⟶ Z) (0 : Z ⟶ Z) (by simp)
  have hT : T.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · intro y
      constructor
      · intro _
        exact ⟨0, Subsingleton.elim _ _⟩
      · intro _
        exact Subsingleton.elim _ _
    · intro x y _
      exact Subsingleton.elim _ _
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (F := forget₂ (FGModuleCat.{u} k[G]) (ModuleCat.{u} k[G]))
    (S := zeroFGShortComplex (k := k) (G := G))
  change T.ShortExact
  exact hT

/-- The class of the concrete zero module is zero in exact `K₀`. -/
theorem classOf_zeroFGModule :
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (zeroFGModule (k := k) (G := G)) = 0 := by
  let c := ExactGrothendieckGroup.classOf (FGModuleCat k[G])
    (zeroFGModule (k := k) (G := G))
  have h : c = c + c :=
    ExactGrothendieckGroup.classOf_middle_eq (FGModuleCat k[G])
      (zeroFGShortComplex (k := k) (G := G))
      zeroFGShortComplex_shortExact
  have h' : c + 0 = c + c := by simpa using h
  exact (add_left_cancel h').symm

/-- The class of the bottom submodule is zero. -/
theorem classOf_botFGModule
    {M : Type u} [AddCommGroup M] [Module k[G] M] [Module.Finite k[G] M] :
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] (⊥ : Submodule k[G] M)) = 0 := by
  calc
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] (⊥ : Submodule k[G] M)) =
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (zeroFGModule (k := k) (G := G)) := by
      apply ExactGrothendieckGroup.classOf_iso
      exact (Submodule.botEquivPUnit (R := k[G]) (M := M)).toFGModuleCatIso
    _ = 0 := classOf_zeroFGModule

/-- The full submodule has the same exact-`K₀` class as its ambient module. -/
theorem classOf_topFGModule
    {M : Type u} [AddCommGroup M] [Module k[G] M] [Module.Finite k[G] M] :
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] (⊤ : Submodule k[G] M)) =
      ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] M) := by
  apply ExactGrothendieckGroup.classOf_iso
  exact (Submodule.topEquiv (R := k[G]) (M := M)).toFGModuleCatIso

/-- The group algebra module underlying the representation attached to a
simple class is simple. -/
theorem simpleClassFDRep_underlying_simple
    (X : SimpleModuleClass k[G]) :
    Simple
      ((FDRepFiniteLength.toModuleMonoidAlgebra (k := k) (G := G)).obj
        (simpleClassFDRep X)) := by
  let _ : Simple ((fromSkeleton (ModuleCat.{u} k[G])).obj X.1) := X.2
  exact Simple.of_iso (simpleClassFDRepModuleIso X)

/-- The Jordan--Hölder homomorphism with target generated only by simple
`k[G]`-module classes. -/
noncomputable def fdRepSimpleJordanHolderHom :
    FDRepKZero k G →+ SimpleModuleClassGroup k[G] :=
  (simpleClassProjection k[G]).comp fdRepJordanHolderKZeroHom

/-- On a representation class, the simple-class homomorphism is its chosen
composition-factor sum. -/
@[simp]
theorem fdRepSimpleJordanHolderHom_classOf (V : FDRep k G) :
    fdRepSimpleJordanHolderHom
        (ExactGrothendieckGroup.classOf (FDRep k G) V) =
      compositionFactorSimpleSum k[G] (chosenFDRepCompositionSeries V) := by
  rw [fdRepSimpleJordanHolderHom, AddMonoidHom.comp_apply,
    fdRepJordanHolderKZeroHom_classOf]
  unfold fdRepJordanHolderSum
  exact simpleClassProjection_compositionFactorIsoSum k[G]
    (chosenFDRepCompositionSeries V)

/-- The final term of the chosen composition series represents the underlying
finitely generated group algebra module. -/
theorem chosenFDRepCompositionSeries_last_class (V : FDRep k G) :
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] (chosenFDRepCompositionSeries V).last) =
      ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        ((FDRepGroupAlgebraEquivalence.equivalenceFGModule k G).functor.obj V) := by
  calc
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] (chosenFDRepCompositionSeries V).last) =
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (FGModuleCat.of k[G]
            (⊤ : Submodule k[G] (Representation.asModule V.ρ))) := by
      apply ExactGrothendieckGroup.classOf_iso
      exact (LinearEquiv.ofEq _ _
        (chosenFDRepCompositionSeries_last V)).toFGModuleCatIso
    _ = ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (FGModuleCat.of k[G] (Representation.asModule V.ρ)) :=
      classOf_topFGModule
    _ = ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          ((FDRepGroupAlgebraEquivalence.equivalenceFGModule k G).functor.obj V) := by
      rfl

/-- The initial term of the chosen composition series has zero exact-`K₀`
class. -/
theorem chosenFDRepCompositionSeries_head_class (V : FDRep k G) :
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] (chosenFDRepCompositionSeries V).head) = 0 := by
  calc
    ExactGrothendieckGroup.classOf (FGModuleCat k[G])
        (FGModuleCat.of k[G] (chosenFDRepCompositionSeries V).head) =
        ExactGrothendieckGroup.classOf (FGModuleCat k[G])
          (FGModuleCat.of k[G]
            (⊥ : Submodule k[G] (Representation.asModule V.ρ))) := by
      apply ExactGrothendieckGroup.classOf_iso
      exact (LinearEquiv.ofEq _ _
        (chosenFDRepCompositionSeries_head V)).toFGModuleCatIso
    _ = 0 := classOf_botFGModule

/-- The exact-`K₀` class of a representation is the sum of the classes of the
simple factors in its chosen composition series. -/
theorem simpleClassToFDRepKZero_compositionFactorSimpleSum
    (V : FDRep k G) :
    simpleClassToFDRepKZero
        (compositionFactorSimpleSum k[G] (chosenFDRepCompositionSeries V)) =
      ExactGrothendieckGroup.classOf (FDRep k G) V := by
  let E := FDRepGroupAlgebraEquivalence.equivalenceFGModule k G
  have hFG :
      ExactGrothendieckGroup.classOf (FGModuleCat k[G]) (E.functor.obj V) =
        simpleClassToFGModuleKZero
          (compositionFactorSimpleSum k[G] (chosenFDRepCompositionSeries V)) := by
    rw [← chosenFDRepCompositionSeries_last_class V,
      compositionSeriesFGKZero_decomposition,
      chosenFDRepCompositionSeries_head_class, zero_add]
  calc
    simpleClassToFDRepKZero
        (compositionFactorSimpleSum k[G] (chosenFDRepCompositionSeries V)) =
        fgModuleToFDRepKZero
          (simpleClassToFGModuleKZero
            (compositionFactorSimpleSum k[G]
              (chosenFDRepCompositionSeries V))) := by
      rw [fgModuleToFDRepKZero_simpleClassToFGModuleKZero]
    _ = fgModuleToFDRepKZero
          (ExactGrothendieckGroup.classOf (FGModuleCat k[G])
            (E.functor.obj V)) := congrArg fgModuleToFDRepKZero hFG.symm
    _ = ExactGrothendieckGroup.classOf (FDRep k G)
          (E.inverse.obj (E.functor.obj V)) :=
      fgModuleToFDRepKZero_classOf (E.functor.obj V)
    _ = ExactGrothendieckGroup.classOf (FDRep k G) V :=
      (ExactGrothendieckGroup.classOf_iso (FDRep k G)
        (E.unitIso.app V)).symm

/-- The map from simple generators is a left inverse to the simple-class
Jordan--Hölder homomorphism on object classes. -/
theorem simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom_classOf
    (V : FDRep k G) :
    simpleClassToFDRepKZero
        (fdRepSimpleJordanHolderHom
          (ExactGrothendieckGroup.classOf (FDRep k G) V)) =
      ExactGrothendieckGroup.classOf (FDRep k G) V := by
  rw [fdRepSimpleJordanHolderHom_classOf,
    simpleClassToFDRepKZero_compositionFactorSimpleSum]

/-- A simple generator is recovered from the exact-`K₀` class of its
associated representation. -/
@[simp]
theorem fdRepSimpleJordanHolderHom_simpleClassGenerator
    (X : SimpleModuleClass k[G]) :
    fdRepSimpleJordanHolderHom (simpleClassToFDRepKZeroGenerator X) =
      FreeAbelianGroup.of X := by
  let hSimple :
      IsSimpleModule k[G]
        (Representation.asModule (simpleClassFDRep X).ρ) :=
    simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple X)
  let _ : IsSimpleModule k[G]
      (Representation.asModule (simpleClassFDRep X).ρ) := hSimple
  rw [fdRepSimpleJordanHolderHom, AddMonoidHom.comp_apply,
    simpleClassToFDRepKZeroGenerator, fdRepJordanHolderKZeroHom_classOf]
  unfold fdRepJordanHolderSum
  rw [simpleClassProjection_compositionFactorIsoSum,
    compositionFactorSimpleSum_of_simple k[G]
      (chosenFDRepCompositionSeries (simpleClassFDRep X))
      (chosenFDRepCompositionSeries_head (simpleClassFDRep X))
      (chosenFDRepCompositionSeries_last (simpleClassFDRep X))]
  apply congrArg FreeAbelianGroup.of
  apply Subtype.ext
  change
    toSkeleton
        ((FDRepFiniteLength.toModuleMonoidAlgebra (k := k) (G := G)).obj
          (simpleClassFDRep X)) = X.1
  rw [congr_toSkeleton_of_iso (simpleClassFDRepModuleIso X),
    toSkeleton_fromSkeleton_obj]

/-- The simple-class Jordan--Hölder map is a left inverse to the map sending
simple generators to their representation classes. -/
theorem fdRepSimpleJordanHolderHom_simpleClassToFDRepKZero
    (x : SimpleModuleClassGroup k[G]) :
    fdRepSimpleJordanHolderHom (simpleClassToFDRepKZero x) = x := by
  refine FreeAbelianGroup.induction_on x ?_ ?_ ?_ ?_
  · rfl
  · intro X
    rw [simpleClassToFDRepKZero, FreeAbelianGroup.lift_apply_of,
      fdRepSimpleJordanHolderHom_simpleClassGenerator]
  · intro X hX
    simpa only [map_neg] using congrArg Neg.neg hX
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (.+.) hx hy

/-- The map from simple generators is a left inverse to the simple-class
Jordan--Hölder homomorphism on the whole exact Grothendieck group. -/
theorem simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom
    (x : FDRepKZero k G) :
    simpleClassToFDRepKZero (fdRepSimpleJordanHolderHom x) = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro x
  refine FreeAbelianGroup.induction_on x ?_ ?_ ?_ ?_
  · simp
  · intro X
    let V := (fromSkeleton (FDRep k G)).obj X
    rw [← toSkeleton_fromSkeleton_obj X]
    change simpleClassToFDRepKZero
        (fdRepSimpleJordanHolderHom
          (ExactGrothendieckGroup.classOf (FDRep k G) V)) =
      ExactGrothendieckGroup.classOf (FDRep k G) V
    exact simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom_classOf V
  · intro x hx
    simpa using congrArg Neg.neg hx
  · intro x y hx hy
    simpa using congrArg₂ (.+.) hx hy

/-- The exact Grothendieck group of finite-dimensional representations of a
finite group is freely generated by isomorphism classes of simple
group algebra modules. -/
noncomputable def fdRepKZeroEquivSimpleModuleClassGroup :
    FDRepKZero k G ≃+ SimpleModuleClassGroup k[G] where
  toFun := fdRepSimpleJordanHolderHom
  invFun := simpleClassToFDRepKZero
  left_inv := simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom
  right_inv := fdRepSimpleJordanHolderHom_simpleClassToFDRepKZero
  map_add' := map_add fdRepSimpleJordanHolderHom

/-- The simple-class Jordan--Hölder homomorphism factors the unrestricted
factor-sum homomorphism through the inclusion of simple classes. -/
theorem simpleClassInclusion_fdRepSimpleJordanHolderHom
    (x : FDRepKZero k G) :
    simpleClassInclusion k[G] (fdRepSimpleJordanHolderHom x) =
      fdRepJordanHolderKZeroHom x := by
  refine QuotientAddGroup.induction_on x ?_
  intro x
  refine FreeAbelianGroup.induction_on x ?_ ?_ ?_ ?_
  · simp
  · intro X
    let V := (fromSkeleton (FDRep k G)).obj X
    rw [← toSkeleton_fromSkeleton_obj X]
    change simpleClassInclusion k[G]
        (fdRepSimpleJordanHolderHom
          (ExactGrothendieckGroup.classOf (FDRep k G) V)) =
      fdRepJordanHolderKZeroHom
        (ExactGrothendieckGroup.classOf (FDRep k G) V)
    rw [fdRepSimpleJordanHolderHom, AddMonoidHom.comp_apply,
      fdRepJordanHolderKZeroHom_classOf]
    unfold fdRepJordanHolderSum
    rw [simpleClassProjection_compositionFactorIsoSum]
    exact simpleClassInclusion_compositionFactorSimpleSum k[G]
      (chosenFDRepCompositionSeries V)
  · intro x hx
    simpa using congrArg Neg.neg hx
  · intro x y hx hy
    simpa using congrArg₂ (.+.) hx hy

end FDRep

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
