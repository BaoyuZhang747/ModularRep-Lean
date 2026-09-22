import ModularRep.JordanHolderCoordinates
import ModularRep.FDRepFiniteLength
import ModularRep.FDRepGroupAlgebraEquivalence
import Mathlib.RingTheory.Length

/-!
# Jordan--Hölder coordinates on the exact Grothendieck group of `FDRep`

This module transports composition factors through the arrows of a
short exact sequence, proves additivity of the formal Jordan--Hölder factor
sum, and descends that sum to the exact Grothendieck group of `FDRep`.
The target is a free abelian group of module isomorphism classes, not the
Grothendieck group of the category of all modules.
-/

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators MonoidAlgebra SetRel

namespace ModularRep.FDRepJordanHolderKZero

open JordanHolderCoordinates ExactGrothendieckGroup

universe u

variable {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- An injection identifies a subquotient with the corresponding image subquotient. -/
noncomputable def quotientMapEquivOfInjective
    {N : Type u} [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (hf : Function.Injective f)
    (A B : Submodule R N) (hAB : A ≤ B) :
    (B ⧸ A.comap B.subtype) ≃ₗ[R]
      ((B.map f) ⧸ (A.map f).comap (B.map f).subtype) := by
  let e : B ≃ₗ[R] B.map f := Submodule.equivMapOfInjective f hf B
  apply Submodule.Quotient.equiv _ _ e
  ext y
  constructor
  · intro hy
    rcases Submodule.mem_map.mp hy with ⟨x, hx, hxy⟩
    change (y : M) ∈ A.map f
    rw [← hxy]
    exact Submodule.mem_map_of_mem (show (x : N) ∈ A from hx)
  · intro hy
    change (y : M) ∈ A.map f at hy
    rcases Submodule.mem_map.mp hy with ⟨a, ha, hay⟩
    let x : B := ⟨a, hAB ha⟩
    apply Submodule.mem_map.mpr
    refine ⟨x, ?_, ?_⟩
    · exact ha
    · apply Subtype.ext
      exact hay

/-- Map every term of a composition series through an injection. -/
def mapCompositionSeries
    {N : Type u} [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (hf : Function.Injective f)
    (t : CompositionSeries (Submodule R N)) :
    CompositionSeries (Submodule R M) :=
  t.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩

/-- Corresponding factors of a series and its image under an injection are equivalent. -/
noncomputable def compositionFactorMapEquivOfInjective
    {N : Type u} [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (hf : Function.Injective f)
    (t : CompositionSeries (Submodule R N)) (i : Fin t.length) :
    compositionFactor t i ≃ₗ[R]
      compositionFactor (mapCompositionSeries f hf t) i :=
  quotientMapEquivOfInjective f hf
    (t (Fin.castSucc i)) (t (Fin.succ i)) (t.step i).le

/-- Mapping a series through an injection preserves its formal factor sum. -/
theorem compositionFactorIsoSum_map_injective
    {N : Type u} [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (hf : Function.Injective f)
    (t : CompositionSeries (Submodule R N)) :
    compositionFactorIsoSum (mapCompositionSeries f hf t) =
      compositionFactorIsoSum t := by
  classical
  unfold compositionFactorIsoSum
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg FreeAbelianGroup.of
  exact (congr_toSkeleton_of_iso
    (compositionFactorMapEquivOfInjective f hf t i).toModuleIso).symm

/-- Restrict a linear map from the inverse image of a submodule to that submodule. -/
def submoduleComapMap
    {N : Type u} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (B : Submodule R N) :
    B.comap g →ₗ[R] B :=
  (g.domRestrict (B.comap g)).codRestrict B (fun x ↦ x.2)

/-- The restricted map onto an inverse image is surjective when the original map is. -/
theorem submoduleComapMap_surjective
    {N : Type u} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (hg : Function.Surjective g) (B : Submodule R N) :
    Function.Surjective (submoduleComapMap g B) := by
  intro y
  obtain ⟨x, hx⟩ := hg y
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change g x ∈ B
    rw [hx]
    exact y.2
  · apply Subtype.ext
    exact hx

/-- The denominator of a factor is preserved by the restricted inverse-image map. -/
theorem comap_factor_denominator
    {N : Type u} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (A B : Submodule R N) :
    (A.comap B.subtype).comap (submoduleComapMap g B) =
      (A.comap g).comap (B.comap g).subtype := by
  ext x
  rfl

/-- The induced linear map between factors of inverse-image submodules. -/
def quotientComapMap
    {N : Type u} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (A B : Submodule R N) :
    ((B.comap g) ⧸ ((A.comap g).comap (B.comap g).subtype)) →ₗ[R]
      (B ⧸ (A.comap B.subtype)) :=
  ((A.comap g).comap (B.comap g).subtype).mapQ
    (A.comap B.subtype)
    (submoduleComapMap g B)
    (by rw [comap_factor_denominator])

/-- A surjection identifies inverse-image factors with the original factors. -/
noncomputable def quotientComapEquivOfSurjective
    {N : Type u} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (A B : Submodule R N) :
    ((B.comap g) ⧸ ((A.comap g).comap (B.comap g).subtype)) ≃ₗ[R]
      (B ⧸ (A.comap B.subtype)) :=
  LinearEquiv.ofBijective (quotientComapMap g A B) ⟨by
    rw [← LinearMap.ker_eq_bot]
    unfold quotientComapMap
    rw [Submodule.ker_mapQ, comap_factor_denominator]
    exact Submodule.mkQ_map_self _, by
    rw [← LinearMap.range_eq_top]
    unfold quotientComapMap
    rw [Submodule.range_mapQ,
      LinearMap.range_eq_top.mpr (submoduleComapMap_surjective g hg B)]
    rw [Submodule.map_top, Submodule.range_mkQ]⟩

/-- Take inverse images of every term of a composition series under a surjection. -/
def comapCompositionSeries
    {N : Type u} [AddCommGroup N] [Module R N]
    (s : CompositionSeries (Submodule R N))
    (g : M →ₗ[R] N) (hg : Function.Surjective g) :
    CompositionSeries (Submodule R M) :=
  s.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩

/-- Taking inverse images under a surjection preserves the formal factor sum. -/
theorem compositionFactorIsoSum_comap_surjective
    {N : Type u} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (s : CompositionSeries (Submodule R N)) :
    compositionFactorIsoSum (comapCompositionSeries s g hg) =
      compositionFactorIsoSum s := by
  classical
  unfold compositionFactorIsoSum
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg FreeAbelianGroup.of
  apply congr_toSkeleton_of_iso
  exact (quotientComapEquivOfSurjective g hg
    (s (Fin.castSucc i)) (s (Fin.succ i))).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- The formal factor sum of a smashed series is the sum for its two pieces. -/
theorem compositionFactorIsoSum_smash
    (p q : CompositionSeries (Submodule R M))
    (h : p.last = q.head) :
    compositionFactorIsoSum (p.smash q h) =
      compositionFactorIsoSum p + compositionFactorIsoSum q := by
  classical
  unfold compositionFactorIsoSum
  change
    (∑ i : Fin (p.length + q.length),
      FreeAbelianGroup.of (toSkeleton (ModuleCat.of R
        ((p.smash q h) (Fin.succ i) ⧸
          ((p.smash q h) (Fin.castSucc i)).comap
            ((p.smash q h) (Fin.succ i)).subtype)))) = _
  rw [Fin.sum_univ_add]
  congr 1
  · apply Fintype.sum_congr
    intro i
    congr 2
    rw [RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd]
  · apply Fintype.sum_congr
    intro i
    congr 2
    rw [RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd]

set_option backward.isDefEq.respectTransparency false in
/-- Jordan--Hölder factor sums are additive in a short exact sequence. -/
theorem compositionFactorIsoSum_eq_add_of_exact
    {N P : Type u}
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (H : Function.Exact f g)
    (sM : CompositionSeries (Submodule R M))
    (sN : CompositionSeries (Submodule R N))
    (sP : CompositionSeries (Submodule R P))
    (hMhead : sM.head = ⊥) (hMlast : sM.last = ⊤)
    (hNhead : sN.head = ⊥) (hNlast : sN.last = ⊤)
    (hPhead : sP.head = ⊥) (hPlast : sP.last = ⊤) :
    compositionFactorIsoSum sM =
      compositionFactorIsoSum sN + compositionFactorIsoSum sP := by
  let sN' : CompositionSeries (Submodule R M) :=
    mapCompositionSeries f hf sN
  let sP' : CompositionSeries (Submodule R M) :=
    comapCompositionSeries sP g hg
  have hconnect : sN'.last = sP'.head := by
    change Submodule.map f sN.last = Submodule.comap g sP.head
    rw [hNlast, hPhead, Submodule.map_top, Submodule.comap_bot,
      LinearMap.exact_iff.mp H]
  let middleSeries : CompositionSeries (Submodule R M) :=
    sN'.smash sP' hconnect
  have hMiddleHead : middleSeries.head = ⊥ := by
    simpa [middleSeries, sN', mapCompositionSeries,
      hNhead, -Submodule.map_bot] using Submodule.map_bot f
  have hMiddleLast : middleSeries.last = ⊤ := by
    simpa [middleSeries, sP', comapCompositionSeries,
      hPlast, -Submodule.comap_top] using Submodule.comap_top g
  calc
    compositionFactorIsoSum sM =
        compositionFactorIsoSum middleSeries :=
      compositionFactorIsoSum_eq sM middleSeries
        (hMhead.trans hMiddleHead.symm) (hMlast.trans hMiddleLast.symm)
    _ = compositionFactorIsoSum sN' + compositionFactorIsoSum sP' :=
      compositionFactorIsoSum_smash sN' sP' hconnect
    _ = compositionFactorIsoSum sN + compositionFactorIsoSum sP := by
      rw [show compositionFactorIsoSum sN' = compositionFactorIsoSum sN by
          exact compositionFactorIsoSum_map_injective f hf sN,
        show compositionFactorIsoSum sP' = compositionFactorIsoSum sP by
          exact compositionFactorIsoSum_comap_surjective g hg sP]

/-- Linearly equivalent finite-length modules have the same formal factor sum. -/
theorem compositionFactorIsoSum_eq_of_linearEquiv
    {N : Type u} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N)
    (sM : CompositionSeries (Submodule R M))
    (sN : CompositionSeries (Submodule R N))
    (hMhead : sM.head = ⊥) (hMlast : sM.last = ⊤)
    (hNhead : sN.head = ⊥) (hNlast : sN.last = ⊤) :
    compositionFactorIsoSum sM = compositionFactorIsoSum sN := by
  let mapped : CompositionSeries (Submodule R N) :=
    mapCompositionSeries e.toLinearMap e.injective sM
  have hMappedHead : mapped.head = ⊥ := by
    simp [mapped, mapCompositionSeries, hMhead]
  have hMappedLast : mapped.last = ⊤ := by
    change Submodule.map e.toLinearMap sM.last = ⊤
    rw [hMlast, Submodule.map_top, LinearEquiv.range]
  calc
    compositionFactorIsoSum sM = compositionFactorIsoSum mapped :=
      (compositionFactorIsoSum_map_injective e.toLinearMap e.injective sM).symm
    _ = compositionFactorIsoSum sN :=
      compositionFactorIsoSum_eq mapped sN
        (hMappedHead.trans hNhead.symm) (hMappedLast.trans hNlast.symm)

section FDRepBridge

variable {k G : Type u} [Field k] [Monoid G]

/-- A chosen composition series for the group algebra module underlying a representation. -/
noncomputable def chosenFDRepCompositionSeries (V : FDRep k G) :
    CompositionSeries
      (Submodule k[G] (Representation.asModule V.ρ)) :=
  Classical.choose (FDRepFiniteLength.exists_compositionSeries V)

/-- The chosen series starts at the zero submodule. -/
theorem chosenFDRepCompositionSeries_head (V : FDRep k G) :
    (chosenFDRepCompositionSeries V).head = ⊥ :=
  (Classical.choose_spec
    (FDRepFiniteLength.exists_compositionSeries V)).1

/-- The chosen series ends at the full module. -/
theorem chosenFDRepCompositionSeries_last (V : FDRep k G) :
    (chosenFDRepCompositionSeries V).last = ⊤ :=
  (Classical.choose_spec
    (FDRepFiniteLength.exists_compositionSeries V)).2

/-- The formal sum of the simple factors of a finite-dimensional representation. -/
noncomputable def fdRepJordanHolderSum (V : FDRep k G) :
    FreeClassGroup (ModuleCat.{u} k[G]) :=
  compositionFactorIsoSum (chosenFDRepCompositionSeries V)

/-- The formal factor sum is invariant under isomorphism of representations. -/
theorem fdRepJordanHolderSum_iso {V W : FDRep k G} (e : V ≅ W) :
    fdRepJordanHolderSum V = fdRepJordanHolderSum W := by
  let eM := (FDRepFiniteLength.toModuleMonoidAlgebra (k := k) (G := G)).mapIso e
  exact compositionFactorIsoSum_eq_of_linearEquiv eM.toLinearEquiv
    (chosenFDRepCompositionSeries V) (chosenFDRepCompositionSeries W)
    (chosenFDRepCompositionSeries_head V) (chosenFDRepCompositionSeries_last V)
    (chosenFDRepCompositionSeries_head W) (chosenFDRepCompositionSeries_last W)

/-- The formal factor sum is additive on every short exact complex in `FDRep`. -/
theorem fdRepJordanHolderSum_shortExact
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    fdRepJordanHolderSum S.X₂ =
      fdRepJordanHolderSum S.X₁ + fdRepJordanHolderSum S.X₃ := by
  let F := FDRepFiniteLength.toModuleMonoidAlgebra (k := k) (G := G)
  let T := S.map F
  have hT : T.ShortExact := hS.map_of_exact F
  exact compositionFactorIsoSum_eq_add_of_exact
    T.f.hom T.g.hom hT.moduleCat_injective_f hT.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact)
    (chosenFDRepCompositionSeries S.X₂)
    (chosenFDRepCompositionSeries S.X₁)
    (chosenFDRepCompositionSeries S.X₃)
    (chosenFDRepCompositionSeries_head S.X₂)
    (chosenFDRepCompositionSeries_last S.X₂)
    (chosenFDRepCompositionSeries_head S.X₁)
    (chosenFDRepCompositionSeries_last S.X₁)
    (chosenFDRepCompositionSeries_head S.X₃)
    (chosenFDRepCompositionSeries_last S.X₃)

/-- The factor-sum function on the chosen skeleton of `FDRep`. -/
noncomputable def fdRepJordanHolderSumOnSkeleton
    (X : Skeleton (FDRep k G)) :
    FreeClassGroup (ModuleCat.{u} k[G]) :=
  fdRepJordanHolderSum ((fromSkeleton (FDRep k G)).obj X)

/-- Evaluating the skeletal factor sum on an object recovers its factor sum. -/
theorem fdRepJordanHolderSumOnSkeleton_toSkeleton (V : FDRep k G) :
    fdRepJordanHolderSumOnSkeleton (toSkeleton V) =
      fdRepJordanHolderSum V :=
  fdRepJordanHolderSum_iso (fromSkeletonToSkeletonIso V)

/-- Jordan--Hölder factor sums define a homomorphism on the exact `K₀` of `FDRep`. -/
noncomputable def fdRepJordanHolderKZeroHom :
    FDRepKZero k G →+
      FreeClassGroup (ModuleCat.{u} k[G]) :=
  ExactGrothendieckGroup.lift (FDRep k G)
    fdRepJordanHolderSumOnSkeleton
    (fun S hS ↦ by
      rw [fdRepJordanHolderSumOnSkeleton_toSkeleton,
        fdRepJordanHolderSumOnSkeleton_toSkeleton,
        fdRepJordanHolderSumOnSkeleton_toSkeleton]
      exact fdRepJordanHolderSum_shortExact S hS)

/-- The `K₀` homomorphism sends an object class to its Jordan--Hölder factor sum. -/
@[simp]
theorem fdRepJordanHolderKZeroHom_classOf (V : FDRep k G) :
    fdRepJordanHolderKZeroHom
        (ExactGrothendieckGroup.classOf (FDRep k G) V) =
      fdRepJordanHolderSum V := by
  rw [fdRepJordanHolderKZeroHom,
    ExactGrothendieckGroup.lift_classOf,
    fdRepJordanHolderSumOnSkeleton_toSkeleton]

/-- The multiplicity of one module isomorphism class in the Jordan--Hölder sum. -/
noncomputable def fdRepJordanHolderCoordinate
    (X : Skeleton (ModuleCat.{u} k[G])) :
    FDRepKZero k G →+ ℤ :=
  (FreeAbelianGroup.coeff X).comp fdRepJordanHolderKZeroHom

/-- On an object class, a coordinate is the corresponding composition-factor multiplicity. -/
@[simp]
theorem fdRepJordanHolderCoordinate_classOf
    (X : Skeleton (ModuleCat.{u} k[G])) (V : FDRep k G) :
    fdRepJordanHolderCoordinate X
        (ExactGrothendieckGroup.classOf (FDRep k G) V) =
      compositionCoefficient (chosenFDRepCompositionSeries V) X := by
  rw [fdRepJordanHolderCoordinate, AddMonoidHom.comp_apply,
    fdRepJordanHolderKZeroHom_classOf]
  rfl

end FDRepBridge

end ModularRep.FDRepJordanHolderKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
