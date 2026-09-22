import ModularRep.BrauerCharacterExact
import ModularRep.BrauerCharacterLinearIndependence
import ModularRep.ExactGrothendieckGroup
import ModularRep.FDRepSimpleClassKZero
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Brauer characters on the exact Grothendieck group

Brauer-character formation is additive on short exact sequences, so it
descends to the exact Grothendieck group of finite dimensional modular
representations.  The simple-module coordinates for this Grothendieck group,
together with linear independence of irreducible Brauer characters, show that
the resulting homomorphism is injective.

The construction is relative to an explicit `PrimeRegularRootEmbedding`.  It
does not assert that such an embedding has been constructed from a modular
system.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.FDRepSimpleClassKZero

universe u v

variable {p : ℕ} {k G : Type u} {K : Type v}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

open ExactGrothendieckGroup

/-- Brauer character of the representation selected by a skeletal object. -/
private noncomputable def skeletonBrauerCharacter
    (iota : PrimeRegularRootEmbedding p k K G)
    (X : Skeleton (FDRep k G)) :
    PrimeRegularClassFunction K G p :=
  Representation.brauerCharacterOfRootEmbedding
    ((fromSkeleton (FDRep k G)).obj X).ρ iota

/-- The skeletal Brauer-character function respects every short exact
relation in `FDRep`. -/
private theorem skeletonBrauerCharacter_shortExact
    (iota : PrimeRegularRootEmbedding p k K G)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    skeletonBrauerCharacter iota (toSkeleton S.X₂) =
      skeletonBrauerCharacter iota (toSkeleton S.X₁) +
        skeletonBrauerCharacter iota (toSkeleton S.X₃) := by
  calc
    skeletonBrauerCharacter iota (toSkeleton S.X₂) =
        Representation.brauerCharacterOfRootEmbedding S.X₂.ρ iota :=
      Representation.brauerCharacterOfRootEmbedding_iso iota
        (fromSkeletonToSkeletonIso S.X₂)
    _ = Representation.brauerCharacterOfRootEmbedding S.X₁.ρ iota +
          Representation.brauerCharacterOfRootEmbedding S.X₃.ρ iota :=
      FDRep.brauerCharacterOfRootEmbedding_shortExact iota S hS
    _ = skeletonBrauerCharacter iota (toSkeleton S.X₁) +
          skeletonBrauerCharacter iota (toSkeleton S.X₃) := by
      dsimp only [skeletonBrauerCharacter]
      exact congrArg₂ (· + ·)
        (Representation.brauerCharacterOfRootEmbedding_iso iota
          (fromSkeletonToSkeletonIso S.X₁)).symm
        (Representation.brauerCharacterOfRootEmbedding_iso iota
          (fromSkeletonToSkeletonIso S.X₃)).symm

/-- The additive homomorphism from exact `K₀` induced by Brauer
characters. -/
noncomputable def brauerCharacterKZeroHom
    (iota : PrimeRegularRootEmbedding p k K G) :
    FDRepKZero k G →+ PrimeRegularClassFunction K G p :=
  ExactGrothendieckGroup.lift (FDRep k G)
    (skeletonBrauerCharacter iota)
    (skeletonBrauerCharacter_shortExact iota)

/-- The exact-`K₀` Brauer-character homomorphism sends an object class to
the Brauer character afforded by that object. -/
@[simp]
theorem brauerCharacterKZeroHom_classOf
    (iota : PrimeRegularRootEmbedding p k K G) (V : FDRep k G) :
    brauerCharacterKZeroHom iota
        (ExactGrothendieckGroup.classOf (FDRep k G) V) =
      Representation.brauerCharacterOfRootEmbedding V.ρ iota := by
  rw [brauerCharacterKZeroHom,
    ExactGrothendieckGroup.lift_classOf]
  exact Representation.brauerCharacterOfRootEmbedding_iso iota
    (fromSkeletonToSkeletonIso V)

/-- Forget conjugation invariance and retain the underlying function on
prime regular elements. -/
private def classFunctionToFunctionAddHom :
    PrimeRegularClassFunction K G p →+
      PrimeRegularFunction K G p where
  toFun := PrimeRegularClassFunction.toFun
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- The function-valued version of the exact-`K₀` Brauer-character
homomorphism. -/
private noncomputable def brauerFunctionKZeroHom
    (iota : PrimeRegularRootEmbedding p k K G) :
    FDRepKZero k G →+ PrimeRegularFunction K G p :=
  classFunctionToFunctionAddHom.comp (brauerCharacterKZeroHom iota)

/-- A linearly independent family over a characteristic-zero field gives an
injective homomorphism from the free abelian group on its indices. -/
private theorem freeAbelianGroup_lift_injective_of_linearIndependent
    {I M : Type*} [AddCommGroup M] [Module K M]
    (f : I → M) (hf : LinearIndependent K f) :
    Function.Injective (FreeAbelianGroup.lift f) := by
  have hfZ : LinearIndependent ℤ f := hf.restrict_scalars' ℤ
  intro x y hxy
  apply (FreeAbelianGroup.equivFinsupp I).injective
  apply hfZ.finsuppLinearCombination_injective
  let L : FreeAbelianGroup I →+ M :=
    (Finsupp.linearCombination ℤ f).toAddMonoidHom.comp
      (FreeAbelianGroup.equivFinsupp I).toAddMonoidHom
  have hL : L = FreeAbelianGroup.lift f := by
    apply FreeAbelianGroup.lift_ext
    intro i
    simp [L]
  change L x = L y
  rw [hL]
  exact hxy

/-- The free abelian group on simple module classes maps to the family of
their function-valued Brauer characters. -/
private noncomputable def simpleBrauerFunctionHom
    (iota : PrimeRegularRootEmbedding p k K G) :
    SimpleModuleClassGroup k[G] →+ PrimeRegularFunction K G p :=
  FreeAbelianGroup.lift (simpleClassBrauerFamily iota)

/-- The simple-class Brauer-character homomorphism is injective. -/
private theorem simpleBrauerFunctionHom_injective
    (iota : PrimeRegularRootEmbedding p k K G) :
    Function.Injective (simpleBrauerFunctionHom iota) :=
  freeAbelianGroup_lift_injective_of_linearIndependent
    (simpleClassBrauerFamily iota)
    (irreducibleBrauerCharacterLinearIndependence_of_rootEmbedding iota)

/-- On simple-class coordinates, the exact-`K₀` construction is precisely
the free additive extension of the irreducible Brauer characters. -/
private theorem brauerFunctionKZeroHom_simpleClassToFDRepKZero
    (iota : PrimeRegularRootEmbedding p k K G)
    (x : SimpleModuleClassGroup k[G]) :
    brauerFunctionKZeroHom iota (simpleClassToFDRepKZero x) =
      simpleBrauerFunctionHom iota x := by
  apply DFunLike.congr_fun
    (FreeAbelianGroup.lift_ext
      ((brauerFunctionKZeroHom iota).comp simpleClassToFDRepKZero)
      (simpleBrauerFunctionHom iota) (fun X ↦ ?_))
  simp only [AddMonoidHom.comp_apply, simpleClassToFDRepKZero,
    simpleBrauerFunctionHom, FreeAbelianGroup.lift_apply_of]
  rw [simpleClassToFDRepKZeroGenerator,
    brauerFunctionKZeroHom, AddMonoidHom.comp_apply,
    brauerCharacterKZeroHom_classOf]
  rfl

/-- Brauer characters distinguish all elements of the exact Grothendieck
group of finite dimensional modular representations. -/
theorem brauerCharacterKZeroHom_injective
    (iota : PrimeRegularRootEmbedding p k K G) :
    Function.Injective (brauerCharacterKZeroHom iota) := by
  intro x y hxy
  let e := fdRepKZeroEquivSimpleModuleClassGroup (k := k) (G := G)
  apply e.injective
  apply simpleBrauerFunctionHom_injective iota
  rw [← brauerFunctionKZeroHom_simpleClassToFDRepKZero iota,
    ← brauerFunctionKZeroHom_simpleClassToFDRepKZero iota]
  rw [show simpleClassToFDRepKZero (e x) = x from e.symm_apply_apply x,
    show simpleClassToFDRepKZero (e y) = y from e.symm_apply_apply y]
  exact congrArg PrimeRegularClassFunction.toFun hxy

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
