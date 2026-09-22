import ModularRep.StableLatticeKZero

/-!
# A character-theoretic construction of the exact decomposition map

Suppose ordinary and modular exact Grothendieck groups map to one additive
character group, the modular character map is injective, and stable-lattice
reduction preserves the relevant character.  These hypotheses imply
lattice independence and construct the exact decomposition map.

This file proves that deduction abstractly.  The stable-reduction character
identity remains an explicit field of `ExactCharacterBridge`; it is not a
project axiom.
-/

open CategoryTheory

namespace ModularRep

open ExactGrothendieckGroup

universe u v w

variable {p : ℕ} {K O k : Type u} {G : Type v}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [Group G] [Finite G]

/-- Character-theoretic data sufficient to derive stable-lattice
independence and the exact decomposition map.

In the intended application the target is the additive group of
characteristic-zero class functions on the `p`-regular elements. -/
structure ExactCharacterBridge
    (Msys : ModularSystem p K O k) (A : Type w) [AddCommGroup A] where
  ordinaryCharacterHom : FDRepKZero K G →+ A
  modularCharacterHom : FDRepKZero k G →+ A
  modularCharacterHom_injective : Function.Injective modularCharacterHom
  stableReduction_compatible :
    ∀ {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
      [IsScalarTower O K V] [Module.Finite K V]
      (rho : Representation K G V) (L : StableLattice O K rho),
      letI := Msys.residueAlgebra
      modularCharacterHom
          (classOf (FDRep k G) (FDRep.of (L.reduction k))) =
        ordinaryCharacterHom (classOf (FDRep K G) (FDRep.of rho))

namespace ExactCharacterBridge

variable {A : Type w} [AddCommGroup A]

/-- Character compatibility for the stable lattice chosen from a finite
basis and its orbit span. -/
theorem chosenReductionClass_compatible
    (Msys : ModularSystem p K O k)
    (B : ExactCharacterBridge (G := G) Msys A) (V : FDRep K G) :
    B.modularCharacterHom (chosenReductionClass Msys V) =
      B.ordinaryCharacterHom (classOf (FDRep K G) V) := by
  let _ : Module O V := Module.restrictScalars O K V
  let _ : IsScalarTower O K V := IsScalarTower.restrictScalars O K V
  let _ := Msys.residueAlgebra
  calc
    B.modularCharacterHom (chosenReductionClass Msys V) =
        B.ordinaryCharacterHom
          (classOf (FDRep K G) (FDRep.of V.ρ)) := by
      exact B.stableReduction_compatible V.ρ (chosenStableLattice O V)
    _ = B.ordinaryCharacterHom (classOf (FDRep K G) V) := by
      rw [classOf_iso (FDRep K G) (fdRepOfRhoIso V)]

/-- The exact decomposition-map data obtained by reducing a chosen stable
lattice.  Additivity follows from ordinary-character additivity and
injectivity of the modular character map. -/
noncomputable def toExactDecompositionMapData
    (Msys : ModularSystem p K O k)
    (B : ExactCharacterBridge (G := G) Msys A) :
    ExactDecompositionMapData K k G where
  reductionClass X :=
    chosenReductionClass Msys ((fromSkeleton (FDRep K G)).obj X)
  map_shortExact S hS := by
    apply B.modularCharacterHom_injective
    rw [map_add]
    let W₁ := (fromSkeleton (FDRep K G)).obj (toSkeleton S.X₁)
    let W₂ := (fromSkeleton (FDRep K G)).obj (toSkeleton S.X₂)
    let W₃ := (fromSkeleton (FDRep K G)).obj (toSkeleton S.X₃)
    change B.modularCharacterHom (chosenReductionClass Msys W₂) =
      B.modularCharacterHom (chosenReductionClass Msys W₁) +
        B.modularCharacterHom (chosenReductionClass Msys W₃)
    rw [B.chosenReductionClass_compatible Msys W₁,
      B.chosenReductionClass_compatible Msys W₂,
      B.chosenReductionClass_compatible Msys W₃,
      classOf_iso (FDRep K G) (fromSkeletonToSkeletonIso S.X₁),
      classOf_iso (FDRep K G) (fromSkeletonToSkeletonIso S.X₂),
      classOf_iso (FDRep K G) (fromSkeletonToSkeletonIso S.X₃),
      ← map_add, classOf_middle_eq (FDRep K G) S hS]

/-- The exact decomposition homomorphism obtained from the character
bridge. -/
noncomputable def decompositionMap
    (Msys : ModularSystem p K O k)
    (B : ExactCharacterBridge (G := G) Msys A) :
    FDRepKZero K G →+ FDRepKZero k G :=
  (B.toExactDecompositionMapData Msys).toAddMonoidHom

/-- The decomposition homomorphism makes the ordinary and modular
character maps commute. -/
theorem decompositionMap_characterSquare
    (Msys : ModularSystem p K O k)
    (B : ExactCharacterBridge (G := G) Msys A) :
    B.modularCharacterHom.comp (B.decompositionMap Msys) =
      B.ordinaryCharacterHom := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [AddMonoidHom.comp_apply, decompositionMap,
    ExactDecompositionMapData.toAddMonoidHom_classOf]
  change B.modularCharacterHom
      (chosenReductionClass Msys
        ((fromSkeleton (FDRep K G)).obj (toSkeleton V))) =
    B.ordinaryCharacterHom (classOf (FDRep K G) V)
  rw [B.chosenReductionClass_compatible Msys,
    classOf_iso (FDRep K G) (fromSkeletonToSkeletonIso V)]

/-- The decomposition homomorphism is the unique additive map making the
character square commute. -/
theorem existsUnique_decompositionMap
    (Msys : ModularSystem p K O k)
    (B : ExactCharacterBridge (G := G) Msys A) :
    ∃! d : FDRepKZero K G →+ FDRepKZero k G,
      B.modularCharacterHom.comp d = B.ordinaryCharacterHom := by
  refine ⟨B.decompositionMap Msys,
    B.decompositionMap_characterSquare Msys, ?_⟩
  intro d hd
  apply AddMonoidHom.ext
  intro x
  apply B.modularCharacterHom_injective
  have hdx := DFunLike.congr_fun hd x
  have hBx := DFunLike.congr_fun
    (B.decompositionMap_characterSquare Msys) x
  exact hdx.trans hBx.symm

/-- The character-theoretically constructed data represents the reduction
of every stable lattice. -/
theorem toExactDecompositionMapData_realises
    (Msys : ModularSystem p K O k)
    (B : ExactCharacterBridge (G := G) Msys A) :
    RealisesStableLatticeReduction Msys
      (B.toExactDecompositionMapData Msys) := by
  intro V _ _ _ _ _ rho L
  let _ := Msys.residueAlgebra
  let W : FDRep K G :=
    (fromSkeleton (FDRep K G)).obj (toSkeleton (FDRep.of rho))
  apply B.modularCharacterHom_injective
  change B.modularCharacterHom (chosenReductionClass Msys W) =
    B.modularCharacterHom
      (classOf (FDRep k G) (FDRep.of (L.reduction k)))
  calc
    B.modularCharacterHom (chosenReductionClass Msys W) =
        B.ordinaryCharacterHom (classOf (FDRep K G) W) :=
      B.chosenReductionClass_compatible Msys W
    _ = B.ordinaryCharacterHom
        (classOf (FDRep K G) (FDRep.of rho)) := by
      rw [classOf_iso (FDRep K G)
        (fromSkeletonToSkeletonIso (FDRep.of rho))]
    _ = B.modularCharacterHom
        (classOf (FDRep k G) (FDRep.of (L.reduction k))) :=
      (B.stableReduction_compatible rho L).symm

/-- The resulting homomorphism sends every ordinary representation class
to the exact modular `K₀` class of every stable-lattice reduction. -/
theorem decompositionMap_classOf_eq_reduction
    (Msys : ModularSystem p K O k)
    (B : ExactCharacterBridge (G := G) Msys A)
    {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    B.decompositionMap Msys
        (classOf (FDRep K G) (FDRep.of rho)) =
      classOf (FDRep k G) (FDRep.of (L.reduction k)) :=
  ExactDecompositionMapData.map_classOf_eq_reduction Msys
    (B.toExactDecompositionMapData Msys)
    (B.toExactDecompositionMapData_realises Msys) rho L

/-- Stable-lattice reductions of the same ordinary representation have the
same exact modular `K₀` class. -/
theorem reductionClass_eq
    (Msys : ModularSystem p K O k)
    (B : ExactCharacterBridge (G := G) Msys A)
    {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L₁ L₂ : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    classOf (FDRep k G) (FDRep.of (L₁.reduction k)) =
      classOf (FDRep k G) (FDRep.of (L₂.reduction k)) :=
  ExactDecompositionMapData.reductionClass_eq Msys
    (B.toExactDecompositionMapData Msys)
    (B.toExactDecompositionMapData_realises Msys) rho L₁ L₂

end ExactCharacterBridge

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
