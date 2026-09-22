import ModularRep.ReductionModulo
import Mathlib.RepresentationTheory.Equiv

/-!
# Equivariance of reduction modulo the maximal ideal

The quotient action in this file is descended directly from the integral
representation.  The tensor/quotient comparison from `ReductionModulo` is
then proved to intertwine that natural action with scalar extension.  The
quotient action is not defined by transport across the desired equivalence.
-/

open scoped TensorProduct

namespace ModularRep.ReductionModulo

universe uO uk uM uG

section AlgebraMap

variable {O : Type uO} {k : Type uk} {M : Type uM} {G : Type uG}
variable [CommRing O] [CommSemiring k] [Algebra O k]
variable [AddCommGroup M] [Module O M] [Group G]

/-- The kernel multiple submodule is stable under every endomorphism in an
`O`-linear representation. -/
theorem kernelSMul_le_comap (rho : Representation O G M) (g : G) :
    kernelSMul (O := O) (k := k) (M := M) ≤
      (kernelSMul (O := O) (k := k) (M := M)).comap (rho g) := by
  refine Submodule.smul_le.mpr ?_
  intro r hr x hx
  change rho g (r • x) ∈ kernelSMul (O := O) (k := k) (M := M)
  rw [map_smul]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- The natural action on `M / ker(O → k) M`, obtained by descending the
integral action and then making the descended maps `k`-linear. -/
noncomputable def quotientRepresentation
    (rho : Representation O G M)
    (hf : Function.Surjective (algebraMap O k)) :
    letI := quotientModule (M := M) hf
    Representation k G
      (M ⧸ kernelSMul (O := O) (k := k) (M := M)) := by
  let _ := quotientModule (M := M) hf
  let _ := quotientIsScalarTower (M := M) hf
  let rhoO := rho.quotient
    (kernelSMul (O := O) (k := k) (M := M))
    (kernelSMul_le_comap (k := k) rho)
  exact
    { toFun := fun g ↦ (rhoO g).extendScalarsOfSurjective hf
      map_one' := by
        ext x
        change rhoO 1 x = x
        simp
      map_mul' := by
        intro g h
        ext x
        change rhoO (g * h) x = rhoO g (rhoO h x)
        simp [← Module.End.mul_apply] }

@[simp]
theorem quotientRepresentation_apply_mk
    (rho : Representation O G M)
    (hf : Function.Surjective (algebraMap O k))
    (g : G) (x : M) :
    letI := quotientModule (M := M) hf
    quotientRepresentation rho hf g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (rho g x) := by
  let _ := quotientModule (M := M) hf
  let _ := quotientIsScalarTower (M := M) hf
  rfl

/-- The tensor/quotient comparison intertwines base change of the integral
action with its naturally descended quotient action. -/
theorem tensorQuotientEquiv_isIntertwining
    (rho : Representation O G M)
    (hf : Function.Surjective (algebraMap O k)) (g : G) :
    letI := quotientModule (M := M) hf
    (tensorQuotientEquiv (M := M) hf).toLinearMap.comp
        (rho.baseChange k g) =
      (quotientRepresentation rho hf g).comp
        (tensorQuotientEquiv (M := M) hf).toLinearMap := by
  let _ := quotientModule (M := M) hf
  let _ := quotientIsScalarTower (M := M) hf
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add x y hx hy =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy

/-- The tensor/quotient linear equivalence, bundled as an equivalence of
representations for the natural quotient action. -/
noncomputable def tensorQuotientRepresentationEquiv
    (rho : Representation O G M)
    (hf : Function.Surjective (algebraMap O k)) :
    letI := quotientModule (M := M) hf
    (rho.baseChange k).Equiv (quotientRepresentation rho hf) := by
  letI := quotientModule (M := M) hf
  exact Representation.Equiv.mk
    (tensorQuotientEquiv (M := M) hf)
    (tensorQuotientEquiv_isIntertwining rho hf)

end AlgebraMap

section RingHom

variable {O : Type uO} {k : Type uk} {M : Type uM} {G : Type uG}
variable [CommRing O] [CommSemiring k]
variable [AddCommGroup M] [Module O M] [Group G]

/-- Ring-homomorphism form of the natural quotient representation, with its
kernel identified with a named ideal. -/
noncomputable def quotientRepresentationOfKernelEq
    (rho : Representation O G M)
    (f : O →+* k) (hf : Function.Surjective f)
    (m : Ideal O) (hm : RingHom.ker f = m) :
    letI := f.toAlgebra
    letI := quotientModuleOfKernelEq (M := M) f hf m hm
    Representation k G (M ⧸ m • (⊤ : Submodule O M)) := by
  subst m
  let _ := f.toAlgebra
  let _ := quotientModuleOfKernelEq
    (M := M) f hf (RingHom.ker f) rfl
  exact quotientRepresentation rho hf

@[simp]
theorem quotientRepresentationOfKernelEq_apply_mk
    (rho : Representation O G M)
    (f : O →+* k) (hf : Function.Surjective f)
    (m : Ideal O) (hm : RingHom.ker f = m)
    (g : G) (x : M) :
    letI := f.toAlgebra
    letI := quotientModuleOfKernelEq (M := M) f hf m hm
    quotientRepresentationOfKernelEq rho f hf m hm g
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (rho g x) := by
  subst m
  let _ := f.toAlgebra
  let _ := quotientModuleOfKernelEq
    (M := M) f hf (RingHom.ker f) rfl
  exact quotientRepresentation_apply_mk rho hf g x

/-- The named-kernel tensor/quotient equivalence is intertwining for the
natural quotient action. -/
theorem tensorQuotientEquivOfKernelEq_isIntertwining
    (rho : Representation O G M)
    (f : O →+* k) (hf : Function.Surjective f)
    (m : Ideal O) (hm : RingHom.ker f = m) (g : G) :
    letI := f.toAlgebra
    letI := quotientModuleOfKernelEq (M := M) f hf m hm
    (tensorQuotientEquivOfKernelEq (M := M) f hf m hm).toLinearMap.comp
        (rho.baseChange k g) =
      (quotientRepresentationOfKernelEq rho f hf m hm g).comp
        (tensorQuotientEquivOfKernelEq
          (M := M) f hf m hm).toLinearMap := by
  subst m
  let _ := f.toAlgebra
  let _ := quotientModuleOfKernelEq
    (M := M) f hf (RingHom.ker f) rfl
  exact tensorQuotientEquiv_isIntertwining rho hf g

/-- The named-kernel tensor/quotient equivalence, bundled as a
representation equivalence. -/
noncomputable def tensorQuotientRepresentationEquivOfKernelEq
    (rho : Representation O G M)
    (f : O →+* k) (hf : Function.Surjective f)
    (m : Ideal O) (hm : RingHom.ker f = m) :
    letI := f.toAlgebra
    letI := quotientModuleOfKernelEq (M := M) f hf m hm
    (rho.baseChange k).Equiv
      (quotientRepresentationOfKernelEq rho f hf m hm) := by
  letI := f.toAlgebra
  letI := quotientModuleOfKernelEq (M := M) f hf m hm
  exact Representation.Equiv.mk
    (tensorQuotientEquivOfKernelEq (M := M) f hf m hm)
    (tensorQuotientEquivOfKernelEq_isIntertwining rho f hf m hm)

end RingHom

section ModularSystem

universe uK uV

variable {p : ℕ} {K : Type uK} {O : Type uO} {k : Type uk}
variable {G : Type uG} {V : Type uV}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [Group G] [AddCommGroup V] [Module O V] [Module K V]
variable [IsScalarTower O K V]
variable {rho : Representation K G V}

/-- The natural modular representation on `L / mL`, descended directly from
the integral representation carried by `L`. -/
noncomputable def stableLatticeQuotientRepresentation
    (Msys : ModularSystem p K O k) (L : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    letI := quotientModuleOfKernelEq
      (M := L.toSubrepresentation.toSubmodule)
      Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
    Representation k G
      (L.toSubrepresentation.toSubmodule ⧸
        Msys.maximalIdeal •
          (⊤ : Submodule O L.toSubrepresentation.toSubmodule)) := by
  let _ := Msys.residueAlgebra
  let _ := quotientModuleOfKernelEq
    (M := L.toSubrepresentation.toSubmodule)
    Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
  exact quotientRepresentationOfKernelEq
    L.integralRepresentation Msys.residue Msys.residue_surjective
    Msys.maximalIdeal Msys.ker_residue

@[simp]
theorem stableLatticeQuotientRepresentation_apply_mk
    (Msys : ModularSystem p K O k) (L : StableLattice O K rho)
    (g : G) (x : L.toSubrepresentation.toSubmodule) :
    letI := Msys.residueAlgebra
    letI := quotientModuleOfKernelEq
      (M := L.toSubrepresentation.toSubmodule)
      Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
    stableLatticeQuotientRepresentation Msys L g
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (L.integralRepresentation g x) := by
  let _ := Msys.residueAlgebra
  let _ := quotientModuleOfKernelEq
    (M := L.toSubrepresentation.toSubmodule)
    Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
  exact quotientRepresentationOfKernelEq_apply_mk
    L.integralRepresentation Msys.residue Msys.residue_surjective
    Msys.maximalIdeal Msys.ker_residue g x

/-- The stable-lattice tensor/quotient map commutes with the `G`-actions. -/
theorem stableLatticeReductionCarrierQuotientEquiv_isIntertwining
    (Msys : ModularSystem p K O k) (L : StableLattice O K rho) (g : G) :
    letI := Msys.residueAlgebra
    letI := quotientModuleOfKernelEq
      (M := L.toSubrepresentation.toSubmodule)
      Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
    (stableLatticeReductionCarrierQuotientEquiv Msys L).toLinearMap.comp
        (L.reduction k g) =
      (stableLatticeQuotientRepresentation Msys L g).comp
        (stableLatticeReductionCarrierQuotientEquiv Msys L).toLinearMap := by
  let _ := Msys.residueAlgebra
  let _ := quotientModuleOfKernelEq
    (M := L.toSubrepresentation.toSubmodule)
    Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
  exact tensorQuotientEquivOfKernelEq_isIntertwining
    L.integralRepresentation Msys.residue Msys.residue_surjective
    Msys.maximalIdeal Msys.ker_residue g

/-- The stable-lattice carrier equivalence is an equivalence of the
base-changed representation and the natural quotient representation. -/
noncomputable def stableLatticeReductionQuotientEquiv
    (Msys : ModularSystem p K O k) (L : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    letI := quotientModuleOfKernelEq
      (M := L.toSubrepresentation.toSubmodule)
      Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
    (L.reduction k).Equiv (stableLatticeQuotientRepresentation Msys L) := by
  letI := Msys.residueAlgebra
  letI := quotientModuleOfKernelEq
    (M := L.toSubrepresentation.toSubmodule)
    Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
  exact Representation.Equiv.mk
    (stableLatticeReductionCarrierQuotientEquiv Msys L)
    (stableLatticeReductionCarrierQuotientEquiv_isIntertwining Msys L)

@[simp]
theorem stableLatticeReductionQuotientEquiv_toLinearEquiv
    (Msys : ModularSystem p K O k) (L : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    letI := quotientModuleOfKernelEq
      (M := L.toSubrepresentation.toSubmodule)
      Msys.residue Msys.residue_surjective Msys.maximalIdeal Msys.ker_residue
    (stableLatticeReductionQuotientEquiv Msys L).toLinearEquiv =
      stableLatticeReductionCarrierQuotientEquiv Msys L := by
  rfl

end ModularSystem

end ModularRep.ReductionModulo


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
