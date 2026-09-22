import Mathlib.GroupTheory.QuotientGroup.Basic
import ModularRep.Twist

/-!
# Representations descended along surjective group homomorphisms

This neutral module constructs a descent of a representation
whose kernel contains the kernel of a surjective group homomorphism.  It
contains no character correspondence, block, weight, or manuscript source.
-/

noncomputable section

namespace ModularRep.RepresentationSurjectiveDescent

universe u

variable {K A B V : Type u}
variable [Field K] [Group A] [Group B]
variable [AddCommGroup V] [Module K V]

private def factorThroughKernel
    (f : A →* B) (rho : Representation K A V)
    (hkernel : f.ker ≤ rho.ker) :
    Representation K (A ⧸ f.ker) V :=
  QuotientGroup.lift f.ker rho hkernel

@[simp]
private theorem factorThroughKernel_apply_mk
    (f : A →* B) (rho : Representation K A V)
    (hkernel : f.ker ≤ rho.ker) (a : A) :
    factorThroughKernel f rho hkernel (QuotientGroup.mk' f.ker a) =
      rho a :=
  QuotientGroup.lift_mk' f.ker hkernel a

private theorem quotientKerEquivOfSurjective_symm_apply
    (f : A →* B) (hf : Function.Surjective f) (a : A) :
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a) =
      QuotientGroup.mk' f.ker a := by
  let e : A ⧸ f.ker ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  change e.symm (f a) = QuotientGroup.mk' f.ker a
  apply e.injective
  rw [e.apply_symm_apply]
  change f a = QuotientGroup.kerLift f (QuotientGroup.mk' f.ker a)
  exact (QuotientGroup.kerLift_mk f a).symm

/-- Descend a representation along a surjective group homomorphism once its
kernel contains the kernel of that homomorphism. -/
noncomputable def descend
    (f : A →* B) (hf : Function.Surjective f)
    (rho : Representation K A V) (hkernel : f.ker ≤ rho.ker) :
    Representation K B V :=
  (factorThroughKernel f rho hkernel).pullback
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom

@[simp]
theorem descend_apply
    (f : A →* B) (hf : Function.Surjective f)
    (rho : Representation K A V) (hkernel : f.ker ≤ rho.ker)
    (a : A) :
    descend f hf rho hkernel (f a) = rho a := by
  change
    factorThroughKernel f rho hkernel
        ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a)) =
      rho a
  rw [quotientKerEquivOfSurjective_symm_apply,
    factorThroughKernel_apply_mk]

@[simp]
theorem descend_pullback
    (f : A →* B) (hf : Function.Surjective f)
    (rho : Representation K A V) (hkernel : f.ker ≤ rho.ker) :
    (descend f hf rho hkernel).pullback f = rho := by
  ext a v
  change descend f hf rho hkernel (f a) v = rho a v
  rw [descend_apply]

/-- Descent along a surjection preserves irreducibility. -/
theorem descend_irreducible
    (f : A →* B) (hf : Function.Surjective f)
    (rho : Representation K A V) (hkernel : f.ker ≤ rho.ker)
    (hirreducible : Representation.IsIrreducible rho) :
    Representation.IsIrreducible (descend f hf rho hkernel) := by
  apply (Representation.isIrreducible_pullback_iff
    (descend f hf rho hkernel) f hf).mp
  rw [descend_pullback]
  exact hirreducible

end ModularRep.RepresentationSurjectiveDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
