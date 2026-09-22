import ModularRep.StabilizerFactorizationTransport
import Formalisation.EquivariantActions

/-!
# One-way modular packet transport of the Levi stabilizer

An injective map on the actual Levi packet, equivariant for the Levi and
field actors, transfers the preceding Levi factorization to its ambient
character image. The field stabilizers are equal for that same image.
The codomain may be the full ambient Brauer set of characters; neither
surjectivity nor a field action on a prescribed Levi orbit is required.

This is supporting action theory. The consumer must bind the map to the
same modular Jordan packet and its literal actions. This module by itself
does not assert the manuscript's ambient diagonal enlargement.
-/

set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeJordanPacketTransport

open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {H E X Y : Type*} [Group H] [Group E]
variable [MulAction H X] [MulAction E X]
variable [MulAction H Y] [MulAction E Y]

/-- Only reflection of equality is needed to transfer the product condition
from a packet to its character image. -/
theorem product_factorization_of_injective_equivariant
    (f : X → Y) (injective : Function.Injective f)
    (equivariantH : ∀ (h : H) (x : X), f (h • x) = h • f x)
    (equivariantE : ∀ (e : E) (x : X), f (e • x) = e • f x)
    (x : X)
    (levi_factorization : ProductStabilizerFactorization (D := H) (E := E) x) :
    ProductStabilizerFactorization (D := H) (E := E) (f x) := by
  intro h e
  constructor
  · intro combined
    have preimage : h • (e • x) = x := by
      apply injective
      calc
        f (h • (e • x)) = h • f (e • x) := equivariantH h (e • x)
        _ = h • (e • f x) := congrArg (fun y : Y => h • y) (equivariantE e x)
        _ = f x := combined
    obtain ⟨fixedH, fixedE⟩ := (levi_factorization h e).mp preimage
    exact ⟨(Formalisation.fixed_iff_of_injective_equivariant
      injective equivariantH h x).mp fixedH,
      (Formalisation.fixed_iff_of_injective_equivariant
        injective equivariantE e x).mp fixedE⟩
  · rintro ⟨fixedH, fixedE⟩
    rw [fixedE, fixedH]

/-- The same one-way packet injection preserves the full field fixer. -/
theorem field_stabilizer_eq
    (f : X → Y) (injective : Function.Injective f)
    (equivariantE : ∀ (e : E) (x : X), f (e • x) = e • f x)
    (x : X) :
    MulAction.stabilizer E (f x) = MulAction.stabilizer E x :=
  (Formalisation.stabilizer_eq_of_injective_equivariant
    injective equivariantE x).symm

/-- The packet image retains both the actual compatible semidirect
factorization and the field stabilizer of the same original character. -/
theorem semidirect_packet_transport
    (field : E →* MulAut H)
    (compatibleX : Formalisation.SemidirectActionCompatible (X := X) field)
    (compatibleY : Formalisation.SemidirectActionCompatible (X := Y) field)
    (f : X → Y) (injective : Function.Injective f)
    (equivariantH : ∀ (h : H) (x : X), f (h • x) = h • f x)
    (equivariantE : ∀ (e : E) (x : X), f (e • x) = e • f x)
    (x : X)
    (levi_factorization :
      Formalisation.SemidirectStabilizerFactors field compatibleX x) :
    Formalisation.SemidirectStabilizerFactors field compatibleY (f x) ∧
      MulAction.stabilizer E (f x) = MulAction.stabilizer E x := by
  constructor
  · apply (semidirectStabilizerFactors_iff_productStabilizerFactorization
      field compatibleY (f x)).mpr
    exact product_factorization_of_injective_equivariant
      f injective equivariantH equivariantE x
      ((semidirectStabilizerFactors_iff_productStabilizerFactorization
        field compatibleX x).mp levi_factorization)
  · exact field_stabilizer_eq f injective equivariantE x

end ModularRep.PaperProofs.TypeBRankThreeJordanPacketTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
