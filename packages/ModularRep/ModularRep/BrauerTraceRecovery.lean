import ModularRep.BrauerCharacter
import ModularRep.CyclotomicRootSumReflection
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Recovery of modular traces from Brauer root sums

This file packages the roots of a characteristic polynomial at a prime regular
element as roots of unity.  Cyclotomic root-sum reflection then shows that
equality of the characteristic-zero Brauer values forces equality of the
original characteristic-`p` traces.
-/

open Polynomial

namespace ModularRep.BrauerTraceRecovery

open CyclotomicRootSumReflection

universe u v w x y

variable {k : Type u} {K : Type v} [Field k] [Field K] [CharZero K]

section CharacteristicPolynomialRoots

variable {p : ℕ} {G : Type w} {V : Type x}
variable [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The roots of the characteristic polynomial at a prime regular element,
with every occurrence packaged as a root of unity. -/
noncomputable def charpolyRootsOfUnity
    (rho : Representation k G V)
    (iota : PrimeRegularRootEmbedding p k K G)
    (g : PrimeRegularElement (G := G) p) :
    Multiset (rootsOfUnity (primeRegularExponent p G) k) :=
  (rho g.1).charpoly.roots.attach.map fun a ↦
    rho.charpolyRootAsRootOfUnity iota g a

omit [CharZero K] [CharP k p] [IsAlgClosed k] in
theorem charpolyRootsOfUnity_map_source
    (rho : Representation k G V)
    (iota : PrimeRegularRootEmbedding p k K G)
    (g : PrimeRegularElement (G := G) p) :
    (charpolyRootsOfUnity rho iota g).map
        (fun z ↦ (((z : rootsOfUnity
          (primeRegularExponent p G) k) : kˣ) : k)) =
      (rho g.1).charpoly.roots := by
  rw [charpolyRootsOfUnity, Multiset.map_map]
  calc
    (rho g.1).charpoly.roots.attach.map
        ((fun z ↦ (((z : rootsOfUnity
          (primeRegularExponent p G) k) : kˣ) : k)) ∘
          fun a ↦ rho.charpolyRootAsRootOfUnity iota g a) =
      (rho g.1).charpoly.roots.attach.map Subtype.val := by
        apply Multiset.map_congr rfl
        intro a ha
        exact rho.coe_charpolyRootAsRootOfUnity iota g a
    _ = (rho g.1).charpoly.roots :=
      Multiset.attach_map_val _

omit [CharZero K] [CharP k p] [IsAlgClosed k] in
theorem charpolyRootsOfUnity_map_image
    (rho : Representation k G V)
    (iota : PrimeRegularRootEmbedding p k K G)
    (g : PrimeRegularElement (G := G) p) :
    (charpolyRootsOfUnity rho iota g).map
        (fun z ↦ (((iota.toMulEquiv z : rootsOfUnity
          (primeRegularExponent p G) K) : Kˣ) : K)) =
      (rho g.1).charpoly.roots.map iota.lift := by
  rw [charpolyRootsOfUnity, Multiset.map_map]
  calc
    (rho g.1).charpoly.roots.attach.map
        ((fun z ↦ (((iota.toMulEquiv z : rootsOfUnity
          (primeRegularExponent p G) K) : Kˣ) : K)) ∘
          fun a ↦ rho.charpolyRootAsRootOfUnity iota g a) =
      (rho g.1).charpoly.roots.attach.map (fun a ↦ iota.lift a.1) := by
        apply Multiset.map_congr rfl
        intro a ha
        simpa [Function.comp_apply,
          PrimeRegularRootEmbedding.liftRoot] using
          (rho.lift_charpolyRootAsRootOfUnity iota g a).symm
    _ = (rho g.1).charpoly.roots.map iota.lift :=
      Multiset.attach_map_val' _ _

end CharacteristicPolynomialRoots

section BrauerRootSumsDetermineTrace

variable {p : ℕ} {G : Type w} {V : Type x} {W : Type y}
variable [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- At a prime regular element, equality of the lifted characteristic
polynomial root sums implies equality of the modular traces. -/
theorem character_apply_eq_of_brauerRootSum_eq
    (rho : Representation k G V) (sigma : Representation k G W)
    (iota : PrimeRegularRootEmbedding p k K G)
    (g : PrimeRegularElement (G := G) p)
    (h : ((rho g.1).charpoly.roots.map iota.lift).sum =
      ((sigma g.1).charpoly.roots.map iota.lift).sum) :
    Representation.character rho g.1 =
      Representation.character sigma g.1 := by
  have hcop : (primeRegularExponent p G).Coprime p := by
    exact (Nat.coprime_ordCompl iota.prime Nat.card_pos.ne').symm
  have himage :
      ((charpolyRootsOfUnity rho iota g).map
        (fun z ↦ (((iota.toMulEquiv z : rootsOfUnity
          (primeRegularExponent p G) K) : Kˣ) : K))).sum =
      ((charpolyRootsOfUnity sigma iota g).map
        (fun z ↦ (((iota.toMulEquiv z : rootsOfUnity
          (primeRegularExponent p G) K) : Kˣ) : K))).sum := by
    rw [charpolyRootsOfUnity_map_image, charpolyRootsOfUnity_map_image]
    exact h
  have hsource := multiset_sum_coe_eq_of_image_sum_eq_isAlgClosed
    iota.prime hcop iota.toMulEquiv
    (charpolyRootsOfUnity rho iota g)
    (charpolyRootsOfUnity sigma iota g) himage
  rw [charpolyRootsOfUnity_map_source,
    charpolyRootsOfUnity_map_source] at hsource
  change LinearMap.trace k V (rho g.1) =
    LinearMap.trace k W (sigma g.1)
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits
      (IsAlgClosed.splits (rho g.1).charpoly),
    Module.End.trace_eq_sum_roots_charpoly_of_splits
      (IsAlgClosed.splits (sigma g.1).charpoly)]
  exact hsource

/-- Pointwise form using the function-valued Brauer characters already
defined in the project. -/
theorem character_apply_eq_of_brauerCharacter_apply_eq
    (rho : Representation k G V) (sigma : Representation k G W)
    (iota : PrimeRegularRootEmbedding p k K G)
    (g : PrimeRegularElement (G := G) p)
    (h : rho.brauerCharacterOfRootEmbedding iota g =
      sigma.brauerCharacterOfRootEmbedding iota g) :
    Representation.character rho g.1 =
      Representation.character sigma g.1 := by
  apply character_apply_eq_of_brauerRootSum_eq rho sigma iota g
  simpa only [Representation.brauerCharacterOfRootEmbedding_apply] using h

end BrauerRootSumsDetermineTrace

end ModularRep.BrauerTraceRecovery


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
