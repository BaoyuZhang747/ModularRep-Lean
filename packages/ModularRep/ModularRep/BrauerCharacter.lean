import ModularRep.PrimeRegularClassFunction
import ModularRep.PrimeRegularEigenvalues
import ModularRep.ScalarCharpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Brauer characters from an explicit root lift

For a finite group `G` and a prime `p`, the eigenvalues of a `p`-regular
element are roots of unity whose orders divide `primeRegularExponent p G`.
A splitting modular system supplies a multiplicative correspondence between
these roots in characteristic `p` and characteristic zero.  Mathlib does not
yet construct that correspondence, so this file makes it explicit as
`PrimeRegularRootEmbedding`.

Given such an embedding, the Brauer-character value of a representation is
defined by lifting the roots of the characteristic polynomial individually
and summing them.  No project axiom is used.  The existence of the root
embedding, and its construction from a splitting modular system, remain an
external dependency.
-/

namespace ModularRep

universe u v w

/-- A chosen multiplicative correspondence between the roots of unity needed
for Brauer-character values in the two coefficient fields. -/
structure PrimeRegularRootEmbedding
    (p : ℕ) (k : Type u) (K : Type v) (G : Type w)
    [Field k] [Field K] [Group G] [Finite G] where
  /-- The coefficient prime really is prime. -/
  prime : p.Prime
  /-- The chosen correspondence on roots whose orders divide the part of
  `|G|` prime to `p`. -/
  toMulEquiv :
    rootsOfUnity (primeRegularExponent p G) k ≃*
      rootsOfUnity (primeRegularExponent p G) K

namespace PrimeRegularRootEmbedding

variable {p : ℕ} {k : Type u} {K : Type v} {G : Type w}
variable [Field k] [Field K] [Group G] [Finite G]

/-- The value in `K` of a root in the domain of a chosen root embedding. -/
noncomputable def liftRoot (iota : PrimeRegularRootEmbedding p k K G)
    (z : rootsOfUnity (primeRegularExponent p G) k) : K :=
  ((iota.toMulEquiv z : rootsOfUnity (primeRegularExponent p G) K) : Kˣ)

/-- Extend the chosen root lift to the whole source field, using zero outside
its intended domain.  Characteristic-polynomial roots at `p`-regular elements
always lie in the intended domain; see
`Representation.lift_charpolyRootAsRootOfUnity`. -/
noncomputable def lift (iota : PrimeRegularRootEmbedding p k K G) : k → K :=
  Function.extend
    (fun zeta : rootsOfUnity (primeRegularExponent p G) k ↦
      (((zeta : kˣ) : k)))
    iota.liftRoot
    (fun _ ↦ 0)

@[simp]
theorem lift_coe (iota : PrimeRegularRootEmbedding p k K G)
    (zeta : rootsOfUnity (primeRegularExponent p G) k) :
    iota.lift (((zeta : kˣ) : k)) = iota.liftRoot zeta := by
  exact (Units.val_injective.comp Subtype.val_injective).extend_apply _ _ zeta

end PrimeRegularRootEmbedding

end ModularRep

namespace Representation

universe u v w x

variable {p : ℕ} {k : Type w} {K : Type x} {G : Type u} {V : Type v}
variable [Field k] [Field K] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Package a characteristic-polynomial root at a `p`-regular element as a
root of unity of the common prime regular exponent. -/
noncomputable def charpolyRootAsRootOfUnity
    (rho : Representation k G V)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (g : ModularRep.PrimeRegularElement (G := G) p)
    (a : {a : k // a ∈ (rho g.1).charpoly.roots}) :
    rootsOfUnity (ModularRep.primeRegularExponent p G) k := by
  letI : NeZero (ModularRep.primeRegularExponent p G) :=
    ⟨(ModularRep.primeRegularExponent_pos p G).ne'⟩
  exact rootsOfUnity.mkOfPowEq a.1
    (rho.charpolyRoot_pow_primeRegularExponent_eq_one iota.prime g a.2)

@[simp]
theorem coe_charpolyRootAsRootOfUnity
    (rho : Representation k G V)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (g : ModularRep.PrimeRegularElement (G := G) p)
    (a : {a : k // a ∈ (rho g.1).charpoly.roots}) :
    ((((rho.charpolyRootAsRootOfUnity iota g a :
        rootsOfUnity (ModularRep.primeRegularExponent p G) k) : kˣ) : k)) =
      a.1 :=
  rfl

/-- On every characteristic-polynomial root that occurs at a `p`-regular
element, the total field-level lift agrees with the chosen root equivalence. -/
theorem lift_charpolyRootAsRootOfUnity
    (rho : Representation k G V)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (g : ModularRep.PrimeRegularElement (G := G) p)
    (a : {a : k // a ∈ (rho g.1).charpoly.roots}) :
    iota.lift a.1 =
      iota.liftRoot (rho.charpolyRootAsRootOfUnity iota g a) := by
  simpa only [coe_charpolyRootAsRootOfUnity] using
    iota.lift_coe (rho.charpolyRootAsRootOfUnity iota g a)

/-- The action of a group element as a linear equivalence. -/
def actionLinearEquiv (rho : Representation k G V) (x : G) : V ≃ₗ[k] V where
  toLinearMap := rho x
  invFun := rho x⁻¹
  left_inv := rho.inv_self_apply x
  right_inv := rho.self_inv_apply x

omit [Finite G] [FiniteDimensional k V] in
@[simp]
theorem actionLinearEquiv_apply (rho : Representation k G V) (x : G) (v : V) :
    rho.actionLinearEquiv x v = rho x v :=
  rfl

omit [Finite G] in
/-- Conjugate group elements have the same characteristic polynomial in a
finite dimensional representation. -/
theorem charpoly_conj (rho : Representation k G V) (g x : G) :
    (rho (x * g * x⁻¹)).charpoly = (rho g).charpoly := by
  have hconj :
      rho (x * g * x⁻¹) = (rho.actionLinearEquiv x).conj (rho g) := by
    ext v
    simp [actionLinearEquiv, LinearEquiv.conj_apply_apply,
      ← Module.End.mul_apply, ← map_mul, mul_assoc]
  rw [hconj]
  exact LinearEquiv.charpoly_conj (rho.actionLinearEquiv x) (rho g)

/-- The Brauer character associated with a modular representation and an
explicit multiplicative lift of the required roots of unity. -/
noncomputable def brauerCharacterOfRootEmbedding
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (rho : Representation k G V)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G) :
    ModularRep.PrimeRegularClassFunction K G p :=
  ModularRep.PrimeRegularClassFunction.ofFunction
    (fun g ↦ ((rho g).charpoly.roots.map iota.lift).sum)
    (fun x g ↦ by rw [rho.charpoly_conj g x])

@[simp]
theorem brauerCharacterOfRootEmbedding_apply
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (rho : Representation k G V)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (g : ModularRep.PrimeRegularElement (G := G) p) :
    rho.brauerCharacterOfRootEmbedding iota g =
      ((rho g.1).charpoly.roots.map iota.lift).sum :=
  rfl

/-- Brauer-character formation commutes with the manuscript's right
automorphism action. -/
@[simp]
theorem brauerCharacterOfRootEmbedding_twist
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (rho : Representation k G V)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (alpha : MulAut G) :
    (rho.twist alpha).brauerCharacterOfRootEmbedding iota =
      (rho.brauerCharacterOfRootEmbedding iota).twist alpha := by
  ext g
  rfl

/-- At a central `p`-regular element, the Brauer-character value is the
dimension times the lifted central character scalar. -/
theorem brauerCharacterOfRootEmbedding_apply_central
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (rho : Representation k G V) [rho.IsIrreducible]
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) (z : Z)
    (hz : ModularRep.IsPrimeRegular p (z : G)) :
    rho.brauerCharacterOfRootEmbedding iota ⟨(z : G), hz⟩ =
      (Module.finrank k V : K) *
        iota.lift (rho.centralCharacter Z hZ z : k) := by
  change ((rho (z : G)).charpoly.roots.map iota.lift).sum = _
  simpa only [nsmul_eq_mul] using
    rho.sum_map_roots_charpoly_centralCharacter iota.lift Z hZ z

end Representation

namespace Representation

universe y z

variable {p : ℕ} {k G : Type y} {K : Type z}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Isomorphic finite dimensional representations afford the same
function-valued Brauer character. -/
theorem brauerCharacterOfRootEmbedding_iso
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    {V W : FDRep k G} (e : V ≅ W) :
    Representation.brauerCharacterOfRootEmbedding V.ρ iota =
      Representation.brauerCharacterOfRootEmbedding W.ρ iota := by
  ext g
  change ((V.ρ g.1).charpoly.roots.map iota.lift).sum =
    ((W.ρ g.1).charpoly.roots.map iota.lift).sum
  rw [FDRep.Iso.conj_ρ e g.1, LinearEquiv.charpoly_conj]

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
