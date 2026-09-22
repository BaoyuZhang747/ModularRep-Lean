import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Prime regular elements

An element is `p`-regular when its order is coprime to `p`.  The definition is
made for an arbitrary natural number; the usual equivalent statement that
`p` does not divide the order requires the separate hypothesis `p.Prime`.
-/

namespace ModularRep

variable {G H : Type*} {p : ℕ}

/-- An element is `p`-regular when its order is coprime to `p`.

For a prime `p`, this is equivalent to saying that `p` does not divide the
order of the element; see `isPrimeRegular_iff_not_dvd`.
-/
def IsPrimeRegular [Monoid G] (p : ℕ) (g : G) : Prop :=
  (orderOf g).Coprime p

/-- The subtype of `p`-regular elements of a monoid. -/
def PrimeRegularElement [Monoid G] (p : ℕ) :=
  {g : G // IsPrimeRegular p g}

theorem isPrimeRegular_iff_not_dvd [Monoid G] (hp : p.Prime) (g : G) :
    IsPrimeRegular p g ↔ ¬ p ∣ orderOf g := by
  simpa only [IsPrimeRegular, Nat.coprime_comm] using
    (hp.coprime_iff_not_dvd (n := orderOf g))

@[simp]
theorem isPrimeRegular_one [Monoid G] : IsPrimeRegular p (1 : G) := by
  simp [IsPrimeRegular]

namespace IsPrimeRegular

variable [Monoid G] {g : G}

/-- A monoid homomorphism sends a `p`-regular element to a `p`-regular element. -/
theorem map [Monoid H] (hg : IsPrimeRegular p g) (f : G →* H) :
    IsPrimeRegular p (f g) :=
  Nat.Coprime.of_dvd_left (orderOf_map_dvd f g) hg

/-- Every nonnegative power of a `p`-regular element is `p`-regular. -/
theorem pow (hg : IsPrimeRegular p g) (n : ℕ) : IsPrimeRegular p (g ^ n) :=
  Nat.Coprime.of_dvd_left (orderOf_pow_dvd (x := g) n) hg

end IsPrimeRegular

@[simp]
theorem isPrimeRegular_map_mulEquiv [Monoid G] [Monoid H] (e : G ≃* H) (g : G) :
    IsPrimeRegular p (e g) ↔ IsPrimeRegular p g := by
  simp only [IsPrimeRegular, MulEquiv.orderOf_eq]

@[simp]
theorem isPrimeRegular_inv [Group G] (g : G) :
    IsPrimeRegular p g⁻¹ ↔ IsPrimeRegular p g := by
  simp only [IsPrimeRegular, orderOf_inv]

namespace IsPrimeRegular

variable [Group G] {g : G}

/-- A conjugate of a `p`-regular element is `p`-regular. -/
theorem conj (hg : IsPrimeRegular p g) (x : G) :
    IsPrimeRegular p (x * g * x⁻¹) := by
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
    IsPrimeRegular.map hg (MulAut.conj x).toMonoidHom

/-- If the group order is coprime to `p`, every element is `p`-regular. -/
theorem of_coprime_natCard (hG : (Nat.card G).Coprime p) (g : G) :
    IsPrimeRegular p g :=
  Nat.Coprime.of_dvd_left (orderOf_dvd_natCard g) hG

end IsPrimeRegular

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
