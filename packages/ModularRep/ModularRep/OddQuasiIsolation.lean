import ModularRep.PrimeRegular

/-!
# Odd quasi-isolated parameters

This module isolates the elementary order argument used in the odd-field,
characteristic-two reduction: an element whose order is coprime to `2` and
whose square is one must itself be one.

The surrounding representation theory is deliberately exposed as input.
In particular, this file supplies neither Bonnafé's square theorem, nor the
semantic identification of a `2'`-element with an element whose `orderOf` is
coprime to `2`, nor the block-theoretic passage from the parameter `1` to the
principal block.
-/

namespace ModularRep

namespace IsPrimeRegular

variable {G : Type*} [Monoid G] {n : ℕ} {s : G}

/-- If the order of `s` is coprime to `n` and `s ^ n = 1`, then `s = 1`. -/
theorem eq_one_of_pow_eq_one (hs : IsPrimeRegular n s) (hpow : s ^ n = 1) :
    s = 1 := by
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hs dvd_rfl (orderOf_dvd_of_pow_eq_one hpow)

/-- A `2`-regular element whose square is one is the identity. -/
theorem eq_one_of_sq_eq_one (hs : IsPrimeRegular 2 s) (hsq : s ^ 2 = 1) :
    s = 1 :=
  hs.eq_one_of_pow_eq_one hsq

end IsPrimeRegular

namespace OddQuasiIsolation

variable {G Block : Type*} [Monoid G]

/-- The shape of the external Bonnafé input used by the reduction.

No inhabitant of this type is provided here: applications must supply the
relevant square theorem for their notion of strict quasi-isolation.
-/
abbrev BonnafeSquareInterface (IsStrictlyQuasiIsolated : G → Prop) : Prop :=
  ∀ {s : G}, IsStrictlyQuasiIsolated s → s ^ 2 = 1

/-- The semantic bridge from an application's notion of a `2'`-element to
the `orderOf`-based predicate used by the elementary argument.

No inhabitant of this type is provided here.
-/
abbrev TwoPrimeOrderInterface (IsSemisimpleTwoPrime : G → Prop) : Prop :=
  ∀ {s : G}, IsSemisimpleTwoPrime s → IsPrimeRegular 2 s

/-- The shape of the external block-theoretic implication used after the
semisimple parameter has been proved equal to one.

`IsAssociated c s` can encode, for example, the required Lusztig-series
condition.  No block theory or inhabitant of this interface is provided here.
-/
abbrev PrincipalBlockInterface
    (IsAssociated : Block → G → Prop) (IsPrincipalBlock : Block → Prop) : Prop :=
  ∀ {c : Block} {s : G}, IsAssociated c s → s = 1 → IsPrincipalBlock c

/-- A strictly quasi-isolated semisimple `2'`-parameter is one, conditional
on the explicit square theorem and semantic order bridge.
-/
theorem parameter_eq_one
    {IsStrictlyQuasiIsolated IsSemisimpleTwoPrime : G → Prop} {s : G}
    (bonnafeSquare : BonnafeSquareInterface IsStrictlyQuasiIsolated)
    (twoPrimeOrder : TwoPrimeOrderInterface IsSemisimpleTwoPrime)
    (hstrict : IsStrictlyQuasiIsolated s)
    (htwoPrime : IsSemisimpleTwoPrime s) :
    s = 1 :=
  (twoPrimeOrder htwoPrime).eq_one_of_sq_eq_one (bonnafeSquare hstrict)

/-- The principal-block conclusion of the reduction, conditional on all
three external interfaces: the square theorem, the semantic order bridge,
and the block-theoretic implication at parameter one.
-/
theorem isPrincipalBlock_of_strictlyQuasiIsolated_twoPrime
    {IsStrictlyQuasiIsolated IsSemisimpleTwoPrime : G → Prop}
    {IsAssociated : Block → G → Prop} {IsPrincipalBlock : Block → Prop}
    {s : G} {c : Block}
    (bonnafeSquare : BonnafeSquareInterface IsStrictlyQuasiIsolated)
    (twoPrimeOrder : TwoPrimeOrderInterface IsSemisimpleTwoPrime)
    (principalBlock : PrincipalBlockInterface IsAssociated IsPrincipalBlock)
    (hstrict : IsStrictlyQuasiIsolated s)
    (htwoPrime : IsSemisimpleTwoPrime s)
    (hassociated : IsAssociated c s) :
    IsPrincipalBlock c := by
  exact principalBlock hassociated
    (parameter_eq_one bonnafeSquare twoPrimeOrder hstrict htwoPrime)

end OddQuasiIsolation

namespace TypeBQuasiIsolation

variable {G Ghat Block : Type*} [Monoid G] [Monoid Ghat]

/-- An element of odd order whose order divides four is the identity. -/
theorem eq_one_of_odd_order_of_orderOf_dvd_four
    {s : Ghat} (hOdd : Odd (orderOf s)) (hFour : orderOf s ∣ 4) :
    s = 1 := by
  have hCoprime : Nat.Coprime (orderOf s) 4 := by
    simpa only [show 4 = 2 ^ 2 by decide] using
      hOdd.coprime_two_right.pow_right 2
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hCoprime dvd_rfl hFour)

/-- Source-shaped form of Bonnafé's order bound for a chosen lift of a
quasi-isolated parameter. -/
def BonnafeOrderFourLiftInterface
    (IsQuasiIsolated : G → Prop) (IsLift : G → Ghat → Prop) : Prop :=
  ∀ {s : G} {shat : Ghat}, IsQuasiIsolated s → IsLift s shat →
    orderOf shat ∣ 4

/-- Source-shaped block-theoretic input saying that the identity semisimple
label gives the principal block. -/
def IdentityLabelPrincipalBlockInterface
    (IsAssociated : Block → G → Prop)
    (IsPrincipalBlock : Block → Prop) : Prop :=
  ∀ {b : Block}, IsAssociated b 1 → IsPrincipalBlock b

/-- The order deduction for a quasi-isolated element with an odd-order
lift.  A quasi-isolated odd-order lift has order dividing four,
hence is the identity, and so is the parameter below it. -/
theorem parameter_eq_one_of_quasiIsolated_odd_lift
    {IsQuasiIsolated : G → Prop} {IsLift : G → Ghat → Prop}
    {s : G} {shat : Ghat}
    (bonnafe : BonnafeOrderFourLiftInterface IsQuasiIsolated IsLift)
    (projection : Ghat →* G)
    (hQuasi : IsQuasiIsolated s)
    (hLift : IsLift s shat)
    (hProjection : projection shat = s)
    (hOdd : Odd (orderOf shat)) :
    s = 1 := by
  have hHat : shat = 1 :=
    eq_one_of_odd_order_of_orderOf_dvd_four hOdd
      (bonnafe hQuasi hLift)
  rw [← hProjection, hHat, map_one]

/-- Consequently, a nonprincipal block with an odd-order lifted semisimple
label cannot have a quasi-isolated label.  The Bonnafé order bound and the
identity-label block theorem remain separate, recognisable external inputs. -/
theorem nonprincipal_label_not_quasiIsolated
    {IsQuasiIsolated : G → Prop} {IsLift : G → Ghat → Prop}
    {IsAssociated : Block → G → Prop}
    {IsPrincipalBlock : Block → Prop}
    {b : Block} {s : G} {shat : Ghat}
    (bonnafe : BonnafeOrderFourLiftInterface IsQuasiIsolated IsLift)
    (identityPrincipal :
      IdentityLabelPrincipalBlockInterface IsAssociated IsPrincipalBlock)
    (projection : Ghat →* G)
    (hAssociated : IsAssociated b s)
    (hLift : IsLift s shat)
    (hProjection : projection shat = s)
    (hOdd : Odd (orderOf shat))
    (hNonprincipal : ¬ IsPrincipalBlock b) :
    ¬ IsQuasiIsolated s := by
  intro hQuasi
  have hs : s = 1 :=
    parameter_eq_one_of_quasiIsolated_odd_lift bonnafe projection
      hQuasi hLift hProjection hOdd
  apply hNonprincipal
  apply identityPrincipal
  simpa [hs] using hAssociated

end TypeBQuasiIsolation

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
