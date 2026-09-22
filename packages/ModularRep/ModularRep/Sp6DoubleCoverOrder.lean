import ModularRep.CyclicSylow

/-!
# The order calculation for the double cover of `Sp₆(2)`

This file isolates only the elementary finite group consequence of the order
formula used in Proposition 3.9 of the manuscript.  Malle--Testerman,
Table 24.1 gives the order of `Sp₆(2)`, while Remark 24.19 and Table 24.3
give its exceptional multiplier of order two.  The Lean theorems below do
not identify any concrete group with the resulting abstract order and contain
no block-theoretic claim.
-/

namespace ModularRep.ManuscriptVerification.Sp6DoubleCoverOrder

/-- The order occurring for the exceptional double cover `2.Sp₆(2)`. -/
def sp6DoubleCoverOrder : ℕ := 2 ^ 10 * 3 ^ 4 * 5 * 7

/-- The prime divisors of the specified order are exactly `2`, `3`, `5`,
and `7`.  The representation theoretic application still has to identify
the order of the concrete universal cover with `sp6DoubleCoverOrder`. -/
theorem prime_dvd_sp6DoubleCoverOrder
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ sp6DoubleCoverOrder) :
    ell = 2 ∨ ell = 3 ∨ ell = 5 ∨ ell = 7 := by
  rw [sp6DoubleCoverOrder] at hdiv
  rcases (hell.dvd_mul.mp hdiv) with h235 | h7
  · rcases (hell.dvd_mul.mp h235) with h23 | h5
    · rcases (hell.dvd_mul.mp h23) with h2 | h3
      · exact Or.inl
          ((Nat.prime_dvd_prime_iff_eq hell Nat.prime_two).mp
            (hell.dvd_of_dvd_pow h2))
      · exact Or.inr <| Or.inl
          ((Nat.prime_dvd_prime_iff_eq hell (by decide)).mp
            (hell.dvd_of_dvd_pow h3))
    · exact Or.inr <| Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hell (by decide)).mp h5)
  · exact Or.inr <| Or.inr <| Or.inr
      ((Nat.prime_dvd_prime_iff_eq hell (by decide)).mp h7)

/-- The `5`-part of the specified order is `5`. -/
theorem fivePart_sp6DoubleCoverOrder :
    5 ^ (sp6DoubleCoverOrder.factorization 5) = 5 := by
  have hp : Nat.Prime 5 := by decide
  have hn : sp6DoubleCoverOrder ≠ 0 := by
    norm_num [sp6DoubleCoverOrder]
  have hlower : 1 ≤ sp6DoubleCoverOrder.factorization 5 :=
    (hp.dvd_iff_one_le_factorization hn).mp (by
      norm_num [sp6DoubleCoverOrder])
  have hupper : sp6DoubleCoverOrder.factorization 5 < 2 := by
    rw [← not_le]
    intro h
    have hdvd : 5 ^ 2 ∣ sp6DoubleCoverOrder :=
      (hp.pow_dvd_iff_le_factorization hn).mpr h
    norm_num [sp6DoubleCoverOrder] at hdvd
  have : sp6DoubleCoverOrder.factorization 5 = 1 := by omega
  simp [this]

/-- The `7`-part of the specified order is `7`. -/
theorem sevenPart_sp6DoubleCoverOrder :
    7 ^ (sp6DoubleCoverOrder.factorization 7) = 7 := by
  have hp : Nat.Prime 7 := by decide
  have hn : sp6DoubleCoverOrder ≠ 0 := by
    norm_num [sp6DoubleCoverOrder]
  have hlower : 1 ≤ sp6DoubleCoverOrder.factorization 7 :=
    (hp.dvd_iff_one_le_factorization hn).mp (by
      norm_num [sp6DoubleCoverOrder])
  have hupper : sp6DoubleCoverOrder.factorization 7 < 2 := by
    rw [← not_le]
    intro h
    have hdvd : 7 ^ 2 ∣ sp6DoubleCoverOrder :=
      (hp.pow_dvd_iff_le_factorization hn).mpr h
    norm_num [sp6DoubleCoverOrder] at hdvd
  have : sp6DoubleCoverOrder.factorization 7 = 1 := by omega
  simp [this]

/-- Every Sylow `5`-subgroup of an abstract finite group of the specified
order has order `5`. -/
theorem card_sylow_five
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = sp6DoubleCoverOrder) (P : Sylow 5 G) :
    Nat.card P = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [P.card_eq_multiplicity, hcard]
  exact fivePart_sp6DoubleCoverOrder

/-- Every Sylow `7`-subgroup of an abstract finite group of the specified
order has order `7`. -/
theorem card_sylow_seven
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = sp6DoubleCoverOrder) (P : Sylow 7 G) :
    Nat.card P = 7 := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [P.card_eq_multiplicity, hcard]
  exact sevenPart_sp6DoubleCoverOrder

/-- Every Sylow `5`-subgroup of an abstract finite group of the specified
order is cyclic. -/
theorem isCyclic_sylow_five
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = sp6DoubleCoverOrder) (P : Sylow 5 G) :
    IsCyclic P := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact isCyclic_of_prime_card (card_sylow_five hcard P)

/-- Every Sylow `7`-subgroup of an abstract finite group of the specified
order is cyclic. -/
theorem isCyclic_sylow_seven
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = sp6DoubleCoverOrder) (P : Sylow 7 G) :
    IsCyclic P := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact isCyclic_of_prime_card (card_sylow_seven hcard P)

/-- Every `5`-subgroup of an abstract finite group of the specified order is
cyclic.  This is the block-independent endpoint needed before importing the
external fact that block defect groups are `5`-subgroups. -/
theorem isCyclic_five_subgroup
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = sp6DoubleCoverOrder)
    (D : Subgroup G) (hD : IsPGroup 5 D) : IsCyclic D := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 G := default
  let _ : IsCyclic P := isCyclic_sylow_five hcard P
  apply
    CyclicSylow.isCyclic_of_isPGroup_of_full_part_dvd_card_cyclic_subgroup
      P _ D hD
  rw [card_sylow_five hcard P, hcard, fivePart_sp6DoubleCoverOrder]

/-- Every `7`-subgroup of an abstract finite group of the specified order is
cyclic.  As above, this statement contains no block theory. -/
theorem isCyclic_seven_subgroup
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = sp6DoubleCoverOrder)
    (D : Subgroup G) (hD : IsPGroup 7 D) : IsCyclic D := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 7 G := default
  let _ : IsCyclic P := isCyclic_sylow_seven hcard P
  apply
    CyclicSylow.isCyclic_of_isPGroup_of_full_part_dvd_card_cyclic_subgroup
      P _ D hD
  rw [card_sylow_seven hcard P, hcard, sevenPart_sp6DoubleCoverOrder]

end ModularRep.ManuscriptVerification.Sp6DoubleCoverOrder


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
