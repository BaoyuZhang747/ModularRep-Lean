import ModularRep.PaperProofs.TypeBTwoCommon
import ModularRep.PaperProofs.TypeBLocalizedReturnLemma49Relative

/-!
# A conditional strong induction for type B at the prime 2

The central-cover, odd-label, and orbit-stabiliser deductions are in
`TypeBTwoCommon`. This module proves a strong induction from the specified
selector and reduction implications, followed at each rank by the
conditional reduction associated with Lemma 4.12.

The representation theoretic inputs are kept separate.  No blockwise BAW,
iBAW, Assumption 5.3, or desired all-ranks conclusion is an input.
-/

namespace ModularRep.PaperProofs.TypeBTwoHighRankProposition410Relative

section StrongInduction

open ModularRep.PaperProofs.TypeBLocalizedReturnLemma49Relative

universe uB uF

variable {Block : ℕ → Type uB} {Factor : ℕ → Type uF}

/-- The specified stages of the induction on the rank.

The intermediate propositions prevent a single callback from concealing the
desired all-orbit selector.  The intended instantiations are respectively the
normal-core transport of Lemma 2.6, the component return of Lemmas 4.4--4.5,
the characteristic-two Clifford deduction of Lemma 4.6, and the equivariant
Jordan/BDR transfer.  The final `localizedInputs` field contains the precise
factor-by-factor hypotheses of Lemma 4.12, not its conclusion. -/
structure HighRankAssemblyInputs (n0 : ℕ) where
  OrbitSelectors : ℕ → Prop
  PrincipalSelectors : ℕ → Prop
  QuotientFactorMaps : ℕ → Prop
  SpinFactorMaps : ℕ → Prop
  FactorMaps : ℕ → Prop
  ComponentRepresentatives : ℕ → Prop
  LeviRepresentatives : ℕ → Prop
  NonprincipalSelectors : ℕ → Prop
  PrincipalFieldFixed : ℕ → Prop
  BlockGood : ∀ r, Block r → Prop

  principalSelectors : ∀ r, 4 ≤ r → r ≤ n0 → PrincipalSelectors r
  quotientFactorMaps_of_lower : ∀ r, 4 ≤ r → r ≤ n0 →
    (∀ m, 4 ≤ m → m < r → OrbitSelectors m) → QuotientFactorMaps r
  spinFactorMaps_of_normalCore : ∀ r,
    QuotientFactorMaps r → SpinFactorMaps r
  factorMaps_of_lower : ∀ r, 4 ≤ r → r ≤ n0 →
    (∀ m, 4 ≤ m → m < r → OrbitSelectors m) →
    SpinFactorMaps r → FactorMaps r
  componentRepresentatives_of_factorMaps : ∀ r,
    FactorMaps r → ComponentRepresentatives r
  leviRepresentatives_of_componentRepresentatives : ∀ r,
    ComponentRepresentatives r → LeviRepresentatives r
  nonprincipalSelectors_of_leviRepresentatives : ∀ r,
    LeviRepresentatives r → NonprincipalSelectors r
  orbitSelectors_of_principal_and_nonprincipal : ∀ r,
    PrincipalSelectors r → NonprincipalSelectors r → OrbitSelectors r
  principalFieldFixed : ∀ r, 4 ≤ r → r ≤ n0 → PrincipalFieldFixed r

  localizedInputs : ∀ r, 4 ≤ r → r ≤ n0 →
    OrbitSelectors r →
    (∀ m, 4 ≤ m → m < r → OrbitSelectors m) →
    PrincipalFieldFixed r →
    {D : Inputs (Block := Block r) (Factor := Factor r) r n0 //
      D.BlockGood = BlockGood r}

namespace HighRankAssemblyInputs

/-- The checked outcome of the finite strong induction. -/
structure Conclusion
    {n0 : ℕ} (I : HighRankAssemblyInputs
      (Block := Block) (Factor := Factor) n0) where
  orbitSelectors : ∀ r, 4 ≤ r → r ≤ n0 → I.OrbitSelectors r
  allBlocksGood : ∀ r, 4 ≤ r → r ≤ n0 → ∀ b : Block r,
    I.BlockGood r b

/-- The conditional strong induction. At each rank Lean first
constructs the orbit-selector stages from lower ranks and then applies the
protected relative Lemma 4.12 to the exact factor data for that rank. -/
theorem proposition_4_10_ranked_assembly
    {n0 : ℕ} (I : HighRankAssemblyInputs
      (Block := Block) (Factor := Factor) n0) :
    Conclusion I := by
  have selectors : ∀ r, 4 ≤ r → r ≤ n0 → I.OrbitSelectors r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro hr hrn0
        have lower : ∀ m, 4 ≤ m → m < r → I.OrbitSelectors m := by
          intro m hm hmr
          exact ih m hmr hm (Nat.le_trans (Nat.le_of_lt hmr) hrn0)
        have quotientMaps := I.quotientFactorMaps_of_lower r hr hrn0 lower
        have spinMaps := I.spinFactorMaps_of_normalCore r quotientMaps
        have factorMaps := I.factorMaps_of_lower r hr hrn0 lower spinMaps
        have componentRepresentatives :=
          I.componentRepresentatives_of_factorMaps r factorMaps
        have leviRepresentatives :=
          I.leviRepresentatives_of_componentRepresentatives r
            componentRepresentatives
        have nonprincipalSelectors :=
          I.nonprincipalSelectors_of_leviRepresentatives r leviRepresentatives
        exact I.orbitSelectors_of_principal_and_nonprincipal r
          (I.principalSelectors r hr hrn0) nonprincipalSelectors
  refine ⟨selectors, ?_⟩
  intro r hr hrn0
  have lower : ∀ m, 4 ≤ m → m < r → I.OrbitSelectors m := by
    intro m hm hmr
    exact selectors m hm (Nat.le_trans (Nat.le_of_lt hmr) hrn0)
  obtain ⟨D, hBlockGood⟩ := I.localizedInputs r hr hrn0
    (selectors r hr hrn0) lower (I.principalFieldFixed r hr hrn0)
  have hgood : ∀ b : Block r, D.BlockGood b :=
    D.lemma_4_9_relative hr hrn0
  rw [hBlockGood] at hgood
  exact hgood

end HighRankAssemblyInputs

end StrongInduction

end ModularRep.PaperProofs.TypeBTwoHighRankProposition410Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
