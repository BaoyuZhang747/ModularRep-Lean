import Mathlib.Tactic

/-!
# Paper proof: the localised return in type B

This file checks the case routing in manuscript Lemma 4.12.  The cited
representation theory is kept in source-shaped interfaces.  Lean proves that
the listed type A and lower-rank type B inputs cover every simple factor that
can occur in the proper Levi reduction, and then applies the reduction only
after complete factor data and the short-root return condition have been
combined.

No blockwise conclusion for the ambient group is a premise.  The only
ambient reduction input is an implication for a nonprincipal block whose
antecedents are the complete data for every factor actually occurring in
that block.
-/

namespace ModularRep.PaperProofs.TypeBLocalizedReturnLemma49Relative

/-- The two families of simple factors occurring in the derived subgroup of
a proper Levi of type `B`. -/
inductive FactorFamily where
  | typeA
  | typeB
  deriving DecidableEq

universe uB uF

variable {Block : Type uB} {Factor : Type uF}

/-- Exact source-shaped inputs for the localised reduction at a fixed ambient
rank `r`, with all ranks bounded by `n0`.

`FactorGood f` means that the block on the factor `f` has the full map needed
by the reduction, including equivariance, extensions, factor sets, and the
required block equalities.  `ReturnControlled f` is the assertion supplied
by the short-root orbit analysis: the type `B` factor is not lost in a
nontrivial permutation orbit and its return automorphism is the one for which
the chosen factor data are valid. -/
structure Inputs (r n0 : ℕ) where
  isPrincipal : Block → Prop
  family : Factor → FactorFamily
  rank : Factor → ℕ
  factorBlockPrincipal : Factor → Prop
  Occurs : Block → Factor → Prop
  FactorGood : Factor → Prop
  ReturnControlled : Factor → Prop
  BlockGood : Block → Prop

  /-- Dynkin-diagram classification for every factor that actually occurs. -/
  family_cases : ∀ b f, Occurs b f →
    family f = .typeA ∨ family f = .typeB
  typeB_rank_positive : ∀ b f, Occurs b f → family f = .typeB →
    1 ≤ rank f
  typeB_rank_smaller : ∀ b f, Occurs b f → family f = .typeB →
    rank f < r
  typeB_block_principal : ∀ b f, Occurs b f → family f = .typeB →
    factorBlockPrincipal f
  typeB_return_controlled : ∀ b f, Occurs b f → family f = .typeB →
    ReturnControlled f

  /-- Complete factor maps supplied by the cited results and the earlier
  manuscript propositions. -/
  typeA_good : ∀ f, family f = .typeA → FactorGood f
  typeB_rank_one_good : ∀ f,
    family f = .typeB → rank f = 1 → factorBlockPrincipal f → FactorGood f
  typeB_rank_two_good : ∀ f,
    family f = .typeB → rank f = 2 → factorBlockPrincipal f → FactorGood f
  typeB_rank_three_good : ∀ f,
    family f = .typeB → rank f = 3 → factorBlockPrincipal f → FactorGood f
  typeB_high_rank_principal_good : ∀ f,
    family f = .typeB → 4 ≤ rank f → rank f ≤ n0 →
      factorBlockPrincipal f → FactorGood f

  /-- The principal ambient block is supplied directly. -/
  principal_good : ∀ b, isPrincipal b → BlockGood b

  /-- Source-shaped form of the Feng--Li--Zhang reduction for a
  nonprincipal block.  It may be applied only after data have been supplied
  for every factor that occurs and the type `B` return has been controlled. -/
  nonprincipal_reduction : ∀ b, ¬ isPrincipal b →
    (∀ f, Occurs b f → FactorGood f) →
    (∀ f, Occurs b f → family f = .typeB → ReturnControlled f) →
    BlockGood b

namespace Inputs

/-- The manuscript's factor list is exhaustive.  In particular, the
high-rank branch is available because a type `B` factor has rank smaller than
the ambient rank, while the ambient rank is at most `n0`. -/
theorem factor_good_of_occurs
    {r n0 : ℕ} (D : Inputs (Block := Block) (Factor := Factor) r n0)
    (hrn0 : r ≤ n0) {b : Block} {f : Factor}
    (hf : D.Occurs b f) : D.FactorGood f := by
  rcases D.family_cases b f hf with hA | hB
  · exact D.typeA_good f hA
  · have hpos : 1 ≤ D.rank f := D.typeB_rank_positive b f hf hB
    have hlt : D.rank f < r := D.typeB_rank_smaller b f hf hB
    have hprincipal : D.factorBlockPrincipal f :=
      D.typeB_block_principal b f hf hB
    rcases show D.rank f = 1 ∨ D.rank f = 2 ∨ D.rank f = 3 ∨ 4 ≤ D.rank f by
      omega with h1 | h2 | h3 | h4
    · exact D.typeB_rank_one_good f hB h1 hprincipal
    · exact D.typeB_rank_two_good f hB h2 hprincipal
    · exact D.typeB_rank_three_good f hB h3 hprincipal
    · exact D.typeB_high_rank_principal_good f hB h4
        (by omega) hprincipal

/-- Every ambient block is covered by the principal construction or by the
localised proper-Levi reduction. -/
theorem lemma_4_9_relative
    {r n0 : ℕ} (D : Inputs (Block := Block) (Factor := Factor) r n0)
    (_hr : 4 ≤ r) (hrn0 : r ≤ n0) :
    ∀ b : Block, D.BlockGood b := by
  intro b
  by_cases hb : D.isPrincipal b
  · exact D.principal_good b hb
  · apply D.nonprincipal_reduction b hb
    · intro f hf
      exact D.factor_good_of_occurs hrn0 hf
    · intro f hf hB
      exact D.typeB_return_controlled b f hf hB

end Inputs

end ModularRep.PaperProofs.TypeBLocalizedReturnLemma49Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
