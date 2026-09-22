import ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions

/-!
# One finite root table through actual group coordinates

Equivalent finite groups have the same prime regular exponent. Transport
of a restriction of ONE finite root table therefore equals its restriction
on the target group. The equality follows from that actual exponent
equality and root-record extensionality, not from a comparison of
independently prescribed conventions.

The compatibility helpers only replace an existing target/source lift by
a literally equal lift function. The backward-transport helpers compare
an arbitrary root with ITS computed transport. Every declaration is K;
no family convention, root-table existence, relation or seed is supplied.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoCommonRootGroupEquiv

open ModularRep
open ModularRep.PrimeRegularRootEmbedding
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions

universe u

variable {p m : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [Group G] [Finite G] [Group H] [Finite H]

/-- The equality is derived from the order of the actual equivalent groups. -/
theorem exponent_eq_of_groupEquiv (e : G ≃* H) :
    primeRegularExponent p G = primeRegularExponent p H :=
  congrArg (fun n : ℕ => ordCompl[p] n) (Nat.card_congr e.toEquiv)

private theorem restrict_table_cast {a b : ℕ} (h : a = b)
    (table : rootsOfUnity m k ≃* rootsOfUnity m K)
    (ha : a ∣ m) (hb : b ∣ m) :
    Eq.ndrec (motive := fun n : ℕ => rootsOfUnity n k ≃* rootsOfUnity n K)
      (restrictRootsOfUnityEquiv ha table) h =
        restrictRootsOfUnityEquiv hb table := by
  subst b
  rfl

/-- Restrictions of the SAME table commute with transport along the actual
group equivalence. Both displayed divisibility proofs bound that table. -/
theorem ofCommonRoot_alongMulEquiv (hp : p.Prime)
    (table : rootsOfUnity m k ≃* rootsOfUnity m K)
    (hG : primeRegularExponent p G ∣ m)
    (hH : primeRegularExponent p H ∣ m) (e : G ≃* H) :
    (PrimeRegularRootEmbedding.ofCommonRoot hp table hG).alongMulEquiv e =
      PrimeRegularRootEmbedding.ofCommonRoot hp table hH := by
  apply root_eq_of_table_eq
  change Eq.ndrec
      (motive := fun n : ℕ => rootsOfUnity n k ≃* rootsOfUnity n K)
      (restrictRootsOfUnityEquiv hG table) (exponent_eq_of_groupEquiv e) =
    restrictRootsOfUnityEquiv hH table
  exact restrict_table_cast (exponent_eq_of_groupEquiv e) table hG hH

/-- Along an equivalence and its inverse, the lift function remains that
of the original root. This does not identify an independently chosen root. -/
theorem alongMulEquiv_inverse_lift (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) :
    ((iota.alongMulEquiv e).alongMulEquiv e.symm).lift = iota.lift := by
  funext z
  exact ((iota.alongMulEquiv e).alongMulEquiv_lift e.symm z).trans
    (iota.alongMulEquiv_lift e z)

section Compatibility

variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Replace only the target-group lift in an existing compatibility square.
Literal equality is an explicit rewrite premise, never a new source law. -/
theorem compatible_replace_target_lift
    (iotaG jG : PrimeRegularRootEmbedding p k K G)
    (iotaH : PrimeRegularRootEmbedding p k K H) (f : H →* G)
    (lift_eq : iotaG.lift = jG.lift)
    (compatible : RootCompatibleAlong iotaG iotaH f) :
    RootCompatibleAlong jG iotaH f := by
  intro V x a
  exact (compatible V x a).trans (congrFun lift_eq a.1)

/-- Replace only the source-group lift, keeping the target root and actual
homomorphism fixed. Equality of character values is not used. -/
theorem compatible_replace_source_lift
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (iotaH jH : PrimeRegularRootEmbedding p k K H) (f : H →* G)
    (lift_eq : iotaH.lift = jH.lift)
    (compatible : RootCompatibleAlong iotaG iotaH f) :
    RootCompatibleAlong iotaG jH f := by
  intro V x a
  exact (congrFun lift_eq a.1).symm.trans (compatible V x a)

/-- Pulling an arbitrary target root backward supplies the exact horizontal
square along the original forward map. No canonical-root restriction is
imposed on that target root. -/
theorem backwardRoot_horizontal (iotaH : PrimeRegularRootEmbedding p k K H)
    (e : G ≃* H) :
    RootCompatibleAlong iotaH (iotaH.alongMulEquiv e.symm) e.toMonoidHom := by
  intro V x a
  exact iotaH.alongMulEquiv_lift e.symm a.1

end Compatibility

end ModularRep.PaperProofs.OddTwoCommonRootGroupEquiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
