import ModularRep.BrauerCharacterHomPullback
import ModularRep.PrimeRegularRootEmbeddingSubgroup

/-!
# Brauer pullback from a single finite root convention

The generic construction is kernel checked relative to the displayed common
root equivalence and divisibilities; its concrete modular-system and table
identifications remain separate source obligations.

The only coefficient input is one multiplicative equivalence on a common
root group. Every smaller root convention is its literal restriction. This
does not construct the equivalence from a modular system, nor identify an
independently prescribed table convention with that restriction.
-/

noncomputable section

namespace ModularRep.PrimeRegularRootEmbedding

universe u v w

/-- Restrict one common root convention to the roots used by a finite group. -/
def ofCommonRoot
    {p n : Nat} {k : Type u} {K : Type v} {G : Type w}
    [Field k] [Field K] [Group G] [Finite G]
    (hp : p.Prime) (e : rootsOfUnity n k ≃* rootsOfUnity n K)
    (hG : primeRegularExponent p G ∣ n) :
    PrimeRegularRootEmbedding p k K G where
  prime := hp
  toMulEquiv := restrictRootsOfUnityEquiv hG e

end ModularRep.PrimeRegularRootEmbedding

namespace Representation

universe u v w x y

variable {p n : Nat} {k : Type u} {K : Type v}
variable {G : Type w} {H : Type x} {V : Type y}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- For a quotient-oriented pullback, agreement on target-group roots is
sufficient. No agreement on all source-group roots is required. -/
theorem brauerRootLiftCompatibleAlong_of_eq_on_target_roots
    (rho : Representation k G V)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaH : ModularRep.PrimeRegularRootEmbedding p k K H)
    (f : H →* G)
    (hroots :
      ∀ zeta : rootsOfUnity (ModularRep.primeRegularExponent p G) k,
        iotaH.lift (((zeta : kˣ) : k)) =
          iotaG.lift (((zeta : kˣ) : k))) :
    BrauerRootLiftCompatibleAlong rho iotaG iotaH f := by
  intro h a
  exact hroots
    (rho.charpolyRootAsRootOfUnity iotaG
      (ModularRep.PrimeRegularElement.map f h) a)

/-- Restrictions of one common root equivalence are compatible along every
homomorphism. Both root groups send each eigenvalue to the same common root.
Neither surjectivity nor a condition on the kernel order is needed here. -/
theorem brauerRootLiftCompatibleAlong_of_commonRoot
    (rho : Representation k G V) (f : H →* G)
    (hp : p.Prime) (e : rootsOfUnity n k ≃* rootsOfUnity n K)
    (hG : ModularRep.primeRegularExponent p G ∣ n)
    (hH : ModularRep.primeRegularExponent p H ∣ n) :
    BrauerRootLiftCompatibleAlong rho
      (ModularRep.PrimeRegularRootEmbedding.ofCommonRoot hp e hG)
      (ModularRep.PrimeRegularRootEmbedding.ofCommonRoot hp e hH) f := by
  intro h a
  let iotaG := ModularRep.PrimeRegularRootEmbedding.ofCommonRoot hp e hG
  let iotaH := ModularRep.PrimeRegularRootEmbedding.ofCommonRoot hp e hH
  let zH := (rho.pullback f).charpolyRootAsRootOfUnity iotaH h a
  let zG := rho.charpolyRootAsRootOfUnity iotaG
    (ModularRep.PrimeRegularElement.map f h) a
  have hz :
      ModularRep.PrimeRegularRootEmbedding.rootsOfUnityInclusion hH zH =
        ModularRep.PrimeRegularRootEmbedding.rootsOfUnityInclusion hG zG := by
    apply Subtype.ext
    apply Units.ext
    rfl
  change iotaH.lift a.1 = iotaG.lift a.1
  calc
    iotaH.lift a.1 =
        (((e
          (ModularRep.PrimeRegularRootEmbedding.rootsOfUnityInclusion hH zH) :
            rootsOfUnity n K) : Kˣ) : K) := by
      rw [(rho.pullback f).lift_charpolyRootAsRootOfUnity iotaH h a]
      rfl
    _ =
        (((e
          (ModularRep.PrimeRegularRootEmbedding.rootsOfUnityInclusion hG zG) :
            rootsOfUnity n K) : Kˣ) : K) := by
      rw [hz]
    _ = iotaG.lift a.1 := by
      rw [rho.lift_charpolyRootAsRootOfUnity iotaG
        (ModularRep.PrimeRegularElement.map f h) a]
      rfl

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
