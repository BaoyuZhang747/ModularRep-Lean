import ModularRep.BrauerCharacterCommonRootCompatibility
import ModularRep.BrauerCharacterEquivTransport

/-!
# Agreement of the roots used for Brauer characters

For a subgroup or quotient, the smaller group uses the restriction of the
root correspondence for the larger group. Agreement is required on every
root whose order divides the prime regular exponent of the smaller group.
In particular, agreement is not inferred from equality of one character.
-/

noncomputable section

namespace ModularRep.PrimeRegularRootEmbedding

universe u v w x y

variable {p : ℕ} {k : Type u} {K : Type v}
variable [Field k] [Field K]
variable {A : Type w} {G : Type x} {H : Type y}
variable [Group A] [Finite A] [Group G] [Finite G] [Group H] [Finite H]

/-- Agreement with the first root correspondence on all roots used by the
second group. The intended applications have an injective or surjective
group homomorphism relating the two groups. -/
def AgreesOnRoots (rA : PrimeRegularRootEmbedding p k K A)
    (rG : PrimeRegularRootEmbedding p k K G) : Prop :=
  ∀ zeta : rootsOfUnity (primeRegularExponent p G) k,
    rA.lift (((zeta : kˣ) : k)) = rG.lift (((zeta : kˣ) : k))

theorem agreesOnRoots_refl (rA : PrimeRegularRootEmbedding p k K A) :
    rA.AgreesOnRoots rA := fun _ => rfl

theorem AgreesOnRoots.trans
    {rA : PrimeRegularRootEmbedding p k K A}
    {rG : PrimeRegularRootEmbedding p k K G}
    {rH : PrimeRegularRootEmbedding p k K H}
    (hAG : rA.AgreesOnRoots rG) (hGH : rG.AgreesOnRoots rH)
    (hHG : primeRegularExponent p H ∣ primeRegularExponent p G) :
    rA.AgreesOnRoots rH := by
  intro zeta
  exact (hAG (rootsOfUnityInclusion hHG zeta)).trans (hGH zeta)

theorem agreesOnRoots_of_commonRoot {n : ℕ}
    (hp : p.Prime) (e : rootsOfUnity n k ≃* rootsOfUnity n K)
    (hA : primeRegularExponent p A ∣ n)
    (hG : primeRegularExponent p G ∣ n)
    (hGA : primeRegularExponent p G ∣ primeRegularExponent p A) :
    (ofCommonRoot hp e hA).AgreesOnRoots (ofCommonRoot hp e hG) := by
  intro zeta
  calc
    (ofCommonRoot hp e hA).lift (((zeta : kˣ) : k)) =
        (ofCommonRoot hp e hA).liftRoot (rootsOfUnityInclusion hGA zeta) :=
      (ofCommonRoot hp e hA).lift_coe (rootsOfUnityInclusion hGA zeta)
    _ = (ofCommonRoot hp e hG).liftRoot zeta := rfl
    _ = (ofCommonRoot hp e hG).lift (((zeta : kˣ) : k)) :=
      ((ofCommonRoot hp e hG).lift_coe zeta).symm

end ModularRep.PrimeRegularRootEmbedding

/-
Part of the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
The results use the explicit assumptions described in the formalisation report.
-/
