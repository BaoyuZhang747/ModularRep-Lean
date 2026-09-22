import ModularRep.PaperProofs.OddTwoCommonRootGroupEquiv

/-!
# Coherent finite scalar roots for a jointly chosen modular system

The E1 datum consists only of multiplicative tables for prime-to-p roots
and their scalar restriction coherence. Its existence, or admissibility
with respect to ONE prescribed ambient table, remains a standard modular-
system source choice. It contains no representation, character, block,
extension, relation, or desired witness.

The root of an actual finite group is computed at its prime regular
exponent. All subsequent restriction, actual-equivalence and representation
compatibility results are K. Equality outside the relevant root domain is
not claimed. This file neither enriches an arbitrary original Definition41
packet nor extends independently prescribed local tables.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCCoherentFiniteRootConvention

open ModularRep PrimeRegularRootEmbedding
open OddTwoCommonRootSelectedPairReductions OddTwoCommonRootGroupEquiv
open OddTwoActualLocalBlockSupport

universe u

/-- The usual common modular-system convention, expressed solely on actual
finite scalar root groups. No existence instance is asserted. -/
structure Convention (p : ℕ) (k K : Type u) [Field k] [Field K] where
  prime : p.Prime
  table : ∀ (m : ℕ), m.Coprime p → rootsOfUnity m k ≃* rootsOfUnity m K
  restrict_scalar : ∀ {m n : ℕ} (hm : m.Coprime p) (hn : n.Coprime p)
      (h : m ∣ n) (z : rootsOfUnity m k),
    (((table m hm z : rootsOfUnity m K) : Kˣ) : K) =
      (((table n hn (rootsOfUnityInclusion h z) : rootsOfUnity n K) : Kˣ) : K)

namespace Convention

variable {p : ℕ} {k K : Type u} [Field k] [Field K]
variable (C : Convention p k K)

/-- Scalar coherence determines the actual restricted multiplicative table. -/
theorem table_restrict {m n : ℕ} (hm : m.Coprime p) (hn : n.Coprime p)
    (h : m ∣ n) :
    C.table m hm = restrictRootsOfUnityEquiv h (C.table n hn) := by
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  apply Units.ext
  exact C.restrict_scalar hm hn h z

variable (G : Type u) [Group G] [Finite G]

include C in
theorem exponent_coprime : (primeRegularExponent p G).Coprime p :=
  (Nat.coprime_ordCompl C.prime Nat.card_pos.ne').symm

/-- The actual group root is a value of the SAME coherent finite table. -/
def rootAt : PrimeRegularRootEmbedding p k K G where
  prime := C.prime
  toMulEquiv := C.table (primeRegularExponent p G) (C.exponent_coprime G)

/-- Any actual exponent bound expresses this group root as a literal
restriction of the convention's table at that bound. -/
theorem rootAt_eq_ofCommonRoot (m : ℕ) (hm : m.Coprime p)
    (hG : primeRegularExponent p G ∣ m) :
    C.rootAt G = PrimeRegularRootEmbedding.ofCommonRoot C.prime (C.table m hm) hG := by
  apply root_eq_of_table_eq
  exact C.table_restrict (C.exponent_coprime G) hm hG

theorem rootAt_lift_coe (z : rootsOfUnity (primeRegularExponent p G) k) :
    (C.rootAt G).lift (((z : kˣ) : k)) =
      (((C.table (primeRegularExponent p G) (C.exponent_coprime G) z :
        rootsOfUnity (primeRegularExponent p G) K) : Kˣ) : K) :=
  (C.rootAt G).lift_coe z

variable {G} {H : Type u} [Group H] [Finite H]

/-- Agreement on EVERY root of the smaller actual exponent, not merely
on roots occurring in a selected representation. -/
theorem rootAt_lift_of_exponent_dvd
    (h : primeRegularExponent p G ∣ primeRegularExponent p H)
    (z : rootsOfUnity (primeRegularExponent p G) k) :
    (C.rootAt G).lift (((z : kˣ) : k)) =
      (C.rootAt H).lift (((z : kˣ) : k)) := by
  calc
    (C.rootAt G).lift (((z : kˣ) : k)) =
        (((C.table (primeRegularExponent p G) (C.exponent_coprime G) z :
          rootsOfUnity (primeRegularExponent p G) K) : Kˣ) : K) :=
      C.rootAt_lift_coe G z
    _ = (((C.table (primeRegularExponent p H) (C.exponent_coprime H)
        (rootsOfUnityInclusion h z) :
          rootsOfUnity (primeRegularExponent p H) K) : Kˣ) : K) :=
      C.restrict_scalar (C.exponent_coprime G) (C.exponent_coprime H) h z
    _ = (C.rootAt H).lift (((z : kˣ) : k)) :=
      ((C.rootAt H).lift_coe (rootsOfUnityInclusion h z)).symm

theorem rootAt_lift_of_card_dvd (h : Nat.card G ∣ Nat.card H)
    (z : rootsOfUnity (primeRegularExponent p G) k) :
    (C.rootAt G).lift (((z : kˣ) : k)) =
      (C.rootAt H).lift (((z : kˣ) : k)) :=
  C.rootAt_lift_of_exponent_dvd (exponent_dvd_of_card_dvd h) z

/-- Actual subgroup divisibility supplies the full finite-root agreement. -/
theorem rootAt_lift_subgroup (N : Subgroup G)
    (z : rootsOfUnity (primeRegularExponent p N) k) :
    (C.rootAt N).lift (((z : kˣ) : k)) =
      (C.rootAt G).lift (((z : kˣ) : k)) :=
  C.rootAt_lift_of_card_dvd (Subgroup.card_subgroup_dvd_card N) z

/-- Actual quotient divisibility supplies agreement on all quotient roots. -/
theorem rootAt_lift_quotient (N : Subgroup G) [N.Normal]
    (z : rootsOfUnity (primeRegularExponent p (G ⧸ N)) k) :
    (C.rootAt (G ⧸ N)).lift (((z : kˣ) : k)) =
      (C.rootAt G).lift (((z : kˣ) : k)) :=
  C.rootAt_lift_of_card_dvd N.card_quotient_dvd_card z

/-- The actual group-equivalence transport is the convention's target
root. This compares two computations from C, not independently given roots. -/
theorem rootAt_alongMulEquiv (e : G ≃* H) :
    (C.rootAt G).alongMulEquiv e = C.rootAt H := by
  let m := primeRegularExponent p H
  have hm : m.Coprime p := C.exponent_coprime H
  have hG : primeRegularExponent p G ∣ m :=
    (exponent_eq_of_groupEquiv (p := p) e).dvd
  have hH : primeRegularExponent p H ∣ m := dvd_refl _
  calc
    (C.rootAt G).alongMulEquiv e =
        (PrimeRegularRootEmbedding.ofCommonRoot C.prime (C.table m hm) hG).alongMulEquiv e :=
      congrArg (fun i : PrimeRegularRootEmbedding p k K G => i.alongMulEquiv e)
        (C.rootAt_eq_ofCommonRoot G m hm hG)
    _ = PrimeRegularRootEmbedding.ofCommonRoot C.prime (C.table m hm) hH :=
      ofCommonRoot_alongMulEquiv C.prime (C.table m hm) hG hH e
    _ = C.rootAt H := (C.rootAt_eq_ofCommonRoot H m hm hH).symm

section RepresentationCompatibility

variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Both group exponents divide their product. Restriction to that one
finite table supplies compatibility along ANY actual homomorphism. -/
theorem rootAt_compatible (f : H →* G) :
    RootCompatibleAlong (C.rootAt G) (C.rootAt H) f := by
  let m := primeRegularExponent p G * primeRegularExponent p H
  have hm : m.Coprime p :=
    Nat.coprime_mul_iff_left.mpr ⟨C.exponent_coprime G, C.exponent_coprime H⟩
  have hG : primeRegularExponent p G ∣ m := dvd_mul_right _ _
  have hH : primeRegularExponent p H ∣ m := dvd_mul_left _ _
  rw [C.rootAt_eq_ofCommonRoot G m hm hG, C.rootAt_eq_ofCommonRoot H m hm hH]
  exact commonRoot_compatible C.prime (C.table m hm) hG hH f

end RepresentationCompatibility
end Convention
end ModularRep.PaperProofs.TypeCCoherentFiniteRootConvention


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
