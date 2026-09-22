import ModularRep.PaperProofs.TypeBModularCommonRootBinding
import ModularRep.PaperProofs.TypeBFLZModularRootBinding
import ModularRep.BrauerCharacterCommonRootCompatibility

/-!
# Every finite group uses the same actual modular-system roots

The finite-order Hensel equivalences construct the Brauer convention for
every finite group, including arbitrary quotient and extension groups.
Their divisibility squares give common-root restriction and compatibility
along every group homomorphism. The accepted Spin and special Clifford
roots coincide with these constructions by their actual residue equations.
No character correspondence or additional root source is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBModularGroupRootBinding

open ModularRep TypeBModularCommonRootBinding

section General

universe uK uO uk uG uH uV

variable {ell : ℕ} {K : Type uK} {O : Type uO} {k : Type uk}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  (Msys : ModularSystem ell K O k)

include Msys in
/-- The actual prime regular exponent is prime to the residue characteristic. -/
theorem exponent_coprime (G : Type uG) [Group G] [Finite G] :
    (primeRegularExponent ell G).Coprime ell :=
  (Nat.coprime_ordCompl Msys.prime (Nat.card_pos (α := G)).ne').symm

/-- The root convention for any finite group is constructed from reduction. -/
def groupRoot (G : Type uG) [Group G] [Finite G] :
    PrimeRegularRootEmbedding ell k K G where
  prime := Msys.prime
  toMulEquiv := rootEquiv Msys (primeRegularExponent_pos ell G)
    (exponent_coprime Msys G)

/-- Equality of the two root-group maps determines the whole embedding. -/
theorem embedding_ext {G : Type uG} [Group G] [Finite G]
    {iota j : PrimeRegularRootEmbedding ell k K G}
    (h : iota.toMulEquiv = j.toMulEquiv) : iota = j := by
  cases iota
  cases j
  cases h
  rfl

/-- Every integral root in the group's required range has its prescribed
ordinary value after reduction and lifting. -/
theorem groupRoot_residue (G : Type uG) [Group G] [Finite G]
    (z : O) (hz : z ^ primeRegularExponent ell G = 1) :
    (groupRoot Msys G).lift (Msys.residue z) = algebraMap O K z := by
  letI : NeZero (primeRegularExponent ell G) :=
    ⟨(primeRegularExponent_pos ell G).ne'⟩
  let a : rootsOfUnity (primeRegularExponent ell G) O :=
    rootsOfUnity.mkOfPowEq z hz
  have hv :
      (((restrictRootsOfUnity Msys.residue (primeRegularExponent ell G) a) : kˣ) : k) =
        Msys.residue z := rfl
  rw [← hv, PrimeRegularRootEmbedding.lift_coe]
  exact rootEquiv_integral Msys (primeRegularExponent_pos ell G)
    (exponent_coprime Msys G) a

/-- The actual residue equation uniquely fixes the group's convention. -/
theorem eq_groupRoot_of_residue
    (G : Type uG) [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding ell k K G)
    (compatible : ∀ z : O, z ^ primeRegularExponent ell G = 1 →
      iota.lift (Msys.residue z) = algebraMap O K z) :
    iota = groupRoot Msys G := by
  apply embedding_ext
  apply rootEquiv_unique Msys (primeRegularExponent_pos ell G)
    (exponent_coprime Msys G)
  intro z
  apply rootsOfUnity.coe_injective
  have hpow : ((z : Oˣ) : O) ^ primeRegularExponent ell G = 1 :=
    (mem_rootsOfUnity' _ (z : Oˣ)).mp z.property
  have h := compatible ((z : Oˣ) : O) hpow
  have hv :
      (((restrictRootsOfUnity Msys.residue (primeRegularExponent ell G) z) : kˣ) : k) =
        Msys.residue ((z : Oˣ) : O) := rfl
  rw [← hv, PrimeRegularRootEmbedding.lift_coe] at h
  exact h

/-- Dividing group exponents use identical values on the smaller root domain. -/
theorem groupRoot_agrees_of_dvd
    (G : Type uG) [Group G] [Finite G]
    (H : Type uH) [Group H] [Finite H]
    (hdiv : primeRegularExponent ell H ∣ primeRegularExponent ell G)
    (z : rootsOfUnity (primeRegularExponent ell H) k) :
    (groupRoot Msys H).lift ((z : kˣ) : k) =
      (groupRoot Msys G).lift ((z : kˣ) : k) := by
  let included := PrimeRegularRootEmbedding.rootsOfUnityInclusion hdiv z
  have hv : ((included : kˣ) : k) = ((z : kˣ) : k) := rfl
  calc
    (groupRoot Msys H).lift ((z : kˣ) : k) =
        (groupRoot Msys H).liftRoot z := (groupRoot Msys H).lift_coe z
    _ = (groupRoot Msys G).liftRoot included :=
      rootEquiv_coherent_value Msys
        (primeRegularExponent_pos ell H) (primeRegularExponent_pos ell G)
        (exponent_coprime Msys H) (exponent_coprime Msys G) hdiv z
    _ = (groupRoot Msys G).lift ((z : kˣ) : k) := by
      rw [← hv, PrimeRegularRootEmbedding.lift_coe]

/-- The group convention equals restriction from any sufficient common
prime-to-ell order in the same modular system. -/
theorem groupRoot_eq_ofCommonRoot
    (G : Type uG) [Group G] [Finite G] {m : ℕ}
    (hm : 0 < m) (hc : m.Coprime ell)
    (hdiv : primeRegularExponent ell G ∣ m) :
    groupRoot Msys G =
      PrimeRegularRootEmbedding.ofCommonRoot Msys.prime (rootEquiv Msys hm hc) hdiv := by
  apply embedding_ext
  apply MulEquiv.ext
  intro z
  apply rootsOfUnity.coe_injective
  exact rootEquiv_coherent_value Msys (primeRegularExponent_pos ell G) hm
    (exponent_coprime Msys G) hc hdiv z

/-- One common finite exponent identifies eigenvalue lifts along every
actual group homomorphism, without a surjectivity or kernel hypothesis. -/
theorem groupRoot_compatible_along
    {G : Type uG} [Group G] [Finite G]
    {H : Type uH} [Group H] [Finite H]
    {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [CharP k ell] [IsAlgClosed k] [CharZero K]
    (rho : Representation k G V) (f : H →* G) :
    Representation.BrauerRootLiftCompatibleAlong rho
      (groupRoot Msys G) (groupRoot Msys H) f := by
  let m := primeRegularExponent ell G * primeRegularExponent ell H
  have hm : 0 < m :=
    Nat.mul_pos (primeRegularExponent_pos ell G) (primeRegularExponent_pos ell H)
  have hc : m.Coprime ell :=
    (exponent_coprime Msys G).mul_left (exponent_coprime Msys H)
  have hG : primeRegularExponent ell G ∣ m := Nat.dvd_mul_right _ _
  have hH : primeRegularExponent ell H ∣ m := Nat.dvd_mul_left _ _
  rw [groupRoot_eq_ofCommonRoot Msys G hm hc hG,
    groupRoot_eq_ofCommonRoot Msys H hm hc hH]
  exact Representation.brauerRootLiftCompatibleAlong_of_commonRoot
    rho f Msys.prime (rootEquiv Msys hm hc) hG hH

end General

section ActualTypeB

variable {n ell : ℕ} {F K O k : Type} [Field F] [Finite F]
  [Finite (TypeBCliffordCarriers.Clifford n F)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K] [CharZero K]
  (Msys : ModularSystem ell K O k)
  (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)

/-- The accepted special Clifford convention is the same Hensel convention. -/
theorem cliffordRoot_eq_groupRoot :
    TypeBFLZModularRootBinding.cliffordRoot Msys choice =
      groupRoot Msys (TypeBCliffordCarriers.SpecialClifford n F) := by
  apply eq_groupRoot_of_residue
  exact TypeBFLZModularRootBinding.cliffordRoot_residue Msys choice

/-- The accepted Spin convention uses the same actual residue roots. -/
theorem spinRoot_eq_groupRoot (N : TypeBCliffordCarriers.NormSource n F) :
    TypeBFLZModularRootBinding.spinRoot Msys choice N =
      groupRoot Msys (TypeBCliffordCarriers.Spin n F N) := by
  apply eq_groupRoot_of_residue
  exact TypeBFLZModularRootBinding.spinRoot_residue Msys choice N

end ActualTypeB

end ModularRep.PaperProofs.TypeBModularGroupRootBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
