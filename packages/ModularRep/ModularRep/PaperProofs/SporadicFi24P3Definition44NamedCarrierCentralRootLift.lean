import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalRootCoherence
import Mathlib.Algebra.CharP.Invertible

/-! # Restriction and injectivity of the retained central root lift -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralRootLift

open ModularRep
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [Group X] [Fintype X]

theorem subgroupRoot_lift_coe
    (iota : PrimeRegularRootEmbedding p k K X)
    (N : Subgroup X)
    (z : rootsOfUnity (primeRegularExponent p N) k) :
    (subgroupRoot iota N).lift ((z : kˣ) : k) =
      iota.lift ((z : kˣ) : k) := by
  let hdiv : primeRegularExponent p N ∣ primeRegularExponent p X := by
    simpa only [primeRegularExponent] using
      Nat.ordCompl_dvd_ordCompl_of_dvd
        (Subgroup.card_subgroup_dvd_card N) p
  let included := PrimeRegularRootEmbedding.rootsOfUnityInclusion hdiv z
  calc
    (subgroupRoot iota N).lift ((z : kˣ) : k) =
        (subgroupRoot iota N).liftRoot z :=
      (subgroupRoot iota N).lift_coe z
    _ = iota.liftRoot included := rfl
    _ = iota.lift ((included : kˣ) : k) :=
      (iota.lift_coe included).symm
    _ = iota.lift ((z : kˣ) : k) := rfl

def centralRootLift
    (iota : PrimeRegularRootEmbedding p k K X)
    (nu : Subgroup.center X →* kˣ) :
    Subgroup.center X → K :=
  fun z => iota.lift (nu z : k)

theorem centralRootLift_injective
    [CharP k p] [Fintype (Subgroup.center X)]
    [Invertible (Fintype.card (Subgroup.center X) : k)]
    (iota : PrimeRegularRootEmbedding p k K X) :
    Function.Injective (centralRootLift iota) := by
  have hprimeTo : ¬ p ∣ Nat.card (Subgroup.center X) := by
    rw [Nat.card_eq_fintype_card]
    exact (CharP.isUnit_natCast_iff (R := k) iota.prime).mp
      (isUnit_of_invertible (Fintype.card (Subgroup.center X) : k))
  intro nu mu heq
  apply MonoidHom.ext
  intro z
  have hz : IsPrimeRegular p z :=
    IsPrimeRegular.of_coprime_natCard
      (iota.prime.coprime_iff_not_dvd.mpr hprimeTo).symm z
  have hzpow : z ^ primeRegularExponent p X = 1 := by
    apply Subtype.ext
    exact PrimeRegularElement.pow_primeRegularExponent_eq_one iota.prime
      (⟨(z : X), hz.map (Subgroup.center X).subtype⟩ :
        PrimeRegularElement (G := X) p)
  let a : rootsOfUnity (primeRegularExponent p X) k :=
    ⟨nu z, by
      change (nu z) ^ primeRegularExponent p X = 1
      rw [← map_pow, hzpow, map_one]⟩
  let b : rootsOfUnity (primeRegularExponent p X) k :=
    ⟨mu z, by
      change (mu z) ^ primeRegularExponent p X = 1
      rw [← map_pow, hzpow, map_one]⟩
  have hroot := congrFun heq z
  change iota.lift ((a : kˣ) : k) =
    iota.lift ((b : kˣ) : k) at hroot
  rw [iota.lift_coe a, iota.lift_coe b] at hroot
  have hab : iota.toMulEquiv a = iota.toMulEquiv b := by
    apply Subtype.ext
    apply Units.ext
    exact hroot
  exact congrArg Subtype.val (iota.toMulEquiv.injective hab)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralRootLift


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
