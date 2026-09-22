import ModularRep.BrauerCharacter
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Compatible prime regular root embeddings for subgroups

A prime regular root embedding for an ambient finite group can be reselected
so that it agrees with a prescribed embedding for a subgroup on every root
needed by the subgroup.  The proof extends an automorphism of one finite
cyclic root group to the larger root group.

The theorem does not construct an ambient root embedding from coefficient
fields alone.  It starts from a supplied ambient embedding and changes that
choice.  Accordingly, it is suitable when the ambient Brauer character is
chosen existentially, but not for preserving a separately prescribed table
convention.
-/

namespace ModularRep

noncomputable section

namespace PrimeRegularRootEmbedding

universe u v w

/-- The canonical inclusion of one group of roots of unity into another when
the first exponent divides the second. -/
def rootsOfUnityInclusion {M : Type*} [CommMonoid M]
    {n m : ℕ} (h : n ∣ m) :
    rootsOfUnity n M →* rootsOfUnity m M :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd h)

/-- Restrict an equivalence between two groups of `m`th roots of unity to
their subgroups of `n`th roots, where `n ∣ m`. -/
def restrictRootsOfUnityHom
    {k K : Type*} [Field k] [Field K] {n m : ℕ}
    (h : n ∣ m)
    (e : rootsOfUnity m k ≃* rootsOfUnity m K) :
    rootsOfUnity n k →* rootsOfUnity n K where
  toFun z :=
    ⟨(e (rootsOfUnityInclusion h z) : rootsOfUnity m K).1, by
      change ((e (rootsOfUnityInclusion h z) : rootsOfUnity m K) : Kˣ) ^ n = 1
      have hinc : rootsOfUnityInclusion h z ^ n = 1 := by
        apply Subtype.ext
        exact z.2
      have hz : e (rootsOfUnityInclusion h z) ^ n = 1 := by
        rw [← map_pow, hinc, map_one]
      exact congrArg Subtype.val hz⟩
  map_one' := by
    apply Subtype.ext
    simp [rootsOfUnityInclusion]
  map_mul' x y := by
    apply Subtype.ext
    simp [rootsOfUnityInclusion]

/-- Restriction of a multiplicative equivalence between root groups along a
divisibility of exponents. -/
def restrictRootsOfUnityEquiv
    {k K : Type*} [Field k] [Field K] {n m : ℕ}
    (h : n ∣ m)
    (e : rootsOfUnity m k ≃* rootsOfUnity m K) :
    rootsOfUnity n k ≃* rootsOfUnity n K where
  toFun := restrictRootsOfUnityHom h e
  invFun := restrictRootsOfUnityHom h e.symm
  left_inv z := by
    apply Subtype.ext
    change ((e.symm (rootsOfUnityInclusion h
      (restrictRootsOfUnityHom h e z)) : rootsOfUnity m k) : kˣ) = z
    have hmap :
        rootsOfUnityInclusion h (restrictRootsOfUnityHom h e z) =
          e (rootsOfUnityInclusion h z) := by
      apply Subtype.ext
      rfl
    rw [hmap, e.symm_apply_apply]
    rfl
  right_inv z := by
    apply Subtype.ext
    change ((e (rootsOfUnityInclusion h
      (restrictRootsOfUnityHom h e.symm z)) : rootsOfUnity m K) : Kˣ) = z
    have hmap :
        rootsOfUnityInclusion h (restrictRootsOfUnityHom h e.symm z) =
          e.symm (rootsOfUnityInclusion h z) := by
      apply Subtype.ext
      rfl
    rw [hmap, e.apply_symm_apply]
    rfl
  map_mul' := map_mul (restrictRootsOfUnityHom h e)

private theorem addAut_apply_eq_mul_unit
    {n : ℕ} (f : AddAut (ZMod n)) (x : ZMod n) :
    f x = (((ZMod.AddAutEquivUnits n f : Additive (ZMod n)ˣ).toMul :
      (ZMod n)ˣ) : ZMod n) * x := by
  rw [ZMod.AddAutEquivUnits_apply]
  change f x = f 1 * x
  rw [mul_comm, ← x.intCast_zmod_cast, ← zsmul_eq_mul,
    ← map_zsmul, zsmul_one]

private theorem mulAut_apply_eq_pow
    {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (alpha : MulAut C) (x : C) :
    alpha x = x ^ ((IsCyclic.mulAutMulEquiv C alpha :
      (ZMod (Nat.card C))ˣ) : ZMod (Nat.card C)).val := by
  let e := zmodCyclicMulEquiv (inferInstance : IsCyclic C)
  let y := e.symm x
  let beta : MulAut (Multiplicative (ZMod (Nat.card C))) :=
    (MulAut.congr e).symm alpha
  let f : AddAut (ZMod (Nat.card C)) :=
    (MulAutMultiplicative (ZMod (Nat.card C)) beta).toAdd
  let unit : (ZMod (Nat.card C))ˣ :=
    (ZMod.AddAutEquivUnits (Nat.card C) f).toMul
  rw [show x = e y by simp [y]]
  rw [← map_pow]
  apply e.symm.injective
  have hbeta : e.symm (alpha (e y)) = beta y := rfl
  rw [hbeta, e.symm_apply_apply]
  have hunit : IsCyclic.mulAutMulEquiv C alpha = unit := rfl
  rw [hunit]
  change beta y = y ^ (unit : ZMod (Nat.card C)).val
  apply_fun Multiplicative.toAdd
  change f y.toAdd = (unit : ZMod (Nat.card C)).val • y.toAdd
  rw [addAut_apply_eq_mul_unit, nsmul_eq_mul,
    ZMod.natCast_zmod_val]

/-- An automorphism of a finite cyclic group extends across an injective
homomorphism into another finite cyclic group. -/
theorem exists_mulAut_extension
    {C D : Type*} [Group C] [Group D] [Finite C] [Finite D]
    [IsCyclic C] [IsCyclic D]
    (i : C →* D) (hi : Function.Injective i) (alpha : MulAut C) :
    ∃ beta : MulAut D, ∀ x : C, beta (i x) = i (alpha x) := by
  let n := Nat.card C
  let m := Nat.card D
  have hnm : n ∣ m := Subgroup.card_dvd_of_injective i hi
  have hmpos : 0 < m := by
    simpa [m] using (Nat.card_pos : 0 < Nat.card D)
  have hm : m ≠ 0 := hmpos.ne'
  letI : NeZero m := ⟨hm⟩
  let uC : (ZMod n)ˣ := IsCyclic.mulAutMulEquiv C alpha
  obtain ⟨uD, huD⟩ := ZMod.unitsMap_surjective hnm uC
  let beta : MulAut D := (IsCyclic.mulAutMulEquiv D).symm uD
  refine ⟨beta, ?_⟩
  intro x
  rw [mulAut_apply_eq_pow beta (i x),
    mulAut_apply_eq_pow alpha x, map_pow]
  rw [show IsCyclic.mulAutMulEquiv D beta = uD by simp [beta]]
  rw [show IsCyclic.mulAutMulEquiv C alpha = uC by rfl]
  apply pow_eq_pow_of_modEq
  · apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
    calc
      (((uD : ZMod m).val : ℕ) : ZMod n) =
          ((uD : ZMod m).cast : ZMod n) := by
            rw [ZMod.cast_eq_val]
      _ = ((ZMod.unitsMap hnm uD : (ZMod n)ˣ) : ZMod n) := by
            rw [ZMod.unitsMap_val]
      _ = (uC : ZMod n) := by rw [huD]
      _ = (((uC : ZMod n).val : ℕ) : ZMod n) := by
            rw [ZMod.natCast_zmod_val]
  · rw [← map_pow]
    simpa [n] using congrArg i (pow_card_eq_one' (x := x))

/-- Starting from any ambient root embedding, choose one whose lift agrees
with the prescribed subgroup lift on every root required by the subgroup. -/
theorem exists_ambient_agreeing_on_subgroup
    {p : ℕ} {k : Type u} {K : Type v} {A : Type w}
    [Field k] [Field K] [Group A] [Finite A]
    (N : Subgroup A)
    (baseRoot : PrimeRegularRootEmbedding p k K N)
    (hAmbient : Nonempty (PrimeRegularRootEmbedding p k K A)) :
    ∃ ambientRoot : PrimeRegularRootEmbedding p k K A,
      ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
        baseRoot.lift (((zeta : kˣ) : k)) =
          ambientRoot.lift (((zeta : kˣ) : k)) := by
  obtain ⟨ambient⟩ := hAmbient

  letI : NeZero (primeRegularExponent p N) :=
    ⟨(primeRegularExponent_pos p N).ne'⟩
  letI : NeZero (primeRegularExponent p A) :=
    ⟨(primeRegularExponent_pos p A).ne'⟩

  have hExp : primeRegularExponent p N ∣ primeRegularExponent p A := by
    simpa only [primeRegularExponent] using
      Nat.ordCompl_dvd_ordCompl_of_dvd
        (Subgroup.card_subgroup_dvd_card N) p

  let hSource :
      rootsOfUnity (primeRegularExponent p N) k ≤
        rootsOfUnity (primeRegularExponent p A) k :=
    rootsOfUnity_le_of_dvd hExp
  let hTarget :
      rootsOfUnity (primeRegularExponent p N) K ≤
        rootsOfUnity (primeRegularExponent p A) K :=
    rootsOfUnity_le_of_dvd hExp

  let inclSource :
      rootsOfUnity (primeRegularExponent p N) k →*
        rootsOfUnity (primeRegularExponent p A) k :=
    Subgroup.inclusion hSource
  let inclTarget :
      rootsOfUnity (primeRegularExponent p N) K →*
        rootsOfUnity (primeRegularExponent p A) K :=
    Subgroup.inclusion hTarget

  let restrictedAmbient :=
    restrictRootsOfUnityEquiv hExp ambient.toMulEquiv

  let alpha : MulAut (rootsOfUnity (primeRegularExponent p N) k) :=
    baseRoot.toMulEquiv.trans restrictedAmbient.symm

  obtain ⟨beta, hbeta⟩ :=
    exists_mulAut_extension
      inclSource
      (Subgroup.inclusion_injective hSource)
      alpha

  let newAmbient : PrimeRegularRootEmbedding p k K A :=
    { prime := ambient.prime
      toMulEquiv := beta.trans ambient.toMulEquiv }

  have hrestrict
      (z : rootsOfUnity (primeRegularExponent p N) k) :
      inclTarget (restrictedAmbient z) =
        ambient.toMulEquiv (inclSource z) := by
    apply Subtype.ext
    rfl

  have halpha
      (z : rootsOfUnity (primeRegularExponent p N) k) :
      restrictedAmbient (alpha z) = baseRoot.toMulEquiv z := by
    simp [alpha]

  have hagree
      (z : rootsOfUnity (primeRegularExponent p N) k) :
      newAmbient.toMulEquiv (inclSource z) =
        inclTarget (baseRoot.toMulEquiv z) := by
    change
      ambient.toMulEquiv (beta (inclSource z)) =
        inclTarget (baseRoot.toMulEquiv z)
    calc
      ambient.toMulEquiv (beta (inclSource z)) =
          ambient.toMulEquiv (inclSource (alpha z)) :=
        congrArg (fun t => ambient.toMulEquiv t) (hbeta z)
      _ = inclTarget (restrictedAmbient (alpha z)) :=
        (hrestrict (alpha z)).symm
      _ = inclTarget (baseRoot.toMulEquiv z) :=
        congrArg (fun t => inclTarget t) (halpha z)

  refine ⟨newAmbient, fun z => ?_⟩
  calc
    baseRoot.lift (((z : kˣ) : k)) = baseRoot.liftRoot z :=
      baseRoot.lift_coe z
    _ = newAmbient.liftRoot (inclSource z) := by
      unfold PrimeRegularRootEmbedding.liftRoot
      change
        (((inclTarget (baseRoot.toMulEquiv z) :
            rootsOfUnity (primeRegularExponent p A) K) : Kˣ) : K) =
          (((newAmbient.toMulEquiv (inclSource z) :
            rootsOfUnity (primeRegularExponent p A) K) : Kˣ) : K)
      exact congrArg
        (fun t : rootsOfUnity (primeRegularExponent p A) K =>
          (((t : Kˣ) : K)))
        (hagree z).symm
    _ = newAmbient.lift
          ((((inclSource z :
            rootsOfUnity (primeRegularExponent p A) k) : kˣ) : k)) :=
      (newAmbient.lift_coe (inclSource z)).symm
    _ = newAmbient.lift (((z : kˣ) : k)) := rfl

end PrimeRegularRootEmbedding

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
