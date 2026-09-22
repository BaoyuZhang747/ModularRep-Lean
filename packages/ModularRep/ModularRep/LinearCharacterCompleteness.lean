import ModularRep.LinearCharacterOrthogonality
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Completeness of central character idempotents
-/

open scoped BigOperators

namespace ModularRep

open MonoidAlgebra

/-- A subgroup contained in the centre inherits a commutative group
structure from its ambient group. -/
@[instance_reducible]
def centralSubgroupCommGroup {G : Type*} [Group G] (Z : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) : CommGroup Z := by
  apply Group.commGroupOfCenterEqTop
  rw [Subgroup.eq_top_iff']
  intro z
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hZ z.property) (w : G)

/-- A finite central subgroup has only finitely many linear characters when
the coefficient monoid has enough roots of unity. -/
@[instance_reducible]
noncomputable def centralSubgroupLinearCharacterFintype
    {k G : Type*} [CommMonoid k] [Group G] (Z : Subgroup G) [Finite Z]
    (hZ : Z ≤ Subgroup.center G)
    [HasEnoughRootsOfUnity k (Monoid.exponent Z)] : Fintype (Z →* kˣ) := by
  let _ : CommGroup Z := centralSubgroupCommGroup Z hZ
  letI : Fintype Z := Fintype.ofFinite Z
  exact Fintype.ofEquiv Z
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Z k).some.symm.toEquiv

/-- If the order of a finite group is invertible in an algebraically closed
field, the field has enough roots of unity for the exponent of the group. -/
theorem hasEnoughRootsOfUnity_of_isAlgClosed_card_invertible
    {k Z : Type*} [Field k] [Group Z] [Fintype Z] [IsAlgClosed k]
    [Invertible (Fintype.card Z : k)] :
    HasEnoughRootsOfUnity k (Monoid.exponent Z) := by
  let _ : NeZero (Monoid.exponent Z : k) := by
    constructor
    intro hexp
    obtain ⟨d, hd⟩ := Group.exponent_dvd_card (G := Z)
    have hcard : (Fintype.card Z : k) = 0 := by
      rw [hd, Nat.cast_mul, hexp, zero_mul]
    exact (Invertible.ne_zero (Fintype.card Z : k)) hcard
  infer_instance

/-- The finite type of linear characters of a finite central subgroup over
an algebraically closed field in which the subgroup order is invertible. -/
@[instance_reducible]
noncomputable def centralSubgroupLinearCharacterFintypeOfIsAlgClosed
    {k G : Type*} [Field k] [Group G] (Z : Subgroup G) [Fintype Z]
    (hZ : Z ≤ Subgroup.center G) [IsAlgClosed k]
    [Invertible (Fintype.card Z : k)] : Fintype (Z →* kˣ) := by
  let _ : HasEnoughRootsOfUnity k (Monoid.exponent Z) :=
    hasEnoughRootsOfUnity_of_isAlgClosed_card_invertible
  exact centralSubgroupLinearCharacterFintype Z hZ

/-- The inverse column of the linear character table sums to zero away from
the identity. -/
theorem sum_linearCharacters_apply_inv_of_ne_one
    {k G : Type*} [Field k] [Group G] (Z : Subgroup G) [Finite Z]
    (hZ : Z ≤ Subgroup.center G)
    [HasEnoughRootsOfUnity k (Monoid.exponent Z)]
    [Fintype (Z →* kˣ)] {z : Z} (hz : z ≠ 1) :
    ∑ nu : Z →* kˣ, (((nu z)⁻¹ : kˣ) : k) = 0 := by
  let _ : CommGroup Z := centralSubgroupCommGroup Z hZ
  let eta : (Z →* kˣ) →* kˣ :=
    (MonoidHom.eval : Z →* (Z →* kˣ) →* kˣ) z⁻¹
  have heta_apply (nu : Z →* kˣ) :
      (eta nu : k) = (((nu z)⁻¹ : kˣ) : k) := by
    simp [eta]
  simp_rw [← heta_apply]
  apply sum_linearCharacter_eq_zero_of_ne_one eta
  intro heta
  apply hz
  apply (CommGroup.forall_apply_eq_apply_iff Z (M := k)).mp
  intro nu
  have h := DFunLike.congr_fun heta nu
  change nu z⁻¹ = 1 at h
  have : nu z = 1 := by
    rw [← inv_eq_one, ← map_inv]
    exact h
  simpa using this

/-- At the identity, the inverse column of the linear character table sums
to the order of the group. -/
theorem sum_linearCharacters_apply_inv_one
    {k G : Type*} [Field k] [Group G] (Z : Subgroup G) [Fintype Z]
    (hZ : Z ≤ Subgroup.center G)
    [HasEnoughRootsOfUnity k (Monoid.exponent Z)]
    [Fintype (Z →* kˣ)] :
    ∑ nu : Z →* kˣ, (((nu (1 : Z))⁻¹ : kˣ) : k) =
      (Fintype.card Z : k) := by
  let _ : CommGroup Z := centralSubgroupCommGroup Z hZ
  simp only [map_one, inv_one, Units.val_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact congrArg (fun n : ℕ ↦ (n : k)) (by
    simpa only [Nat.card_eq_fintype_card] using
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Z k)

/-- For a finite central subgroup, the central character idempotents indexed
by all linear characters sum to one in the ambient group algebra. -/
theorem sum_centralCharacterIdempotent_eq_one
    {k G : Type*} [Field k] [Group G] (Z : Subgroup G) [Fintype Z]
    (hZ : Z ≤ Subgroup.center G)
    [Invertible (Fintype.card Z : k)]
    [HasEnoughRootsOfUnity k (Monoid.exponent Z)]
    [Fintype (Z →* kˣ)] :
    ∑ nu : Z →* kˣ, centralCharacterIdempotent Z nu = 1 := by
  classical
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  change (∑ nu : Z →* kˣ, centralCharacterIdempotent Z nu).coeff g =
    (1 : k[G]).coeff g
  rw [coeff_sum, Finsupp.finsetSum_apply]
  by_cases hg : g ∈ Z
  · let z : Z := ⟨g, hg⟩
    simp_rw [show g = (z : G) by rfl, centralCharacterIdempotent_coeff_coe]
    rw [← Finset.mul_sum]
    by_cases hz : z = 1
    · rw [show (∑ nu : Z →* kˣ, (((nu z)⁻¹ : kˣ) : k)) =
          (Fintype.card Z : k) by
        simpa [hz] using
          sum_linearCharacters_apply_inv_one (k := k) (G := G) Z hZ]
      have hzcoe : (z : G) = 1 := congrArg Subtype.val hz
      rw [hzcoe]
      simp [MonoidAlgebra.one_def]
    · rw [sum_linearCharacters_apply_inv_of_ne_one (k := k) (G := G) Z hZ hz]
      have hz1 : (z : G) ≠ 1 := by
        intro hz1
        apply hz
        apply Subtype.ext
        exact hz1
      simp [MonoidAlgebra.one_def, hz1]
  · have hg1 : g ≠ 1 := by
      intro hg1
      exact hg (hg1 ▸ Z.one_mem)
    simp_rw [centralCharacterIdempotent_coeff_of_not_mem Z _ hg]
    simp [MonoidAlgebra.one_def, hg1]

/-- The finite set of all linear characters of a finite central subgroup over
an algebraically closed field in which the subgroup order is invertible. -/
noncomputable def centralSubgroupLinearCharactersOfIsAlgClosed
    {k G : Type*} [Field k] [Group G] (Z : Subgroup G) [Fintype Z]
    (hZ : Z ≤ Subgroup.center G) [IsAlgClosed k]
    [Invertible (Fintype.card Z : k)] : Finset (Z →* kˣ) :=
  @Finset.univ _
    (centralSubgroupLinearCharacterFintypeOfIsAlgClosed (k := k) (G := G) Z hZ)

@[simp]
theorem mem_centralSubgroupLinearCharactersOfIsAlgClosed
    {k G : Type*} [Field k] [Group G] (Z : Subgroup G) [Fintype Z]
    (hZ : Z ≤ Subgroup.center G) [IsAlgClosed k]
    [Invertible (Fintype.card Z : k)] (nu : Z →* kˣ) :
    nu ∈ centralSubgroupLinearCharactersOfIsAlgClosed (k := k) Z hZ := by
  classical
  simp [centralSubgroupLinearCharactersOfIsAlgClosed]

/-- Over an algebraically closed field in which the central subgroup order
is invertible, the idempotents attached to all linear characters form a
complete family. -/
theorem sum_centralCharacterIdempotent_eq_one_of_isAlgClosed
    {k G : Type*} [Field k] [Group G] (Z : Subgroup G) [Fintype Z]
    (hZ : Z ≤ Subgroup.center G) [IsAlgClosed k]
    [Invertible (Fintype.card Z : k)] :
    (centralSubgroupLinearCharactersOfIsAlgClosed (k := k) Z hZ).sum
      (fun nu : Z →* kˣ ↦ centralCharacterIdempotent Z nu) = (1 : k[G]) := by
  let _ : Fintype (Z →* kˣ) :=
    centralSubgroupLinearCharacterFintypeOfIsAlgClosed (k := k) (G := G) Z hZ
  let _ : HasEnoughRootsOfUnity k (Monoid.exponent Z) :=
    hasEnoughRootsOfUnity_of_isAlgClosed_card_invertible
  change ∑ nu : Z →* kˣ, centralCharacterIdempotent Z nu = 1
  exact sum_centralCharacterIdempotent_eq_one Z hZ

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
