import ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
import ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport

/-!
# Actual tuple coordinates under a corrected automorphism

The raw-pair equality fixes beta = conj(g)*a and one conjugation of the
actual holomorph. Its restrictions identify the two actual global
stabilizers, normal bases and local raw-stabilizer intersections.
The displayed base and own-normalizer maps are proved to be those same
restrictions. Full raw-stabilizer containment is transported in both
directions, without assuming either containment.

All declarations are K. There is no relation, character-value, compatible-
root or source premise here. The two own reductions only select the actual
tuples whose group coordinates are constructed; their roots may differ.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActualTupleAutomorphismCoordinates

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates
open ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport

universe u

private theorem membership_of_image {G J : Type u} [Group G] [Group J]
    (e : G ≃* J) (A : Subgroup G) (B : Subgroup J)
    (himage : A.map e.toMonoidHom = B) (x : G) :
    e x ∈ B ↔ x ∈ A := by
  rw [← himage]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy : y = x := e.injective heq
    change y ∈ A at hy
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem image_of_membership {G J : Type u} [Group G] [Group J]
    (e : G ≃* J) (A : Subgroup G) (B : Subgroup J)
    (hmem : ∀ x : G, e x ∈ B ↔ x ∈ A) :
    A.map e.toMonoidHom = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (hmem (e.symm y)).mp (by simpa only [e.apply_symm_apply] using hy)

variable {p : ℕ} {k K H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]

local instance finiteCoordinateAut : Finite (MulAut H) :=
  Finite.of_injective (fun a : MulAut H => (a : H → H)) DFunLike.coe_injective

variable (iota : PrimeRegularRootEmbedding p k K H)
variable (psi : IBr iota) (g : H) (a : MulAut H)

/-- The whole tuple group map is the restriction of the SAME holomorph
conjugation used for both actual stabilizer images. -/
def globalEquiv :
    globalStabilizer iota (MonoidHom.id (MulAut H)) psi ≃*
      globalStabilizer iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) :=
  ((coordinateHolomorphEquiv g a).subgroupMap
    (globalStabilizer iota (MonoidHom.id (MulAut H)) psi)).trans
      (MulEquiv.subgroupCongr (globalStabilizer_coordinate_image iota g a psi))

@[simp] theorem globalEquiv_ambient
    (x : globalStabilizer iota (MonoidHom.id (MulAut H)) psi) :
    (globalEquiv iota psi g a x : CoordinateHolomorph H) =
      coordinateHolomorphEquiv g a (x : CoordinateHolomorph H) := rfl

/-- The right coordinate is conjugated by the specified automorphism. -/
theorem coordinateHolomorphEquiv_right (x : CoordinateHolomorph H) :
    (coordinateHolomorphEquiv g a x).right = a * x.right * a⁻¹ := by
  change (coordinateElement g a * x * (coordinateElement g a)⁻¹).right = _
  simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    coordinateElement_right]

theorem globalEquiv_mem_base_iff
    (x : globalStabilizer iota (MonoidHom.id (MulAut H)) psi) :
    globalEquiv iota psi g a x ∈
        baseSubgroup iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) ↔
      x ∈ baseSubgroup iota (MonoidHom.id (MulAut H)) psi := by
  change (coordinateHolomorphEquiv g a x.1).right = 1 ↔ x.1.right = 1
  rw [coordinateHolomorphEquiv_right]
  constructor
  · intro hx
    have h := congrArg (fun y : MulAut H => a⁻¹ * y * a) hx
    simpa [mul_assoc] using h
  · intro hx
    simp only [hx, mul_one, mul_inv_cancel]

/-- Exact image of the actual right-projection kernel. -/
theorem globalEquiv_map_base :
    (baseSubgroup iota (MonoidHom.id (MulAut H)) psi).map
        (globalEquiv iota psi g a).toMonoidHom =
      baseSubgroup iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) :=
  image_of_membership _ _ _ (globalEquiv_mem_base_iff iota psi g a)

variable (W V : CharacterWeight p K H)
variable (hpair : W.rightTwist (coordinateAutomorphism g a)⁻¹ = V)

include hpair in
theorem raw_membership_iff (x : CoordinateHolomorph H) :
    coordinateHolomorphEquiv g a x ∈ rawStabilizer (MonoidHom.id (MulAut H)) V ↔
      x ∈ rawStabilizer (MonoidHom.id (MulAut H)) W :=
  membership_of_image _ _ _ (rawStabilizer_coordinate_image W V g a hpair) x

theorem global_membership_iff (x : CoordinateHolomorph H) :
    coordinateHolomorphEquiv g a x ∈
        globalStabilizer iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) ↔
      x ∈ globalStabilizer iota (MonoidHom.id (MulAut H)) psi :=
  membership_of_image _ _ _ (globalStabilizer_coordinate_image iota g a psi) x

include hpair in
theorem globalEquiv_mem_local_iff
    (x : globalStabilizer iota (MonoidHom.id (MulAut H)) psi) :
    globalEquiv iota psi g a x ∈
        localSubgroup iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) V ↔
      x ∈ localSubgroup iota (MonoidHom.id (MulAut H)) psi W :=
  raw_membership_iff g a W V hpair x.1

include hpair in
/-- The local subgroup is the actual raw-stabilizer intersection, even
when the full raw stabilizer is not contained in the global stabilizer. -/
theorem globalEquiv_map_local :
    (localSubgroup iota (MonoidHom.id (MulAut H)) psi W).map
        (globalEquiv iota psi g a).toMonoidHom =
      localSubgroup iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) V :=
  image_of_membership _ _ _ (globalEquiv_mem_local_iff iota psi g a W V hpair)

include g hpair in
/-- Neither full raw-stabilizer containment is a premise. -/
theorem fullRawContainment_iff :
    (rawStabilizer (MonoidHom.id (MulAut H)) W ≤
      globalStabilizer iota (MonoidHom.id (MulAut H)) psi) ↔
    (rawStabilizer (MonoidHom.id (MulAut H)) V ≤
      globalStabilizer iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi)) := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := (coordinateHolomorphEquiv g a).surjective y
    exact (global_membership_iff iota psi g a x).mpr
      (h ((raw_membership_iff g a W V hpair x).mp hy))
  · intro h x hx
    exact (global_membership_iff iota psi g a x).mp
      (h ((raw_membership_iff g a W V hpair x).mpr hx))

/-- Displayed map on the actual base: beta in the original H coordinates. -/
def displayedBaseEquiv :
    baseSubgroup iota (MonoidHom.id (MulAut H)) psi ≃*
      baseSubgroup iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) :=
  ((OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut H)) psi).symm.trans
    (coordinateAutomorphism g a)).trans
      (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut H))
        (MulOpposite.op a⁻¹ • psi))

/-- The displayed base map commutes with the actual whole-group map. -/
theorem displayedBaseEquiv_square
    (x : baseSubgroup iota (MonoidHom.id (MulAut H)) psi) :
    (displayedBaseEquiv iota psi g a x :
      globalStabilizer iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi)) =
      globalEquiv iota psi g a (x : globalStabilizer iota (MonoidHom.id (MulAut H)) psi) := by
  obtain ⟨h, rfl⟩ :=
    (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut H)) psi).surjective x
  apply Subtype.ext
  simp only [displayedBaseEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    OddTwoActualStabilizerTriple.baseEquiv_ambient, globalEquiv_ambient,
    coordinateHolomorphEquiv_inl, coordinateAutomorphism_apply]

/-- Displayed map on the intersection, using the computed OWN normalizer
equivalence from the exact raw-pair equality. -/
def displayedIntersectionEquiv :
    ↥(baseSubgroup iota (MonoidHom.id (MulAut H)) psi ⊓
      localSubgroup iota (MonoidHom.id (MulAut H)) psi W) ≃*
    ↥(baseSubgroup iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) ⊓
      localSubgroup iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) V) :=
  ((normalizerEquivIntersection iota (MonoidHom.id (MulAut H)) psi W).symm.trans
    (ownNormalizerEquiv W V (coordinateAutomorphism g a) hpair)).trans
      (normalizerEquivIntersection iota (MonoidHom.id (MulAut H))
        (MulOpposite.op a⁻¹ • psi) V)

/-- The displayed OWN normalizer map has the same actual ambient square. -/
theorem displayedIntersectionEquiv_square
    (x : ↥(baseSubgroup iota (MonoidHom.id (MulAut H)) psi ⊓
      localSubgroup iota (MonoidHom.id (MulAut H)) psi W)) :
    (displayedIntersectionEquiv iota psi g a W V hpair x :
      globalStabilizer iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi)) =
      globalEquiv iota psi g a (x : globalStabilizer iota (MonoidHom.id (MulAut H)) psi) := by
  obtain ⟨h, rfl⟩ :=
    (normalizerEquivIntersection iota (MonoidHom.id (MulAut H)) psi W).surjective x
  apply Subtype.ext
  simp only [displayedIntersectionEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    normalizerEquivIntersection_ambient, globalEquiv_ambient,
    coordinateHolomorphEquiv_inl, ownNormalizerEquiv_coe, coordinateAutomorphism_apply]

variable (R : OwnNormalizerReduction (k := k) W)
variable (R' : OwnNormalizerReduction (k := k) V)

/-- The group part of the ACTUAL two tuples, with no root or character
compatibility inferred from these coordinates. -/
def groupCoordinates :
    GroupCoordinates
      (arguments iota (MonoidHom.id (MulAut H)) psi W R)
      (arguments iota (MonoidHom.id (MulAut H)) (MulOpposite.op a⁻¹ • psi) V R') where
  ambient := globalEquiv iota psi g a
  map_base := globalEquiv_map_base iota psi g a
  map_local := globalEquiv_map_local iota psi g a W V hpair

/-- Canonical base restriction equals the computed displayed base map. -/
theorem groupCoordinates_baseEquiv :
    (groupCoordinates iota psi g a W V hpair R R').baseEquiv =
      displayedBaseEquiv iota psi g a :=
  GroupCoordinates.baseEquiv_eq_of_ambient _ _
    (displayedBaseEquiv_square iota psi g a)

/-- Canonical own-character-domain restriction equals the computed
normalizer map. Character values and roots are still separate joins. -/
theorem groupCoordinates_intersectionEquiv :
    (groupCoordinates iota psi g a W V hpair R R').intersectionEquiv =
      displayedIntersectionEquiv iota psi g a W V hpair :=
  GroupCoordinates.intersectionEquiv_eq_of_ambient _ _
    (displayedIntersectionEquiv_square iota psi g a W V hpair)

end ModularRep.PaperProofs.OddTwoActualTupleAutomorphismCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
