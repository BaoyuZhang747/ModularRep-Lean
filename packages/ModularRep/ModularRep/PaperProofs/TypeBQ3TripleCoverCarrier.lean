import ModularRep.PaperProofs.TypeBExceptionalCanonicalCover
import ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The central triple cover of the same matrix Omega over ZMod 3

The existing free-presentation cover is formed directly on the actual matrix
Omega carrier used by the principal matching. Its intrinsic central subgroup
of exponent two is then factored out. The induced map has central kernel of
order three and the total group is perfect.

Malle--Testerman, Table 24.1 p.208, Theorem 24.17 p.213 and Remark 24.19 /
Table 24.3 p.214 supply the exceptional simple-group and multiplier scope.
Weibel, Construction 6.9.3, Lemma 6.9.4, Theorem 6.9.5 and Lemma 6.9.6,
pp.199--201 supply the existing free-presentation theorem; the kernel model
uses the Hopf formula in 6.8.8 / 6.9.3. Identification of those source models
with this literal matrix group and this exact kernel remains E1/U. No source
inhabitant or representation theoretic conclusion is supplied here.

The central projection and its finite kernel are the interface for the
principal lift. Maximality among prime-to-two covers is a separate subsequent
deduction and is not asserted by this file.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier

open EvenFieldFLZ318FixedTheoremGate

/-- The exact lower group of the accepted principal matching. -/
abbrev G3 : Type := TypeBRankThreePrincipalCountBinding.G (ZMod 3)

/-- The existing free construction on this same matrix carrier. -/
abbrev FullCover : Type := TypeBExceptionalCanonicalCover.Cover G3

def fullProjection : FullCover →* G3 :=
  TypeBExceptionalCanonicalCover.projection G3

/-- The exceptional source facts on this exact group and free-cover kernel.
The matrix-model and Hopf-formula identifications remain obligations of an
inhabitant. Finiteness of the matrix carrier is already available, so no
separate group-order field is required. -/
structure MatrixExceptionalSource : Prop where
  simple : IsSimpleGroup G3
  nonabelian : ¬ IsMulCommutative G3
  multiplier : Nonempty (fullProjection.ker ≃* Multiplicative (ZMod 6))

variable (source : MatrixExceptionalSource)

include source in
theorem fullProjection_kernel_card : Nat.card fullProjection.ker = 6 := by
  obtain ⟨e⟩ := source.multiplier
  rw [Nat.card_congr e.toEquiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

include source in
theorem fullCover_finite : Finite FullCover := by
  letI : Finite fullProjection.ker :=
    Nat.finite_of_card_ne_zero (by rw [fullProjection_kernel_card source]; decide)
  exact (MonoidHom.finite_iff_finite_ker_range fullProjection).mpr
    ⟨inferInstance, inferInstance⟩

variable (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

include source freeSource in
theorem fullCover_perfect : commutator FullCover = ⊤ :=
  (freeSource.applies G3
    (TypeBExceptionalCanonicalCover.perfect_of_nonabelian_simple
      source.simple source.nonabelian)).1

include source freeSource in
theorem fullProjection_universal : IsUniversalCentralExtension fullProjection :=
  (freeSource.applies G3
    (TypeBExceptionalCanonicalCover.perfect_of_nonabelian_simple
      source.simple source.nonabelian)).2

include source freeSource in
theorem fullProjection_surjective : Function.Surjective fullProjection :=
  (fullProjection_universal source freeSource).1.1

include source freeSource in
theorem fullProjection_kernel_eq_center :
    fullProjection.ker = Subgroup.center FullCover := by
  have central := (fullProjection_universal source freeSource).1.2
  apply le_antisymm central
  intro x hx
  have image : fullProjection x ∈ Subgroup.center G3 := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := fullProjection_surjective source freeSource y
    calc
      fullProjection z * fullProjection x = fullProjection (z * x) :=
        (map_mul fullProjection z x).symm
      _ = fullProjection (x * z) :=
        congrArg (fun w : FullCover => fullProjection w) (Subgroup.mem_center_iff.mp hx z)
      _ = fullProjection x * fullProjection z := map_mul fullProjection x z
  rw [TypeBExceptionalCanonicalCover.center_eq_bot_of_nonabelian_simple
    source.simple source.nonabelian] at image
  exact image

include source freeSource in
theorem fullCover_center_card : Nat.card (Subgroup.center FullCover) = 6 := by
  rw [← fullProjection_kernel_eq_center source freeSource]
  exact fullProjection_kernel_card source

include source freeSource in
theorem fullCover_center_cyclic : IsCyclic (Subgroup.center FullCover) := by
  obtain ⟨e⟩ := source.multiplier
  have cyclic : IsCyclic fullProjection.ker := e.isCyclic.mpr inferInstance
  rw [← fullProjection_kernel_eq_center source freeSource]
  exact cyclic

local instance centerCommGroup : CommGroup (Subgroup.center FullCover) :=
  { (Subgroup.center FullCover).toGroup with
    mul_comm := fun x y =>
      Subtype.ext (Subgroup.mem_center_iff.mp y.property x.val) }

/-- Two-torsion in the intrinsic commutative centre, before using sources. -/
def centerTwoKernel : Subgroup (Subgroup.center FullCover) :=
  (powMonoidHom (α := Subgroup.center FullCover) 2).ker

instance centerTwoKernel_characteristic : centerTwoKernel.Characteristic := by
  apply Subgroup.characteristic_iff_comap_le.mpr
  intro alpha x hx
  change (alpha x) ^ 2 = 1 at hx
  change x ^ 2 = 1
  apply alpha.injective
  simpa only [map_pow, map_one] using hx

/-- The intrinsic central subgroup removed from the full cover. -/
def centralTwoSubgroup : Subgroup FullCover :=
  centerTwoKernel.map (Subgroup.center FullCover).subtype

instance centralTwoSubgroup_characteristic : centralTwoSubgroup.Characteristic := by
  unfold centralTwoSubgroup
  infer_instance

instance centralTwoSubgroup_normal : centralTwoSubgroup.Normal := inferInstance

theorem centralTwoSubgroup_le_center :
    centralTwoSubgroup ≤ Subgroup.center FullCover := by
  rintro x ⟨z, _, rfl⟩
  exact z.property

def centerTwoEquiv : centerTwoKernel ≃* centralTwoSubgroup :=
  centerTwoKernel.equivMapOfInjective (Subgroup.center FullCover).subtype
    Subtype.val_injective

include source freeSource in
theorem centralTwoSubgroup_card : Nat.card centralTwoSubgroup = 2 := by
  letI : Finite FullCover := fullCover_finite source
  letI : IsCyclic (Subgroup.center FullCover) := fullCover_center_cyclic source freeSource
  rw [← Nat.card_congr centerTwoEquiv.toEquiv]
  change Nat.card
    (powMonoidHom (α := Subgroup.center FullCover) 2).ker = 2
  rw [IsCyclic.card_powMonoidHom_ker, fullCover_center_card source freeSource]
  decide

include source freeSource in
theorem centralTwoSubgroup_le_kernel : centralTwoSubgroup ≤ fullProjection.ker := by
  rw [fullProjection_kernel_eq_center source freeSource]
  exact centralTwoSubgroup_le_center

/-- The fixed triple-cover carrier, independent of source proofs. -/
abbrev X : Type := FullCover ⧸ centralTwoSubgroup

include source in
theorem finite_X : Finite X := by
  letI : Finite FullCover := fullCover_finite source
  infer_instance

def fintype_X : Fintype X := @Fintype.ofFinite _ (finite_X source)

/-- The quotient projection lands in the same matrix Omega as the matching. -/
def q : X →* G3 :=
  QuotientGroup.lift centralTwoSubgroup fullProjection
    (centralTwoSubgroup_le_kernel source freeSource)

@[simp] theorem q_mk (x : FullCover) :
    q source freeSource (QuotientGroup.mk' centralTwoSubgroup x) = fullProjection x := rfl

theorem q_surjective : Function.Surjective (q source freeSource) :=
  QuotientGroup.lift_surjective_of_surjective centralTwoSubgroup fullProjection
    (fullProjection_surjective source freeSource)
    (centralTwoSubgroup_le_kernel source freeSource)

theorem q_kernel_le_center : (q source freeSource).ker ≤ Subgroup.center X := by
  rw [q, QuotientGroup.ker_lift]
  rintro x ⟨z, hz, rfl⟩
  have central : z ∈ Subgroup.center FullCover := by
    rwa [← fullProjection_kernel_eq_center source freeSource]
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective centralTwoSubgroup y
  simpa only [map_mul] using
    congrArg (QuotientGroup.mk' centralTwoSubgroup) (Subgroup.mem_center_iff.mp central w)

theorem q_kernel_eq_center : (q source freeSource).ker = Subgroup.center X := by
  apply le_antisymm (q_kernel_le_center source freeSource)
  intro x hx
  have image : q source freeSource x ∈ Subgroup.center G3 := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := q_surjective source freeSource y
    calc
      q source freeSource z * q source freeSource x = q source freeSource (z * x) :=
        (map_mul (q source freeSource) z x).symm
      _ = q source freeSource (x * z) :=
        congrArg (fun w : X => q source freeSource w) (Subgroup.mem_center_iff.mp hx z)
      _ = q source freeSource x * q source freeSource z := map_mul (q source freeSource) x z
  rw [TypeBExceptionalCanonicalCover.center_eq_bot_of_nonabelian_simple
    source.simple source.nonabelian] at image
  exact image

include source freeSource in
theorem fullCover_card : Nat.card FullCover = Nat.card G3 * 6 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup fullProjection.ker]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective fullProjection
    (fullProjection_surjective source freeSource)).toEquiv]
  rw [fullProjection_kernel_card source]

theorem q_kernel_card : Nat.card (q source freeSource).ker = 3 := by
  have quotientCard : Nat.card FullCover = Nat.card X * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup centralTwoSubgroup,
      centralTwoSubgroup_card source freeSource]
  have projectionCard : Nat.card X = Nat.card G3 * Nat.card (q source freeSource).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (q source freeSource).ker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (q source freeSource) (q_surjective source freeSource)).toEquiv]
  have product : Nat.card G3 * 6 = Nat.card G3 * (Nat.card (q source freeSource).ker * 2) := by
    calc
      Nat.card G3 * 6 = Nat.card FullCover := (fullCover_card source freeSource).symm
      _ = Nat.card X * 2 := quotientCard
      _ = (Nat.card G3 * Nat.card (q source freeSource).ker) * 2 := by rw [projectionCard]
      _ = Nat.card G3 * (Nat.card (q source freeSource).ker * 2) := Nat.mul_assoc _ _ _
  have six : 6 = Nat.card (q source freeSource).ker * 2 :=
    Nat.mul_left_cancel (show 0 < Nat.card G3 from Nat.card_pos) product
  omega

theorem q_kernel_primeToTwo : ¬ 2 ∣ Nat.card (q source freeSource).ker := by
  rw [q_kernel_card source freeSource]
  decide

include source freeSource in
theorem center_X_card : Nat.card (Subgroup.center X) = 3 := by
  rw [← q_kernel_eq_center source freeSource]
  exact q_kernel_card source freeSource

include source freeSource in
theorem X_card : Nat.card X = Nat.card G3 * 3 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (q source freeSource).ker]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (q source freeSource) (q_surjective source freeSource)).toEquiv]
  rw [q_kernel_card source freeSource]

include source freeSource in
theorem perfect_X : commutator X = ⊤ := by
  letI : Group.IsPerfect FullCover := ⟨fullCover_perfect source freeSource⟩
  exact Group.IsPerfect.commutator_eq_top

end ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
