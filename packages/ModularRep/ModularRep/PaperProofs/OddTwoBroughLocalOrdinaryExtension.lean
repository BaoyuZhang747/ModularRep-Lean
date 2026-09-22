import ModularRep.PaperProofs.OddTwoBroughExtensionGroups
import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction

/-!
# The own ordinary character on the actual inertia quotient

For either of the constructed Brough extension lanes, K identifies the
actual N_X(Q)/Q with the kernel of the outer map on the actual inertia/Q.
The generator equation fixes this equivalence. The own ordinary character
is transported along it, and conjugation fixedness follows from the SAME
raw pair's isomorphism under the inverse inertia element. Finally the
checked ordinary cyclic-character bridge supplies its actual extension.

There is no new character, fixedness, extension or source-relation input.
The only character-theoretic theorem argument is the existing precise
Isaacs cyclic-extension principle. Neither inertia group is replaced by
a whole normalizer, and no principal-membership hypothesis is used.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughExtensionGroups.Geometry

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction

universe u

variable {n : ℕ} {F K G T : Type u}
variable [Field F] [Finite F] [Field K] [CharZero K]
variable [Group G] [Finite G] [Group T]
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable (L : Geometry (C := C) G T) (W : CharacterWeight 2 K (PSp n F))

local instance groupFintype (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

/-- The own normalizer maps onto the actual kernel in inertia/Q. All
three component maps were already computed from the literal inclusions. -/
def normalizerToLocal : Subgroup.normalizer (W.subgroup : Set (PSp n F)) →*
    (L.localOuter S W).ker :=
  (MulEquiv.subgroupCongr (L.localOuter_ker S W).symm).toMonoidHom.comp
    (((QuotientGroup.mk' (L.radical S W)).subgroupMap (L.rawBase S W)).comp
      (L.rawBaseEquiv S W).toMonoidHom)

@[simp] theorem normalizerToLocal_value
    (x : Subgroup.normalizer (W.subgroup : Set (PSp n F))) :
    (L.normalizerToLocal S W x).1 =
      QuotientGroup.mk' (L.radical S W) (L.normalizerToRaw S W x) := rfl

theorem normalizerToLocal_surjective : Function.Surjective (L.normalizerToLocal S W) :=
  (MulEquiv.subgroupCongr (L.localOuter_ker S W).symm).surjective.comp
    ((MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (L.radical S W))
      (L.rawBase S W)).comp (L.rawBaseEquiv S W).surjective)

/-- The kernel is the actual own Q in its normalizer, not an arbitrary
subgroup with the same order or isomorphism type. -/
theorem normalizerToLocal_ker :
    W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set (PSp n F))) =
      (L.normalizerToLocal S W).ker := by
  ext x
  constructor
  · intro hx
    change L.normalizerToLocal S W x = 1
    apply Subtype.ext
    rw [L.normalizerToLocal_value]
    apply (QuotientGroup.eq_one_iff (L.normalizerToRaw S W x)).2
    exact ⟨⟨x.1, hx⟩, rfl⟩
  · intro hx
    change L.normalizerToLocal S W x = 1 at hx
    have hval := congrArg (fun z : (L.localOuter S W).ker => z.1) hx
    rw [L.normalizerToLocal_value] at hval
    obtain ⟨q, hq⟩ := (QuotientGroup.eq_one_iff (L.normalizerToRaw S W x)).1 hval
    have hbase : L.base x.1 = L.base q.1 :=
      congrArg (fun z : L.raw S W => z.1) hq.symm
    have hxq : x.1 = q.1 := L.base_injective hbase
    change x.1 ∈ W.subgroup
    exact hxq ▸ q.2

/-- The actual first-isomorphism-theorem equivalence, fixed by the own
normalizer map and its exact Q kernel. -/
def normalizerQuotientEquivLocal : NormalizerQuotient W.subgroup ≃* (L.localOuter S W).ker :=
  QuotientGroup.liftEquiv _ (L.normalizerToLocal_surjective S W)
    (L.normalizerToLocal_ker S W)

@[simp] theorem normalizerQuotientEquivLocal_mk
    (x : Subgroup.normalizer (W.subgroup : Set (PSp n F))) :
    L.normalizerQuotientEquivLocal S W (QuotientGroup.mk x) =
      L.normalizerToLocal S W x := rfl

/-- The local ordinary character is the OWN theta under the computed
equivalence, with no new local-character choice. -/
def localOrdinary : OrdinaryIrreducibleCharacter.Irr K (L.localOuter S W).ker :=
  OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter (L.normalizerQuotientEquivLocal S W)

@[simp] theorem localOrdinary_normalizer
    (x : Subgroup.normalizer (W.subgroup : Set (PSp n F))) :
    L.localOrdinary S W (L.normalizerToLocal S W x) =
      W.localCharacter (QuotientGroup.mk x) := by
  change W.localCharacter ((L.normalizerQuotientEquivLocal S W).symm
    (L.normalizerToLocal S W x)) = _
  rw [← L.normalizerQuotientEquivLocal_mk, MulEquiv.symm_apply_apply]

/-- Conjugation in the actual inertia/Q agrees with the automorphism
transport supplied by the inverse raw stabilizer element. Every map is
tested on the actual own normalizer generators. -/
theorem local_conjugation_argument (d : L.raw S W) (x : (L.localOuter S W).ker) :
    let hIso := L.raw_supplies_isomorphic S W d⁻¹
    let hQ := hIso.choose
    (L.normalizerQuotientEquivLocal S W).symm
        (MulAut.conjNormal (QuotientGroup.mk' (L.radical S W) d) x) =
      rightNormalizerQuotientEquiv (S.fullAut ((L.embedding (d⁻¹).1)⁻¹)) W.subgroup
        ((MulEquiv.cast (M := fun R : Subgroup (PSp n F) => NormalizerQuotient R) hQ).symm
          ((L.normalizerQuotientEquivLocal S W).symm x)) := by
  dsimp only
  let hIso := L.raw_supplies_isomorphic S W d⁻¹
  let hQ := hIso.choose
  change W.subgroup.comap (S.fullAut ((L.embedding (d⁻¹).1)⁻¹)).toMonoidHom =
    W.subgroup at hQ
  change _ = rightNormalizerQuotientEquiv _ _ ((MulEquiv.cast hQ).symm _)
  obtain ⟨a, rfl⟩ := L.normalizerToLocal_surjective S W x
  apply (L.normalizerQuotientEquivLocal S W).injective
  rw [MulEquiv.apply_symm_apply]
  rw [← L.normalizerQuotientEquivLocal_mk S W a, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, quotientCast_symm_mk, rightNormalizerQuotientEquiv_mk]
  simp only [normalizerQuotientEquivLocal_mk, normalizerToLocal_value]
  change QuotientGroup.mk' (L.radical S W)
      (d * L.normalizerToRaw S W a * d⁻¹) =
    QuotientGroup.mk' (L.radical S W)
      (L.normalizerToRaw S W
        (rightNormalizerEquiv (S.fullAut ((L.embedding (d⁻¹).1)⁻¹)) W.subgroup
          (castNormalizer hQ.symm a)))
  apply congrArg
  apply Subtype.ext
  change d.1 * L.base a.1 * d.1⁻¹ =
    L.base (S.fullAut ((L.embedding (d⁻¹).1)⁻¹) (castNormalizer hQ.symm a).1)
  rw [castNormalizer_coe]
  have hinv : (L.embedding (d⁻¹).1)⁻¹ = L.embedding d.1 := by
    change (L.embedding (d.1⁻¹))⁻¹ = L.embedding d.1
    rw [map_inv, inv_inv]
  rw [hinv]
  exact (L.base_conjugate S d.1 a.1).symm

/-- Fixedness is derived from the SAME raw pair's own local character
equality; no invariance assertion or extension is a source input. -/
theorem localOrdinary_fixed (d : L.LocalQuotient S W) (x : (L.localOuter S W).ker) :
    L.localOrdinary S W (MulAut.conjNormal d x) = L.localOrdinary S W x := by
  obtain ⟨d0, rfl⟩ := QuotientGroup.mk'_surjective (L.radical S W) d
  change W.localCharacter ((L.normalizerQuotientEquivLocal S W).symm
      (MulAut.conjNormal (QuotientGroup.mk' (L.radical S W) d0) x)) =
    W.localCharacter ((L.normalizerQuotientEquivLocal S W).symm x)
  rw [L.local_conjugation_argument S W d0 x]
  exact localCharacter_fixed_of_rightTwist_isomorphic W
    (S.fullAut ((L.embedding (d0⁻¹).1)⁻¹))
    (L.raw_supplies_isomorphic S W d0⁻¹)
    ((L.normalizerQuotientEquivLocal S W).symm x)

variable [IsAlgClosed K] [IsCyclic T]

/-- The only external character theorem is the existing precise Isaacs
cyclic-extension principle. Cyclicity and own-character fixedness are K. -/
theorem localOrdinary_extension
    (principle : Representation.CyclicExtensionPrinciple.{u, u, u} K) :
    Nonempty (OrdinaryIrreducibleCharacter.ExtensionWitness
      (L.localOuter S W).ker (L.localOrdinary S W)) :=
  OrdinaryIrreducibleCharacter.exists_extensionWitness_of_fixed_cyclic_quotient
    (L.localOuter S W).ker principle (L.localOrdinary S W)
    (L.local_outerQuotient_cyclic S W) (L.localOrdinary_fixed S W)

/-- Literal BS local endpoint: an actual ordinary irreducible character
of inertia/Q restricts on every original normalizer generator to OWN theta. -/
theorem exists_ownLocalOrdinary_extension
    (principle : Representation.CyclicExtensionPrinciple.{u, u, u} K) :
    ∃ chiHat : OrdinaryIrreducibleCharacter.Irr K (L.LocalQuotient S W),
      ∀ x : Subgroup.normalizer (W.subgroup : Set (PSp n F)),
        chiHat (QuotientGroup.mk' (L.radical S W) (L.normalizerToRaw S W x)) =
          W.localCharacter (QuotientGroup.mk x) := by
  obtain ⟨extension⟩ := L.localOrdinary_extension S W principle
  refine ⟨extension.1, ?_⟩
  intro x
  exact (extension.2 (L.normalizerToLocal S W x)).trans (L.localOrdinary_normalizer S W x)

end ModularRep.PaperProofs.OddTwoBroughExtensionGroups.Geometry


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
