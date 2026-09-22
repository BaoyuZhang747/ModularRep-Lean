import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase

/-! The actual base and its centralizer inside an intermediate automorphism
group. The application uses the image of the upstairs character stabilizer.
The displayed subgroup inclusion is proved there from the fixed cover map. -/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionImageAmbient

open ModularRep
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase

universe u
variable {p : Nat} {k K Y : Type u}
variable [Field k] [Field K] [Group Y] [Finite Y]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable (root : PrimeRegularRootEmbedding p k K Y) (phi : IBr root)
variable (J : Subgroup (ActualAutAmbient root phi))

abbrev restrictedBase : Subgroup J := (actualBase root phi).comap J.subtype

def restrictedEmbedding (hJ : actualBase root phi ≤ J) : Y →* J :=
  (innerEmbedding root phi).codRestrict J (fun y => hJ ⟨y, rfl⟩)

theorem restrictedEmbedding_square (hJ : actualBase root phi ≤ J) :
    J.subtype.comp (restrictedEmbedding root phi J hJ) = innerEmbedding root phi := rfl

def restrictedBaseEquiv (hJ : actualBase root phi ≤ J)
    (hc : Subgroup.center Y = ⊥) : Y ≃* restrictedBase root phi J :=
  (actualBaseEquiv root phi hc).trans (Subgroup.subgroupOfEquivOfLe hJ).symm

theorem restrictedBaseEquiv_apply (hJ : actualBase root phi ≤ J)
    (hc : Subgroup.center Y = ⊥) (y : Y) :
    (restrictedBaseEquiv root phi J hJ hc y).val =
      restrictedEmbedding root phi J hJ y := rfl

theorem restrictedBase_centralizer_eq_bot (hJ : actualBase root phi ≤ J)
    (hc : Subgroup.center Y = ⊥) :
    Subgroup.centralizer (restrictedBase root phi J : Set J) = ⊥ := by
  apply bot_unique
  intro a ha
  have ha0 : a.val ∈ Subgroup.centralizer
      (actualBase root phi : Set (ActualAutAmbient root phi)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    have h := Subgroup.mem_centralizer_iff.mp ha ⟨b, hJ hb⟩ hb
    exact congrArg (fun z : J => z.val) h
  rw [actualBase_centralizer_eq_bot root phi hc] at ha0
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  exact Subgroup.mem_bot.mp ha0

theorem restricted_center_eq_bot (hJ : actualBase root phi ≤ J)
    (hc : Subgroup.center Y = ⊥) : Subgroup.center J = ⊥ := by
  apply bot_unique
  exact (Subgroup.center_le_centralizer (restrictedBase root phi J : Set J)).trans
    (restrictedBase_centralizer_eq_bot root phi J hJ hc).le

def restrictedCenterQuotientEquiv (hJ : actualBase root phi ≤ J)
    (hc : Subgroup.center Y = ⊥) : J ⧸ Subgroup.center J ≃* J :=
  (QuotientGroup.quotientMulEquivOfEq
    (restricted_center_eq_bot root phi J hJ hc)).trans QuotientGroup.quotientBot

theorem restrictedCenterQuotientEquiv_mk (hJ : actualBase root phi ≤ J)
    (hc : Subgroup.center Y = ⊥) (a : J) :
    restrictedCenterQuotientEquiv root phi J hJ hc
      (QuotientGroup.mk' (Subgroup.center J) a) = a := by
  change QuotientGroup.quotientBot
    (QuotientGroup.quotientMulEquivOfEq
      (restricted_center_eq_bot root phi J hJ hc) (QuotientGroup.mk a)) = a
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem restrictedNormalizer_eq (hJ : actualBase root phi ≤ J) (Q : Subgroup Y) :
    embeddedNormalizer (restrictedEmbedding root phi J hJ) Q =
      (embeddedNormalizer (innerEmbedding root phi) Q).comap J.subtype := by
  have hmap : (Q.map (restrictedEmbedding root phi J hJ)).map J.subtype =
      Q.map (innerEmbedding root phi) := by
    rw [Subgroup.map_map, restrictedEmbedding_square]
  have hnormal := normalizer_comap_of_injective J.subtype Subtype.val_injective
    (Q.map (restrictedEmbedding root phi J hJ))
  change (Subgroup.normalizer
    ((Q.map (restrictedEmbedding root phi J hJ)).map J.subtype :
      Set (ActualAutAmbient root phi))).comap J.subtype = _ at hnormal
  rw [hmap] at hnormal
  exact hnormal.symm

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionImageAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
