import ManuscriptIBAW.Library.MultiplierQuotient
import ModularRep.PaperProofs.TypeCOddPrimeConformalCriterionCarriers

/-!
# The multiplier calculation for the conformal symplectic group

The geometric assumptions below concern the actual matrix groups and the
same symplectic inclusion used by the criterion. They state the familiar
multiplier equation, its surjectivity and kernel, and the image of the
centre. The index calculation is then proved by the first isomorphism
theorem and the elementary calculation for squares in a finite field.

No assumption here concerns characters, blocks, stabilisers or the
inductive condition.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.TypeCOddPrimeConformalCriterionCarriers (SpSubgroup)

variable (n : ℕ) (F : Type) [Field F]

/-- The multiplier equation on the fixed matrix inclusion identifies the
homomorphism with the alternating form. Surjectivity, its kernel and the
image of the centre are source assumptions. -/
structure ConformalMultiplierSource where
  positiveRank : 0 < n
  multiplier : CSp n F →* Fˣ
  equation : ∀ g : CSp n F,
    (cspMatrix n F g).transpose * Matrix.J (Fin n) F * cspMatrix n F g =
      (multiplier g : F) • Matrix.J (Fin n) F
  surjective : Function.Surjective multiplier
  kernel : multiplier.ker = SpSubgroup n F
  centralImage : (Subgroup.center (CSp n F)).map multiplier = (powMonoidHom 2).range

namespace ConformalMultiplierSource

variable {n F} [Finite F]

theorem index_le_two (S : ConformalMultiplierSource n F) :
    Nat.card (CSp n F ⧸ (SpSubgroup n F ⊔ Subgroup.center (CSp n F))) ≤ 2 := by
  rw [← S.kernel]
  exact multiplier_index_le_two S.multiplier S.surjective S.centralImage

theorem index_dvd_two (S : ConformalMultiplierSource n F) :
    (SpSubgroup n F ⊔ Subgroup.center (CSp n F)).index ∣ 2 := by
  have h := S.index_le_two
  change (SpSubgroup n F ⊔ Subgroup.center (CSp n F)).index ≤ 2 at h
  have hp : 0 < (SpSubgroup n F ⊔ Subgroup.center (CSp n F)).index :=
    Nat.card_pos
  interval_cases (SpSubgroup n F ⊔ Subgroup.center (CSp n F)).index <;> norm_num

theorem index_eq_two (S : ConformalMultiplierSource n F)
    (p : ℕ) [CharP F p] (oddCharacteristic : p ≠ 2) :
    (SpSubgroup n F ⊔ Subgroup.center (CSp n F)).index = 2 := by
  change Nat.card (CSp n F ⧸ (SpSubgroup n F ⊔ Subgroup.center (CSp n F))) = 2
  rw [← S.kernel]
  exact multiplier_index_eq_two p oddCharacteristic S.multiplier S.surjective S.centralImage

end ConformalMultiplierSource

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
