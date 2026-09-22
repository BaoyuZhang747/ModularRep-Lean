import ModularRep.PaperProofs.EvenFieldConcreteTypeCFiniteModel
import ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation

/-!
# Actual simple-quotient coordinates for Type C case construction

Whole-centre quotient transport uses the actual group equivalence. The
existing Frobenius-fixed coefficient field and its proved cardinality give
the actual finite-matrix coordinates over any field of the same order.
The centreless ambient identity cover is then identified with literal PSp.

For a two-element field the same constructions identify its projective
matrix group with the existing ZMod 2 model. Composing an existing covering
projection changes only its simple-target coordinates; its total group is
unchanged. In particular this does not replace the odd-prime double cover
of Sp6(2) by the centreless matrix group.

There are no new source records, roots, character maps, block conditions or
FamilyWitness transports. The existing source identification remains the
same one used to construct the ambient identity cover.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCActualSimpleQuotientCoordinates

open OddTwoConformalProjectiveRealisation (Sp PSp spProjection)
open EvenFieldConcreteTypeC (FiniteSymplecticFixed)
open EvenFieldConcreteTypeCFiniteModel
open EvenFieldFLZFullHG EvenFieldFLZ57CentrelessGate

universe u v

section WholeCentre

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The whole centre is carried by the same group equivalence. -/
theorem center_map (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact MulEquivClass.apply_mem_center e hx
  · intro hy
    exact ⟨e.symm y, MulEquivClass.apply_mem_center e.symm hy, e.apply_symm_apply y⟩

/-- No independently chosen quotient map occurs. -/
def centerQuotientEquiv (e : G ≃* H) :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (center_map e)

@[simp] theorem centerQuotientEquiv_mk (e : G ≃* H) (g : G) :
    centerQuotientEquiv e (QuotientGroup.mk' (Subgroup.center G) g) =
      QuotientGroup.mk' (Subgroup.center H) (e g) := rfl

theorem center_eq_bot_of_equiv (e : G ≃* H)
    (hcenter : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [← center_map e, hcenter, Subgroup.map_bot]

end WholeCentre

section CoefficientFields

variable {F E : Type} [Field F] [Field E]

/-- Entrywise field transport followed by the actual whole-centre quotient. -/
def projectiveFieldEquiv (n : ℕ) (e : F ≃+* E) : PSp n F ≃* PSp n E :=
  centerQuotientEquiv (symplecticGroupRingEquiv n e)

@[simp] theorem projectiveFieldEquiv_projection (n : ℕ) (e : F ≃+* E)
    (g : Sp n F) :
    projectiveFieldEquiv n e (spProjection n F g) =
      spProjection n E (symplecticGroupRingEquiv n e g) := rfl

end CoefficientFields

section FixedPoints

variable (n a : ℕ) (ha : 0 < a) (F : Type) [Field F] [Fintype F]

/-- The finite-field equivalence is chosen only from the two actual field
cardinalities, before any representation theoretic data. -/
def fixedCoefficientFieldEquiv (hcard : Nat.card F = 2 ^ a) :
    FixedCoefficientField a ≃+* F := by
  letI : Finite (FixedCoefficientField a) := finiteFixedCoefficientField a ha
  letI : Fintype (FixedCoefficientField a) := Fintype.ofFinite _
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    natCard_FixedCoefficientField a ha, hcard]

/-- The fixed-point group and the matrix group use the existing entrywise
constructions; equality of group orders is not used to select a group map. -/
def fixedPointsEquivSp (hcard : Nat.card F = 2 ^ a) :
    FiniteSymplecticFixed n a ≃* Sp n F :=
  (fixedCoefficientSymplecticEquivFixedPoints n a).symm.trans
    (symplecticGroupRingEquiv n (fixedCoefficientFieldEquiv a ha F hcard))

@[simp] theorem fixedPointsEquivSp_entry (hcard : Nat.card F = 2 ^ a)
    (g : FiniteSymplecticFixed n a) (i j : Fin n ⊕ Fin n) :
    ((fixedPointsEquivSp n a ha F hcard g : Sp n F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) i j =
        fixedCoefficientFieldEquiv a ha F hcard
          (fixedPointCoefficientMatrix n a g i j) := rfl

end FixedPoints

section CentrelessProjection

variable (n : ℕ) (F : Type) [Field F]

/-- The forward map stays the canonical whole-centre quotient map. -/
def projectiveEquivOfCenterless (hcenter : Subgroup.center (Sp n F) = ⊥) :
    Sp n F ≃* PSp n F :=
  MulEquiv.ofBijective (spProjection n F) ⟨by
    apply (MonoidHom.ker_eq_bot_iff (spProjection n F)).mp
    change (QuotientGroup.mk' (Subgroup.center (Sp n F))).ker = ⊥
    rw [QuotientGroup.ker_mk', hcenter], QuotientGroup.mk'_surjective _⟩

@[simp] theorem projectiveEquivOfCenterless_apply
    (hcenter : Subgroup.center (Sp n F) = ⊥) (g : Sp n F) :
    projectiveEquivOfCenterless n F hcenter g = spProjection n F g := rfl

end CentrelessProjection

section AmbientIdentityCover

variable {ell n a : ℕ} (ha : 0 < a)
variable (scope : FLZFullHGUniverse 2 ell)
variable (coverage : FullHGDefinition35Coverage scope)
variable (model : CentrelessTypeCAmbientModel (r := n) (a := a) scope)
variable (frobenius : AmbientFrobeniusFieldMatch scope model)
variable (F : Type) [Field F] [Fintype F]
variable (hcard : Nat.card F = frobenius.sourceFieldSize)

/-- The sole ambient family is mapped through its actual fixed-point
presentation and the actual coefficient field coordinates. -/
def familySpEquiv : (AmbientFamily scope coverage).H ≃* Sp n F :=
  (familyToConcrete scope coverage model).trans
    (fixedPointsEquivSp n a ha F
      (hcard.trans frobenius.sourceFieldSize_eq_two_pow))

variable (identification : CentrelessTypeCSourceIdentification scope coverage model frobenius)

/-- Its domain is exactly the simple group of the SAME canonical identity
cover. The only structural fact consumed here is its existing centrelessness. -/
def identityCoverSimpleEquiv :
    identification.identityEllPrimeCover.S ≃* PSp n F :=
  (familySpEquiv ha scope coverage model frobenius F hcard).trans
    (projectiveEquivOfCenterless n F
      (center_eq_bot_of_equiv
        (familySpEquiv ha scope coverage model frobenius F hcard)
        identification.centerless))

/-- The actual cover projection square; no character or family transport. -/
theorem identityCoverSimpleEquiv_quotient :
    (identityCoverSimpleEquiv ha scope coverage model frobenius F hcard identification).toMonoidHom.comp
        identification.identityEllPrimeCover.quotient =
      (spProjection n F).comp
        (familySpEquiv ha scope coverage model frobenius F hcard).toMonoidHom := rfl

@[simp] theorem identityCoverSimpleEquiv_apply
    (g : (AmbientFamily scope coverage).H) :
    identityCoverSimpleEquiv ha scope coverage model frobenius F hcard identification g =
      spProjection n F (familySpEquiv ha scope coverage model frobenius F hcard g) := rfl

end AmbientIdentityCover

section TwoElementField

variable (F : Type) [Field F] [Fintype F] (hcard : Nat.card F = 2)

/-- An actual two-element field is identified with the fixed ZMod 2 model. -/
def twoElementFieldEquiv : F ≃+* ZMod 2 := by
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod]
  exact hcard

/-- The simple-target coordinate for the existing Sp6(2) source. -/
def twoElementProjectiveEquiv (n : ℕ) : PSp n F ≃* PSp n (ZMod 2) :=
  projectiveFieldEquiv n (twoElementFieldEquiv F hcard)

@[simp] theorem twoElementProjectiveEquiv_projection (n : ℕ) (g : Sp n F) :
    twoElementProjectiveEquiv F hcard n (spProjection n F g) =
      spProjection n (ZMod 2) (symplecticGroupRingEquiv n
        (twoElementFieldEquiv F hcard) g) := rfl

include hcard in
theorem twoElementProjective_card (n : ℕ) :
    Nat.card (PSp n F) = Nat.card (PSp n (ZMod 2)) :=
  Nat.card_congr (twoElementProjectiveEquiv F hcard n).toEquiv

include hcard in
theorem twoElementProjective_dvd_iff (n ell : ℕ) :
    ell ∣ Nat.card (PSp n F) ↔ ell ∣ Nat.card (PSp n (ZMod 2)) := by
  rw [twoElementProjective_card F hcard n]

variable {U : Type u} [Group U]

/-- Keep the total group U and the given covering projection. Only its
simple-target coordinates change. No cover fact or witness is inferred. -/
def projectionOverTwoElementField (projection : U →* PSp 3 (ZMod 2)) :
    U →* PSp 3 F :=
  (twoElementProjectiveEquiv F hcard 3).symm.toMonoidHom.comp projection

@[simp] theorem projectionOverTwoElementField_apply
    (projection : U →* PSp 3 (ZMod 2)) (g : U) :
    projectionOverTwoElementField F hcard projection g =
      (twoElementProjectiveEquiv F hcard 3).symm (projection g) := rfl

/-- Composing back gives the exact original projection, including for the
predetermined full double-cover projection of Sp6(2). -/
theorem projectionOverTwoElementField_square
    (projection : U →* PSp 3 (ZMod 2)) :
    (twoElementProjectiveEquiv F hcard 3).toMonoidHom.comp
      (projectionOverTwoElementField F hcard projection) = projection := by
  apply MonoidHom.ext
  intro g
  exact (twoElementProjectiveEquiv F hcard 3).apply_symm_apply (projection g)

end TwoElementField

end ModularRep.PaperProofs.TypeCActualSimpleQuotientCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
