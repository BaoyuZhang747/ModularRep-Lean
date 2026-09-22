import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers
import ModularRep.PaperProofs.TypeBAutomorphismSource

/-!
# The same finite Clifford and Spin carriers for modular Jordan transport

The original fixed-point equivalence supplies the Levi inclusion and
transports the prescribed finite point actor. Perfectness of the same
finite norm kernel identifies Spin with the Clifford commutator subgroup,
so every transported automorphism preserves it. No additional norm-action
square, character, block correspondence or stabilizer conclusion is used.

The fixed-point source retains its defining-field, norm and descent
authentication boundary. The interpretation of the prescribed finite
actor as the manuscript field group remains with that actor's source.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeJordanCliffordCarriers

open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers

variable {p f : ℕ} {F A E : Type}
variable [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
variable {N : NormSource 3 F} {Nbar : NormSource 3 A}
variable {Frob : MulAut (SpecialClifford 3 A)}
variable (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)

/-- The already constructed finite special Clifford point equivalence. -/
abbrev ambientEquiv : SpecialClifford 3 F ≃* fixedPoints Frob.toMonoidHom :=
  finiteAmbientEquiv 3 p f F A N Nbar Frob points

/-- The actual rational paired Levi included in the original finite Clifford group. -/
def gammaEmbedding (Lbar : Subgroup (SpecialClifford 3 A)) :
    M Frob.toMonoidHom Lbar →* SpecialClifford 3 F :=
  (ambientEquiv points).symm.toMonoidHom.comp (M Frob.toMonoidHom Lbar).subtype

@[simp] theorem gammaEmbedding_point (Lbar : Subgroup (SpecialClifford 3 A))
    (x : M Frob.toMonoidHom Lbar) :
    ambientEquiv points (gammaEmbedding points Lbar x) = x.val :=
  (ambientEquiv points).apply_symm_apply x.val

@[simp] theorem gammaEmbedding_inclusion (Lbar : Subgroup (SpecialClifford 3 A))
    (x : M Frob.toMonoidHom Lbar) :
    points.inclusion (gammaEmbedding points Lbar x) = x.val.val :=
  congrArg Subtype.val (gammaEmbedding_point points Lbar x)

theorem gammaEmbedding_injective (Lbar : Subgroup (SpecialClifford 3 A)) :
    Function.Injective (gammaEmbedding points Lbar) := by
  intro x y h
  apply Subtype.ext
  exact (ambientEquiv points).symm.injective h

section FieldActor

variable [Group E]
variable (fieldPoints : E →* MulAut (fixedPoints Frob.toMonoidHom))

/-- Transport the same actor through the fixed-point equivalence. -/
def cliffordFieldAction : E →* MulAut (SpecialClifford 3 F) :=
  (MulAut.congr (ambientEquiv points).symm).toMonoidHom.comp fieldPoints

@[simp] theorem cliffordFieldAction_value (e : E) (g : SpecialClifford 3 F) :
    cliffordFieldAction points fieldPoints e g =
      (ambientEquiv points).symm (fieldPoints e (ambientEquiv points g)) := rfl

@[simp] theorem cliffordFieldAction_point (e : E) (g : SpecialClifford 3 F) :
    ambientEquiv points (cliffordFieldAction points fieldPoints e g) =
      fieldPoints e (ambientEquiv points g) :=
  (ambientEquiv points).apply_symm_apply _

@[simp] theorem cliffordFieldAction_inclusion (e : E) (g : SpecialClifford 3 F) :
    points.inclusion (cliffordFieldAction points fieldPoints e g) =
      (fieldPoints e (ambientEquiv points g)).val :=
  congrArg Subtype.val (cliffordFieldAction_point points fieldPoints e g)

variable (Lbar : Subgroup (SpecialClifford 3 A))
variable (stable : ∀ (e : E) (x : fixedPoints Frob.toMonoidHom),
  x ∈ M Frob.toMonoidHom Lbar ↔ fieldPoints e x ∈ M Frob.toMonoidHom Lbar)

/-- Restriction of the same finite point actor to its invariant paired Levi. -/
def gammaFieldAction : E →* MulAut (M Frob.toMonoidHom Lbar) where
  toFun e := {
    toFun := fun x => ⟨fieldPoints e x.val, (stable e x.val).mp x.property⟩
    invFun := fun x => ⟨(fieldPoints e).symm x.val,
      (stable e _).mpr (by
        simpa only [(fieldPoints e).apply_symm_apply] using x.property)⟩
    left_inv := fun x => Subtype.ext ((fieldPoints e).symm_apply_apply x.val)
    right_inv := fun x => Subtype.ext ((fieldPoints e).apply_symm_apply x.val)
    map_mul' := fun x y => Subtype.ext ((fieldPoints e).map_mul x.val y.val) }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change fieldPoints 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' e d := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change fieldPoints (e * d) x.val = fieldPoints e (fieldPoints d x.val)
    rw [map_mul]
    rfl

@[simp] theorem gammaFieldAction_value (e : E) (x : M Frob.toMonoidHom Lbar) :
    (gammaFieldAction fieldPoints Lbar stable e x).val = fieldPoints e x.val := rfl

/-- The finite Clifford inclusion intertwines the same restricted field action. -/
theorem gammaEmbedding_field (e : E) (x : M Frob.toMonoidHom Lbar) :
    gammaEmbedding points Lbar (gammaFieldAction fieldPoints Lbar stable e x) =
      cliffordFieldAction points fieldPoints e (gammaEmbedding points Lbar x) := by
  apply (ambientEquiv points).injective
  rw [gammaEmbedding_point, cliffordFieldAction_point, gammaEmbedding_point]
  rfl

end FieldActor

/-- The finite Spin norm kernel is characteristic by its derived-group description. -/
theorem spinSubgroup_characteristic (N : NormSource 3 F)
    (perfect : commutator (Spin 3 F N) = ⊤) :
    (SpinSubgroup 3 F N).Characteristic := by
  rw [← TypeBAutomorphismSource.derived_eq_spin N perfect, commutator_def]
  infer_instance

theorem spinSubgroup_map_of_perfect (N : NormSource 3 F)
    (perfect : commutator (Spin 3 F N) = ⊤)
    (alpha : MulAut (SpecialClifford 3 F)) :
    (SpinSubgroup 3 F N).map alpha.toMonoidHom = SpinSubgroup 3 F N := by
  letI : (SpinSubgroup 3 F N).Characteristic := spinSubgroup_characteristic N perfect
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance alpha

section SpinActor

variable [Group E]
variable (fieldPoints : E →* MulAut (fixedPoints Frob.toMonoidHom))
variable (perfect : commutator (Spin 3 F N) = ⊤)

/-- Restrict the transported point actor to the same finite Spin group. -/
def spinFieldAction : E →* MulAut (Spin 3 F N) := by
  letI : (SpinSubgroup 3 F N).Characteristic := spinSubgroup_characteristic N perfect
  exact (MulAut.characteristic (SpinSubgroup 3 F N)).comp
    (cliffordFieldAction points fieldPoints)

@[simp] theorem spinFieldAction_coe (e : E) (g : Spin 3 F N) :
    (spinFieldAction points fieldPoints perfect e g).val =
      cliffordFieldAction points fieldPoints e g.val := rfl

@[simp] theorem spinFieldAction_point (e : E) (g : Spin 3 F N) :
    ambientEquiv points (spinFieldAction points fieldPoints perfect e g).val =
      fieldPoints e (ambientEquiv points g.val) :=
  cliffordFieldAction_point points fieldPoints e g.val

@[simp] theorem spinFieldAction_inclusion (e : E) (g : Spin 3 F N) :
    points.inclusion (spinFieldAction points fieldPoints perfect e g).val =
      (fieldPoints e (ambientEquiv points g.val)).val :=
  congrArg Subtype.val (spinFieldAction_point points fieldPoints perfect e g)

/-- The same Spin fixed-point presentation retains the ambient field value. -/
theorem finiteSpinEquiv_field (e : E) (g : Spin 3 F N) :
    (finiteSpinEquiv 3 p f F A N Nbar Frob points
      (spinFieldAction points fieldPoints perfect e g)).val =
      fieldPoints e (finiteSpinEquiv 3 p f F A N Nbar Frob points g).val :=
  spinFieldAction_point points fieldPoints perfect e g

end SpinActor

section OriginalLevi

variable (Lbar : Subgroup (SpecialClifford 3 A))
variable (levi_le_spin : Lbar ≤ SpinSubgroup 3 A Nbar)

/-- The original rational Levi included in the same finite Clifford group. -/
def originalLCliffordEmbedding : L Frob.toMonoidHom Lbar →* SpecialClifford 3 F :=
  (ambientEquiv points).symm.toMonoidHom.comp (L Frob.toMonoidHom Lbar).subtype

@[simp] theorem originalLCliffordEmbedding_point (x : L Frob.toMonoidHom Lbar) :
    ambientEquiv points (originalLCliffordEmbedding points Lbar x) = x.val :=
  (ambientEquiv points).apply_symm_apply x.val

/-- Norm compatibility puts the same original L inside the original finite Spin group. -/
def originalLSpinEmbedding : L Frob.toMonoidHom Lbar →* Spin 3 F N where
  toFun x := ⟨originalLCliffordEmbedding points Lbar x, by
    apply (inclusion_spin_iff 3 p f F A N Nbar Frob points _).mp
    have hx : points.inclusion (originalLCliffordEmbedding points Lbar x) = x.val.val :=
      congrArg Subtype.val (originalLCliffordEmbedding_point points Lbar x)
    rw [hx]
    exact levi_le_spin x.property⟩
  map_one' := Subtype.ext (originalLCliffordEmbedding points Lbar).map_one
  map_mul' x y := Subtype.ext ((originalLCliffordEmbedding points Lbar).map_mul x y)

@[simp] theorem originalLSpinEmbedding_coe (x : L Frob.toMonoidHom Lbar) :
    (originalLSpinEmbedding points Lbar levi_le_spin x).val =
      originalLCliffordEmbedding points Lbar x := rfl

theorem originalLSpinEmbedding_injective :
    Function.Injective (originalLSpinEmbedding points Lbar levi_le_spin) := by
  intro x y h
  apply Subtype.ext
  exact (ambientEquiv points).symm.injective (congrArg Subtype.val h)

/-- Original L reaches Clifford through the SAME paired-Levi inclusion. -/
theorem originalLSpinEmbedding_gamma (x : L Frob.toMonoidHom Lbar) :
    (originalLSpinEmbedding points Lbar levi_le_spin x).val =
      gammaEmbedding points Lbar
        (Subgroup.inclusion (L_le_M Frob.toMonoidHom Lbar) x) := rfl

@[simp] theorem originalLSpinEmbedding_inclusion (x : L Frob.toMonoidHom Lbar) :
    points.inclusion (originalLSpinEmbedding points Lbar levi_le_spin x).val = x.val.val :=
  congrArg Subtype.val (originalLCliffordEmbedding_point points Lbar x)

end OriginalLevi

end ModularRep.PaperProofs.TypeBRankThreeJordanCliffordCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
