import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers
import ModularRep.PaperProofs.TypeBRegularLeviOrbitLemma46Relative
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-!
# Supported rational lifts from geometric projection and central Lang

This is the finite group deduction in current Lemma 4.5. Its ambient B is
to be instantiated with the actual geometric paired Levi Mbar. Rational
elements are the literal fixedPoints of its Frobenius, and H is the
actual geometric derived subgroup inside B. The final source wrapper must
bind Q_i and its injection to the actual rational component-orbit factors.

The input decomposition is GEOMETRIC B = H Z(B), not the generally false
rational decomposition B^F = H^F Z(B)^F. The projections are the original
geometric projections onto Frobenius orbits of components. Their stored
laws are group-level projection, Frobenius, centre and conjugation laws.
They do not assert the existence of a supported rational element.

The exact central Lang equation is an external input on the literal
centre and restricted Frobenius. Its source is Geck--Malle, Theorem 1.4.8,
p. 43, specialized to the F-stable connected algebraic centre with its
Steinberg restriction; the algebraic-to-point-carrier identification and
those hypotheses must remain explicit in the source wrapper. Geometric
central decomposition is Geck--Malle, Remark 1.7.6(a), p. 85; connectedness
of the centre uses Digne--Lehrer--Michel, Lemma 1.4 proof, p. 158, together
with connectedness of the regular overgroup's centre. No numbered lemma,
character orbit, product-image surjectivity, or supported lift is sourced.

The proof corrects a projected geometric element by a central Lang lift,
proves the corrected element is rational, and computes its conjugation.
The factor groups D_i are then the literal ranges of the actual rational
conjugation actions. The existing checked supported-lift deduction gives
surjectivity onto their product. No homomorphic section of an inner
automorphism image is used.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviSupportedLift

open ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers
open ModularRep.PaperProofs.TypeBRegularLeviOrbitLemma46Relative

universe u v

section CentralCorrection

variable {B : Type*} [Group B] (F : B →* B)

/-- The exact pointwise central Lang input on the displayed centre and F.
The source-side connectedness and Steinberg scope are required before
instantiating this narrowly stated one-way consequence. -/
structure CentralLangSource : Prop where
  centre_stable : ∀ z ∈ Subgroup.center B, F z ∈ Subgroup.center B
  lang : ∀ c : Subgroup.center B,
    ∃ z : Subgroup.center B, (z : B)⁻¹ * F z = (c : B)

/-- Multiplication by a geometric central element changes no conjugation. -/
theorem conjugation_mul_central (h x : B) (z : Subgroup.center B) :
    (h * z) * x * (h * z)⁻¹ = h * x * h⁻¹ := by
  have hz := Subgroup.mem_center_iff.mp z.property x
  calc
    (h * z) * x * (h * z)⁻¹ = h * ((z : B) * x * (z : B)⁻¹) * h⁻¹ := by
      group
    _ = h * x * h⁻¹ := by
      rw [← hz]
      group

/-- Rationality of h z forces the Frobenius defect of h into the actual
geometric centre. Neither h nor z is required to be rational. -/
theorem defect_central_of_central_decomposition
    (lang : CentralLangSource F) (h : B) (z : Subgroup.center B)
    (hfixed : F (h * z) = h * z) :
    h⁻¹ * F h ∈ Subgroup.center B := by
  have heq : h⁻¹ * F h = (z : B) * (F z)⁻¹ := by
    calc
      h⁻¹ * F h = (h⁻¹ * (F h * F z)) * (F z)⁻¹ := by group
      _ = (h⁻¹ * F (h * z)) * (F z)⁻¹ := by rw [map_mul]
      _ = (h⁻¹ * (h * z)) * (F z)⁻¹ := by rw [hfixed]
      _ = (z : B) * (F z)⁻¹ := by group
  rw [heq]
  exact (Subgroup.center B).mul_mem z.property
    ((Subgroup.center B).inv_mem (lang.centre_stable z z.property))

/-- A central Frobenius defect can be cancelled by a geometric central
Lang lift. The resulting product is proved rational. -/
theorem central_correction
    (lang : CentralLangSource F) (h : B)
    (hdefect : h⁻¹ * F h ∈ Subgroup.center B) :
    ∃ z : Subgroup.center B, F (h * z) = h * z := by
  obtain ⟨z, hz⟩ := lang.lang
    ⟨(h⁻¹ * F h)⁻¹, (Subgroup.center B).inv_mem hdefect⟩
  have hFz : F z = (z : B) * (h⁻¹ * F h)⁻¹ := by
    calc
      F z = (z : B) * ((z : B)⁻¹ * F z) := by group
      _ = (z : B) * (h⁻¹ * F h)⁻¹ := by rw [hz]
  refine ⟨z, ?_⟩
  calc
    F (h * z) = F h * F z := map_mul F h z
    _ = F h * ((z : B) * (h⁻¹ * F h)⁻¹) := by rw [hFz]
    _ = (z : B) * (F h * (h⁻¹ * F h)⁻¹) := by
      rw [← mul_assoc, Subgroup.mem_center_iff.mp z.property (F h), mul_assoc]
    _ = (z : B) * h := by group
    _ = h * z := (Subgroup.mem_center_iff.mp z.property h).symm

end CentralCorrection

section SupportedLift

variable {B I : Type u} [Group B] (F : B →* B)
variable (H : Subgroup B) (hH : ∀ h ∈ H, F h ∈ H)

/-- The actual restriction of the same Frobenius to the derived subgroup. -/
def derivedFrobenius : H →* H where
  toFun h := ⟨F h, hH h h.property⟩
  map_one' := by apply Subtype.ext; exact F.map_one
  map_mul' x y := by apply Subtype.ext; exact F.map_mul x y

variable (Q : I → Type v) [∀ i, Group (Q i)]

/-- Original geometric projection data and the exact rational conjugation
binding. Q_i remains a displayed carrier parameter until the final wrapper
binds it to its rational component fixed points. The injection and rational
value equation are retained, rather than identifying an arbitrary type
with a component group by its name. -/
structure ProjectionData where
  decomposition : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z
  factorEmbedding : ∀ i, Q i →* H
  factorEmbedding_injective : ∀ i, Function.Injective (factorEmbedding i)
  factorEmbedding_rational : ∀ i (x : Q i), F (factorEmbedding i x : B) =
    (factorEmbedding i x : B)
  project : ∀ i, H →* H
  project_frobenius : ∀ i h,
    project i (derivedFrobenius F H hH h) = derivedFrobenius F H hH (project i h)
  project_centre : ∀ i (h : H), (h : B) ∈ Subgroup.center B →
    (project i h : B) ∈ Subgroup.center B
  project_selected : ∀ i (h : H) (x : Q i),
    (project i h : B) * (factorEmbedding i x : B) * (project i h : B)⁻¹ =
      (h : B) * (factorEmbedding i x : B) * (h : B)⁻¹
  project_other : ∀ i j, j ≠ i → ∀ (h : H) (x : Q j),
    (project i h : B) * (factorEmbedding j x : B) * (project i h : B)⁻¹ =
      (factorEmbedding j x : B)
  factorAction : ∀ i, fixedPoints F →* MulAut (Q i)
  factorAction_value : ∀ i (m : fixedPoints F) (x : Q i),
    (factorEmbedding i (factorAction i m x) : B) =
      (m : B) * (factorEmbedding i x : B) * (m : B)⁻¹

variable (data : ProjectionData F H hH Q)

/-- The geometric component projection preserves the central defect of
the original H-part. The Frobenius square is used before Lang correction. -/
theorem projected_defect_central
    (h : H) (hdefect : (h : B)⁻¹ * F h ∈ Subgroup.center B) (i : I) :
    (data.project i h : B)⁻¹ * F (data.project i h) ∈ Subgroup.center B := by
  have hh : ((h⁻¹ * derivedFrobenius F H hH h : H) : B) ∈ Subgroup.center B :=
    hdefect
  have hp := data.project_centre i (h⁻¹ * derivedFrobenius F H hH h) hh
  have heq : (data.project i (h⁻¹ * derivedFrobenius F H hH h) : B) =
      (data.project i h : B)⁻¹ * F (data.project i h) := by
    rw [map_mul, map_inv, data.project_frobenius]
    rfl
  rw [heq] at hp
  exact hp

/-- A supported rational lift is a deduction from central correction.
On the selected actual factor it acts as the original rational element;
on every other factor its actual conjugation action is the identity. -/
theorem rational_supported_action
    (lang : CentralLangSource F) (m : fixedPoints F) (i : I) :
    ∃ s : fixedPoints F,
      data.factorAction i s = data.factorAction i m ∧
        ∀ j, j ≠ i → data.factorAction j s = 1 := by
  obtain ⟨h, z, hm⟩ := data.decomposition (m : B)
  have hfixed : F ((h : B) * z) = (h : B) * z := by
    rw [← hm]
    exact m.property
  have hc := defect_central_of_central_decomposition F lang (h : B) z hfixed
  have hp := projected_defect_central F H hH Q data h hc i
  obtain ⟨zi, hzi⟩ := central_correction F lang (data.project i h : B) hp
  let s : fixedPoints F := ⟨(data.project i h : B) * zi, hzi⟩
  refine ⟨s, ?_, ?_⟩
  · apply MulEquiv.ext
    intro x
    apply data.factorEmbedding_injective i
    apply Subtype.ext
    rw [data.factorAction_value, data.factorAction_value]
    change ((data.project i h : B) * zi) * (data.factorEmbedding i x : B) *
      ((data.project i h : B) * zi)⁻¹ = _
    rw [conjugation_mul_central, data.project_selected, hm,
      conjugation_mul_central]
  · intro j hji
    apply MulEquiv.ext
    intro x
    change data.factorAction j s x = x
    apply data.factorEmbedding_injective j
    apply Subtype.ext
    rw [data.factorAction_value]
    change ((data.project i h : B) * zi) * (data.factorEmbedding j x : B) *
      ((data.project i h : B) * zi)⁻¹ = _
    rw [conjugation_mul_central, data.project_other i j hji]

/-- The literal image of the actual rational conjugation action on Q_i. -/
def factorImage (i : I) : Subgroup (MulAut (Q i)) :=
  (data.factorAction i).range

/-- The canonical product action map into those literal factor images. -/
def productAction : fixedPoints F →* (∀ i, factorImage F H hH Q data i) where
  toFun m i := (data.factorAction i).rangeRestrict m
  map_one' := by
    funext i
    exact (data.factorAction i).rangeRestrict.map_one
  map_mul' x y := by
    funext i
    exact (data.factorAction i).rangeRestrict.map_mul x y

@[simp]
theorem productAction_value (m : fixedPoints F) (i : I) :
    (productAction F H hH Q data m i : MulAut (Q i)) = data.factorAction i m := rfl

/-- Range membership chooses an original rational representative. The
supported representative is then constructed by the geometric Lang proof. -/
theorem supportedLift
    (lang : CentralLangSource F) (i : I) (d : factorImage F H hH Q data i) :
    ∃ s : fixedPoints F, productAction F H hH Q data s i = d ∧
      ∀ j, j ≠ i → productAction F H hH Q data s j = 1 := by
  obtain ⟨m, hm⟩ := d.property
  obtain ⟨s, hs, hother⟩ := rational_supported_action F H hH Q data lang m i
  refine ⟨s, ?_, ?_⟩
  · apply Subtype.ext
    exact hs.trans hm
  · intro j hji
    apply Subtype.ext
    exact hother j hji

/-- The manuscript's full product-image conclusion. Its source inputs are
only the original geometric laws and the exact central Lang equation. -/
theorem productAction_surjective [Finite I] (lang : CentralLangSource F) :
    Function.Surjective (productAction F H hH Q data) :=
  productActionHom_surjective_of_supported_lifts
    (fun i => factorImage F H hH Q data i) (productAction F H hH Q data)
    (supportedLift F H hH Q data lang)

end SupportedLift

end ModularRep.PaperProofs.TypeBRegularLeviSupportedLift


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
