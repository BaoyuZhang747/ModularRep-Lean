import ModularRep.PaperProofs.EvenFieldFixedPointMulAut
import ModularRep.PaperProofs.EvenFieldLangInnerTwist
import ModularRep.PaperProofs.EvenFieldLeviTorus

/-!
# A unified rational-Levi witness

This module keeps the standard Levi, the Weyl representative, the Lang
element, and both Frobenius endomorphisms in one structure.  From that data
it constructs the two finite fixed-point Levis and proves that conjugation by
the Lang element identifies them.  It also constructs the restrictions of
the standard field automorphism and its inner twist and proves that the
conjugation equivalence intertwines those restrictions.

No independently chosen finite-Levi equivalence, embedding, or intertwining
identity is an input.  The later identification of the selected fixed-point
Levi with the subgroup used in the FMZ generic-weight definition remains a
separate representation theoretic input.
-/

namespace ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi

open ModularRep.PaperProofs.EvenFieldFixedPointMulAut
open ModularRep.PaperProofs.EvenFieldLangInnerTwist
open ModularRep.PaperProofs.EvenFieldLeviTorus
open ModularRep.PaperProofs.EvenFieldSourceShaped

universe u

variable {Gbar : Type u} [Group Gbar]

/-- Source-shaped E6--E7 data for one rational Levi.  The same representative
and Lang element occur in the twisted Frobenius and in the selected conjugate
Levi. -/
structure Data (F : Gbar →* Gbar) (sigmaBar : MulAut Gbar)
    (commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)) where
  standardLevi : Subgroup Gbar
  standardLevi_F_stable : standardLevi.map F = standardLevi
  standardLevi_sigma_stable :
    standardLevi.map sigmaBar.toMonoidHom = standardLevi
  representative : Gbar
  representative_normalises :
    representative ∈ Subgroup.normalizer (standardLevi : Set Gbar)
  representative_fixed : sigmaBar representative = representative
  langElement : Gbar
  langEquation : langElement⁻¹ * F langElement = representative

/-- The twisted Frobenius `F_w = Int(w) ∘ F`. -/
def Data.twistedFrobenius
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) : Gbar →* Gbar :=
  (MulAut.conj D.representative).toMonoidHom.comp F

@[simp]
theorem Data.twistedFrobenius_apply
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) (x : Gbar) :
    D.twistedFrobenius x =
      D.representative * F x * D.representative⁻¹ :=
  rfl

/-- The standard Levi is stable under the twisted Frobenius. -/
theorem Data.standardLevi_twistedFrobenius_stable
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    D.standardLevi.map D.twistedFrobenius = D.standardLevi := by
  rw [Data.twistedFrobenius, ← Subgroup.map_map,
    D.standardLevi_F_stable]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    D.representative_normalises

/-- The standard field automorphism commutes with the twisted Frobenius. -/
theorem Data.commute_twistedFrobenius
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) (x : Gbar) :
    D.twistedFrobenius (sigmaBar x) =
      sigmaBar (D.twistedFrobenius x) := by
  simp only [Data.twistedFrobenius_apply, commute, map_mul, map_inv,
    D.representative_fixed]

/-- The Lang equation in the equivalent form `F(g) = g w`. -/
theorem Data.F_langElement
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    F D.langElement = D.langElement * D.representative := by
  calc
    F D.langElement =
        D.langElement * (D.langElement⁻¹ * F D.langElement) := by simp
    _ = D.langElement * D.representative := by rw [D.langEquation]

/-- The conjugate algebraic Levi selected by the Lang element. -/
def Data.selectedLevi
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) : Subgroup Gbar :=
  conjugateSubgroup D.standardLevi D.langElement

/-- The defining Frobenius stabilises the selected conjugate Levi. -/
theorem Data.selectedLevi_F_stable
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    D.selectedLevi.map F = D.selectedLevi := by
  have hcomp :
      F.comp (MulAut.conj D.langElement).toMonoidHom =
        (MulAut.conj D.langElement).toMonoidHom.comp
          ((MulAut.conj D.representative).toMonoidHom.comp F) := by
    ext x
    change F (D.langElement * x * D.langElement⁻¹) =
      D.langElement *
        (D.representative * F x * D.representative⁻¹) *
          D.langElement⁻¹
    rw [map_mul, map_mul, map_inv, D.F_langElement]
    group
  have hw :
      D.standardLevi.map
          (MulAut.conj D.representative).toMonoidHom =
        D.standardLevi :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      D.representative_normalises
  rw [Data.selectedLevi, conjugateSubgroup, Subgroup.map_map, hcomp,
    ← Subgroup.map_map, ← Subgroup.map_map,
    D.standardLevi_F_stable, hw]

/-- The algebraic inner twist stabilises the selected conjugate Levi. -/
theorem Data.selectedLevi_innerTwisted_stable
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    D.selectedLevi.map
        (innerTwistedAut sigmaBar D.langElement).toMonoidHom =
      D.selectedLevi :=
  innerTwistedAut_stabilises_conjugateSubgroup sigmaBar D.langElement
    D.standardLevi D.standardLevi_sigma_stable

/-- The fixed points of an algebraic subgroup, viewed as a subgroup of the
ambient fixed-point group. -/
def fixedLevi (Phi : Gbar →* Gbar) (L : Subgroup Gbar) :
    Subgroup (frobeniusFixedSubgroup Phi) :=
  L.comap (frobeniusFixedSubgroup Phi).subtype

/-- The standard finite Levi `L^{F_w}`. -/
def Data.standardFiniteLevi
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    Subgroup (frobeniusFixedSubgroup D.twistedFrobenius) :=
  fixedLevi D.twistedFrobenius D.standardLevi

/-- The selected finite Levi `(g L g⁻¹)^F`. -/
def Data.selectedFiniteLevi
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    Subgroup (frobeniusFixedSubgroup F) :=
  fixedLevi F D.selectedLevi

/-- Conjugation by the Lang element identifies the two ambient fixed-point
groups. -/
def Data.fixedPointConjugationEquiv
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    frobeniusFixedSubgroup D.twistedFrobenius ≃*
      frobeniusFixedSubgroup F where
  toFun x := ⟨D.langElement * (x : Gbar) * D.langElement⁻¹, by
    change F (D.langElement * (x : Gbar) * D.langElement⁻¹) =
      D.langElement * (x : Gbar) * D.langElement⁻¹
    have hx := x.property
    change D.representative * F (x : Gbar) * D.representative⁻¹ =
      (x : Gbar) at hx
    calc
      F (D.langElement * (x : Gbar) * D.langElement⁻¹) =
          F D.langElement * F (x : Gbar) * (F D.langElement)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      _ = D.langElement *
          (D.representative * F (x : Gbar) * D.representative⁻¹) *
            D.langElement⁻¹ := by
        rw [D.F_langElement]
        group
      _ = D.langElement * (x : Gbar) * D.langElement⁻¹ := by rw [hx]⟩
  invFun y := ⟨D.langElement⁻¹ * (y : Gbar) * D.langElement, by
    change D.twistedFrobenius
        (D.langElement⁻¹ * (y : Gbar) * D.langElement) =
      D.langElement⁻¹ * (y : Gbar) * D.langElement
    have hy := y.property
    change F (y : Gbar) = (y : Gbar) at hy
    calc
      D.twistedFrobenius
          (D.langElement⁻¹ * (y : Gbar) * D.langElement) =
        D.representative *
          ((F D.langElement)⁻¹ * F (y : Gbar) * F D.langElement) *
            D.representative⁻¹ := by
          rw [Data.twistedFrobenius_apply, map_mul, map_mul, map_inv]
      _ = D.langElement⁻¹ * (y : Gbar) * D.langElement := by
        rw [D.F_langElement, hy]
        group⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv y := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

@[simp]
theorem Data.fixedPointConjugationEquiv_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute)
    (x : frobeniusFixedSubgroup D.twistedFrobenius) :
    (D.fixedPointConjugationEquiv x : Gbar) =
      D.langElement * (x : Gbar) * D.langElement⁻¹ :=
  rfl

/-- Conjugation by `g` carries the standard finite Levi exactly onto the
selected finite Levi. -/
theorem Data.standardFiniteLevi_map_eq_selectedFiniteLevi
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    D.standardFiniteLevi.map D.fixedPointConjugationEquiv.toMonoidHom =
      D.selectedFiniteLevi := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change D.langElement * (x : Gbar) * D.langElement⁻¹ ∈ D.selectedLevi
    change D.langElement * (x : Gbar) * D.langElement⁻¹ ∈
      D.standardLevi.map (MulAut.conj D.langElement).toMonoidHom
    exact ⟨(x : Gbar), hx, rfl⟩
  · intro hy
    let x : frobeniusFixedSubgroup D.twistedFrobenius :=
      D.fixedPointConjugationEquiv.symm y
    have hxL : (x : Gbar) ∈ D.standardLevi := by
      change D.langElement⁻¹ * (y : Gbar) * D.langElement ∈ D.standardLevi
      change (y : Gbar) ∈
        D.standardLevi.map (MulAut.conj D.langElement).toMonoidHom at hy
      rcases hy with ⟨z, hz, hzy⟩
      have hzx : D.langElement⁻¹ * (y : Gbar) * D.langElement = z := by
        rw [← hzy]
        simp [mul_assoc]
      rw [hzx]
      exact hz
    exact ⟨x, hxL, D.fixedPointConjugationEquiv.apply_symm_apply y⟩

/-- The canonical conjugation-by-`g` equivalence
`L^{F_w} ≃ (g L g⁻¹)^F`. -/
def Data.finiteLeviEquiv
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    D.standardFiniteLevi ≃* D.selectedFiniteLevi :=
  (D.fixedPointConjugationEquiv.subgroupMap D.standardFiniteLevi).trans
    (MulEquiv.subgroupCongr
      D.standardFiniteLevi_map_eq_selectedFiniteLevi)

@[simp]
theorem Data.finiteLeviEquiv_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) (x : D.standardFiniteLevi) :
    (((D.finiteLeviEquiv x : D.selectedFiniteLevi) :
        frobeniusFixedSubgroup F) : Gbar) =
      D.langElement *
        (((x : D.standardFiniteLevi) :
          frobeniusFixedSubgroup D.twistedFrobenius) : Gbar) *
        D.langElement⁻¹ :=
  rfl

/-- The unified witness supplies the Lang data used to define the finite
field automorphism and its inner twist. -/
def Data.langData
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) :
    EvenFieldLangInnerTwist.Data F sigmaBar commute D.langElement where
  representative := D.representative
  langEquation := D.langEquation
  representative_fixed := D.representative_fixed

/-- The standard field automorphism restricts canonically to `L^{F_w}`. -/
def Data.standardFieldAut
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) : MulAut D.standardFiniteLevi where
  toFun x := ⟨⟨sigmaBar (x : Gbar), by
    change D.twistedFrobenius (sigmaBar (x : Gbar)) = sigmaBar (x : Gbar)
    rw [D.commute_twistedFrobenius]
    exact congrArg sigmaBar x.1.property⟩, by
      have hm : sigmaBar (x : Gbar) ∈
          D.standardLevi.map sigmaBar.toMonoidHom :=
        ⟨(x : Gbar), x.property, rfl⟩
      rwa [D.standardLevi_sigma_stable] at hm⟩
  invFun x := ⟨⟨sigmaBar.symm (x : Gbar), by
    calc
      D.twistedFrobenius (sigmaBar.symm (x : Gbar)) =
          sigmaBar.symm (D.twistedFrobenius (x : Gbar)) :=
        commute_symm D.twistedFrobenius sigmaBar
          D.commute_twistedFrobenius (x : Gbar)
      _ = sigmaBar.symm (x : Gbar) :=
        congrArg sigmaBar.symm x.1.property⟩, by
      change sigmaBar.symm (x : Gbar) ∈ D.standardLevi
      have hxmap : (x : Gbar) ∈
          D.standardLevi.map sigmaBar.toMonoidHom := by
        rw [D.standardLevi_sigma_stable]
        exact x.property
      rcases hxmap with ⟨z, hz, hzx⟩
      have heq : sigmaBar.symm (x : Gbar) = z := by
        apply sigmaBar.injective
        simpa using hzx.symm
      rw [heq]
      exact hz⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact sigmaBar.symm_apply_apply (x : Gbar)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact sigmaBar.apply_symm_apply (x : Gbar)
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul sigmaBar (x : Gbar) (y : Gbar)

@[simp]
theorem Data.standardFieldAut_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) (x : D.standardFiniteLevi) :
    ((((D.standardFieldAut x : D.standardFiniteLevi) :
        frobeniusFixedSubgroup D.twistedFrobenius) : Gbar)) =
      sigmaBar (x : Gbar) :=
  rfl

/-- The selected finite-Levi automorphism transported through the canonical
conjugation equivalence. -/
def Data.selectedFieldAut
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) : MulAut D.selectedFiniteLevi :=
  D.finiteLeviEquiv.symm.trans (D.standardFieldAut.trans D.finiteLeviEquiv)

/-- The finite Levi equivalence intertwines the standard and selected field
actions. -/
theorem Data.finiteLeviEquiv_intertwines
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) (x : D.standardFiniteLevi) :
    D.finiteLeviEquiv (D.standardFieldAut x) =
      D.selectedFieldAut (D.finiteLeviEquiv x) := by
  simp [Data.selectedFieldAut]

/-- The finite inner twist has the same underlying algebraic automorphism as
`innerTwistedAut sigmaBar g`. -/
@[simp]
theorem Data.langData_tau_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) (y : frobeniusFixedSubgroup F) :
    (D.langData.tau y : Gbar) =
      innerTwistedAut sigmaBar D.langElement (y : Gbar) :=
  rfl

/-- On the ambient finite fixed-point group, the transported selected action
is the inner-twisted field automorphism constructed from the same Lang
element. -/
theorem Data.selectedFieldAut_coe_eq_tau
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (D : Data F sigmaBar commute) (y : D.selectedFiniteLevi) :
    (((D.selectedFieldAut y : D.selectedFiniteLevi) :
        frobeniusFixedSubgroup F) : Gbar) =
      (D.langData.tau ((y : D.selectedFiniteLevi) :
        frobeniusFixedSubgroup F) : Gbar) := by
  let x : D.standardFiniteLevi := D.finiteLeviEquiv.symm y
  have hy : D.finiteLeviEquiv x = y := D.finiteLeviEquiv.apply_symm_apply y
  rw [← hy, ← D.finiteLeviEquiv_intertwines]
  rw [D.langData_tau_coe, D.finiteLeviEquiv_coe,
    D.standardFieldAut_coe, D.finiteLeviEquiv_coe]
  change D.langElement * sigmaBar (x : Gbar) * D.langElement⁻¹ =
    innerTwistedAut sigmaBar D.langElement
      (D.langElement * (x : Gbar) * D.langElement⁻¹)
  exact (innerTwistedAut_conjugate sigmaBar D.langElement (x : Gbar)).symm

end ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
