import ModularRep.PaperProofs.EvenFieldFMZGenericPair
import ModularRep.PaperProofs.EvenFieldGenericOrbitE8
import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
import ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter
import ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Canonical normaliser transport and the FMZ identification

The unified rational-Levi witness determines both algebraic normalisers and
their finite fixed-point groups.  This module proves that conjugation by the
same Lang element identifies those normalisers and intertwines the standard
field action with its finite inner twist.

The compact downstream connection with the literal groups in the FMZ
generic-weight definition is isolated in two ambient subgroup equalities.
A source-shaped adapter below derives those equalities from a faithful torus
realisation, its inner equivariance, the centraliser and finite-Levi
semantics, and the published FMZ normaliser equality.  From the compact
identification Lean constructs all group equivalences, their compatibility
on the finite Levi, and the `RationalLeviNormalizerTransport` consumed by the
E8 adapter.
-/

namespace ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi

open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldFixedPointMulAut
open ModularRep.PaperProofs.EvenFieldFixedQuotient
open ModularRep.PaperProofs.EvenFieldGenericOrbitE8
open ModularRep.PaperProofs.EvenFieldLangInnerTwist
open ModularRep.PaperProofs.EvenFieldLeviTorus
open ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter
open ModularRep.PaperProofs.EvenFieldSourceShaped
open ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi

universe u

variable {Gbar : Type u} [Group Gbar]

/-- The algebraic normaliser of the standard Levi. -/
def Data.standardAlgebraicNormalizer
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) : Subgroup Gbar :=
  Subgroup.normalizer (U.standardLevi : Set Gbar)

/-- The algebraic normaliser of the selected conjugate Levi. -/
def Data.selectedAlgebraicNormalizer
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) : Subgroup Gbar :=
  Subgroup.normalizer (U.selectedLevi : Set Gbar)

/-- The standard finite normaliser `N_Gbar(L)^{F_w}`. -/
def Data.standardFixedNormalizer
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    Subgroup (frobeniusFixedSubgroup U.twistedFrobenius) :=
  fixedLevi U.twistedFrobenius U.standardAlgebraicNormalizer

/-- The selected finite normaliser `N_Gbar(g L g⁻¹)^F`. -/
def Data.selectedFixedNormalizer
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    Subgroup (frobeniusFixedSubgroup F) :=
  fixedLevi F U.selectedAlgebraicNormalizer

/-- Conjugation by the Lang element carries the standard algebraic
normaliser onto the selected algebraic normaliser. -/
theorem Data.standardAlgebraicNormalizer_map_eq_selected
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    U.standardAlgebraicNormalizer.map
        (MulAut.conj U.langElement).toMonoidHom =
      U.selectedAlgebraicNormalizer := by
  rw [Data.standardAlgebraicNormalizer,
    Data.selectedAlgebraicNormalizer, Data.selectedLevi,
    conjugateSubgroup]
  exact Subgroup.map_equiv_normalizer_eq U.standardLevi
    (MulAut.conj U.langElement)

/-- The fixed-point conjugation equivalence maps the standard finite
normaliser exactly onto the selected finite normaliser. -/
theorem Data.standardFixedNormalizer_map_eq_selected
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    U.standardFixedNormalizer.map
        U.fixedPointConjugationEquiv.toMonoidHom =
      U.selectedFixedNormalizer := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change U.langElement * (x : Gbar) * U.langElement⁻¹ ∈
      U.selectedAlgebraicNormalizer
    have hm : U.langElement * (x : Gbar) * U.langElement⁻¹ ∈
        U.standardAlgebraicNormalizer.map
          (MulAut.conj U.langElement).toMonoidHom :=
      ⟨(x : Gbar), hx, rfl⟩
    rwa [U.standardAlgebraicNormalizer_map_eq_selected] at hm
  · intro hy
    let x : frobeniusFixedSubgroup U.twistedFrobenius :=
      U.fixedPointConjugationEquiv.symm y
    have hxN : (x : Gbar) ∈ U.standardAlgebraicNormalizer := by
      change U.langElement⁻¹ * (y : Gbar) * U.langElement ∈
        U.standardAlgebraicNormalizer
      have hymap : (y : Gbar) ∈
          U.standardAlgebraicNormalizer.map
            (MulAut.conj U.langElement).toMonoidHom := by
        rwa [U.standardAlgebraicNormalizer_map_eq_selected]
      rcases hymap with ⟨z, hz, hzy⟩
      have hzx : U.langElement⁻¹ * (y : Gbar) * U.langElement = z := by
        rw [← hzy]
        change U.langElement⁻¹ *
          (U.langElement * z * U.langElement⁻¹) * U.langElement = z
        group
      rw [hzx]
      exact hz
    exact ⟨x, hxN, U.fixedPointConjugationEquiv.apply_symm_apply y⟩

/-- The canonical conjugation equivalence between the two finite
normalisers. -/
def Data.fixedNormalizerEquiv
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    U.standardFixedNormalizer ≃* U.selectedFixedNormalizer :=
  (U.fixedPointConjugationEquiv.subgroupMap
      U.standardFixedNormalizer).trans
    (MulEquiv.subgroupCongr U.standardFixedNormalizer_map_eq_selected)

@[simp]
theorem Data.fixedNormalizerEquiv_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) (x : U.standardFixedNormalizer) :
    (((U.fixedNormalizerEquiv x : U.selectedFixedNormalizer) :
        frobeniusFixedSubgroup F) : Gbar) =
      U.langElement * (x : Gbar) * U.langElement⁻¹ :=
  rfl

/-- The standard field automorphism stabilises the standard algebraic
normaliser. -/
theorem Data.standardAlgebraicNormalizer_sigma_stable
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    U.standardAlgebraicNormalizer.map sigmaBar.toMonoidHom =
      U.standardAlgebraicNormalizer := by
  rw [Data.standardAlgebraicNormalizer,
    Subgroup.map_equiv_normalizer_eq,
    U.standardLevi_sigma_stable]

/-- A commuting automorphism restricted to the fixed points in a stable
algebraic subgroup. -/
def fixedSubgroupAut (Phi : Gbar →* Gbar) (alpha : MulAut Gbar)
    (commutes : ∀ x : Gbar, Phi (alpha x) = alpha (Phi x))
    (L : Subgroup Gbar) (L_stable : L.map alpha.toMonoidHom = L) :
    MulAut (fixedLevi Phi L) where
  toFun x := ⟨⟨alpha (x : Gbar), by
    change Phi (alpha (x : Gbar)) = alpha (x : Gbar)
    rw [commutes]
    exact congrArg alpha x.1.property⟩, by
      have hm : alpha (x : Gbar) ∈ L.map alpha.toMonoidHom :=
        ⟨(x : Gbar), x.property, rfl⟩
      rwa [L_stable] at hm⟩
  invFun x := ⟨⟨alpha.symm (x : Gbar), by
    calc
      Phi (alpha.symm (x : Gbar)) = alpha.symm (Phi (x : Gbar)) :=
        commute_symm Phi alpha commutes (x : Gbar)
      _ = alpha.symm (x : Gbar) :=
        congrArg alpha.symm x.1.property⟩, by
      change alpha.symm (x : Gbar) ∈ L
      have hxmap : (x : Gbar) ∈ L.map alpha.toMonoidHom := by
        rw [L_stable]
        exact x.property
      rcases hxmap with ⟨z, hz, hzx⟩
      have heq : alpha.symm (x : Gbar) = z := by
        apply alpha.injective
        simpa using hzx.symm
      rw [heq]
      exact hz⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact alpha.symm_apply_apply (x : Gbar)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact alpha.apply_symm_apply (x : Gbar)
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul alpha (x : Gbar) (y : Gbar)

/-- The standard field action on the standard finite normaliser. -/
def Data.standardNormalizerFieldAut
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    MulAut U.standardFixedNormalizer :=
  fixedSubgroupAut U.twistedFrobenius sigmaBar
    U.commute_twistedFrobenius U.standardAlgebraicNormalizer
    U.standardAlgebraicNormalizer_sigma_stable

@[simp]
theorem Data.standardNormalizerFieldAut_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) (x : U.standardFixedNormalizer) :
    ((((U.standardNormalizerFieldAut x : U.standardFixedNormalizer) :
        frobeniusFixedSubgroup U.twistedFrobenius) : Gbar)) =
      sigmaBar (x : Gbar) :=
  rfl

/-- The selected normaliser action transported through conjugation by the
Lang element. -/
def Data.selectedNormalizerFieldAut
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    MulAut U.selectedFixedNormalizer :=
  U.fixedNormalizerEquiv.symm.trans
    (U.standardNormalizerFieldAut.trans U.fixedNormalizerEquiv)

/-- The normaliser equivalence intertwines the two finite field actions. -/
theorem Data.fixedNormalizerEquiv_intertwines
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) (x : U.standardFixedNormalizer) :
    U.fixedNormalizerEquiv (U.standardNormalizerFieldAut x) =
      U.selectedNormalizerFieldAut (U.fixedNormalizerEquiv x) := by
  simp [Data.selectedNormalizerFieldAut]

/-- The selected normaliser action is the restriction of the finite inner
twist defined by the same Lang element. -/
theorem Data.selectedNormalizerFieldAut_coe_eq_tau
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) (y : U.selectedFixedNormalizer) :
    (((U.selectedNormalizerFieldAut y : U.selectedFixedNormalizer) :
        frobeniusFixedSubgroup F) : Gbar) =
      (U.langData.tau ((y : U.selectedFixedNormalizer) :
        frobeniusFixedSubgroup F) : Gbar) := by
  let x : U.standardFixedNormalizer := U.fixedNormalizerEquiv.symm y
  have hy : U.fixedNormalizerEquiv x = y :=
    U.fixedNormalizerEquiv.apply_symm_apply y
  rw [← hy, ← U.fixedNormalizerEquiv_intertwines]
  rw [U.langData_tau_coe, U.fixedNormalizerEquiv_coe,
    U.standardNormalizerFieldAut_coe, U.fixedNormalizerEquiv_coe]
  exact (innerTwistedAut_conjugate sigmaBar U.langElement (x : Gbar)).symm

/-- The standard fixed normaliser is stable under the endomorphism induced
by the standard field automorphism. -/
theorem Data.standardFixedNormalizer_stable
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    ∀ x : U.standardFixedNormalizer,
      frobeniusFixedSubgroupHom U.twistedFrobenius
        sigmaBar.toMonoidHom U.commute_twistedFrobenius x ∈
          U.standardFixedNormalizer := by
  intro x
  change sigmaBar (x : Gbar) ∈ U.standardAlgebraicNormalizer
  have hm : sigmaBar (x : Gbar) ∈
      U.standardAlgebraicNormalizer.map sigmaBar.toMonoidHom :=
    ⟨(x : Gbar), x.property, rfl⟩
  rwa [U.standardAlgebraicNormalizer_sigma_stable] at hm

/-- The finite Levi inside the standard fixed normaliser is canonically the
standard finite Levi already constructed by the unified witness. -/
def Data.fixedBaseEquivStandardFiniteLevi
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute) :
    fixedBase U.twistedFrobenius U.standardFixedNormalizer U.standardLevi ≃*
      U.standardFiniteLevi where
  toFun x := ⟨(x : U.standardFixedNormalizer), x.property⟩
  invFun x := ⟨⟨(x : frobeniusFixedSubgroup U.twistedFrobenius),
    U.standardLevi.le_normalizer x.property⟩, x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem Data.fixedBaseEquivStandardFiniteLevi_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute)
    (x : fixedBase U.twistedFrobenius U.standardFixedNormalizer
      U.standardLevi) :
    (((U.fixedBaseEquivStandardFiniteLevi x : U.standardFiniteLevi) :
        frobeniusFixedSubgroup U.twistedFrobenius) : Gbar) =
      (x : Gbar) :=
  rfl

section FMZ

variable {k A Block : Type u} [Field k] [CharZero k]

/-- The minimal E5 identification between the canonical algebraic
fixed-point groups and the literal groups in the FMZ definition.  Both
claims are equalities of subgroups in the common ambient finite group. -/
structure FMZIdentification
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute)
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    (D : Definitions k (frobeniusFixedSubgroup F) A Block)
    (P : LocalPair k (frobeniusFixedSubgroup F) A) : Prop where
  normalizer_eq :
    finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1 =
      U.selectedFixedNormalizer
  levi_image_eq :
    (D.levi P.1).map
        (finiteNormalizer (H := frobeniusFixedSubgroup F)
          (A := A) P.1).subtype =
      U.selectedFiniteLevi

/-- Source-shaped semantics behind the two E5 subgroup equalities.

The explicit parameter `realise` interprets the abstract FMZ torus label as
an algebraic subgroup.  It is an index of the structure rather than stored
data, so a caller that already has a source realisation must use that very
map.  The explicit parameter `realise_injective` supplies its injectivity.
The field `realise_inner` says that the inner action on labels is literal
algebraic conjugation.  The remaining two fields identify the selected
rational Levi with the centraliser of the realised torus and interpret the
abstract finite Levi in `Definitions` as the fixed points of that centraliser.

The published FMZ equality between the normalisers of the torus and its
centraliser is deliberately not a field of this structure.  It is supplied
separately to `toFMZIdentification` below. -/
structure FMZSourceSemantics
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    (U : Data F sigmaBar commute)
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    (D : Definitions k (frobeniusFixedSubgroup F) A Block)
    (P : LocalPair k (frobeniusFixedSubgroup F) A)
    (realise : A → Subgroup Gbar)
    (realise_injective : Function.Injective realise) : Prop where
  realise_inner : ∀ h : frobeniusFixedSubgroup F,
    realise ((MulAut.conj h) • P.1) =
      (realise P.1).map (MulAut.conj (h : Gbar))
  centralizer_eq_selected :
    Subgroup.centralizer (realise P.1 : Set Gbar) = U.selectedLevi
  levi_image_eq_fixedCentralizer :
    (D.levi P.1).map
        (finiteNormalizer (H := frobeniusFixedSubgroup F)
          (A := A) P.1).subtype =
      fixedLevi F (Subgroup.centralizer (realise P.1 : Set Gbar))

/-- The published normaliser statement used in E5, separated from the
semantic interpretation of torus labels and finite Levis.  In the manuscript
this is `N_H(T) = N_H(C_Hbar(T))`, obtained in the proof of FMZ,
Proposition 3.24(a). -/
def FMZNormalizerEquality
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    {realise : A → Subgroup Gbar}
    {realise_injective : Function.Injective realise}
    (_S : FMZSourceSemantics U D P realise realise_injective) : Prop :=
  (Subgroup.normalizer (realise P.1 : Set Gbar)).comap
      (frobeniusFixedSubgroup F).subtype =
    (Subgroup.normalizer
      (Subgroup.centralizer (realise P.1 : Set Gbar) : Set Gbar)).comap
      (frobeniusFixedSubgroup F).subtype

/-- Inner equivariance and injectivity of the torus realisation identify the
abstract label stabiliser with the concrete finite torus normaliser. -/
theorem FMZSourceSemantics.finiteNormalizer_eq_realisedNormalizer
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    {realise : A → Subgroup Gbar}
    {realise_injective : Function.Injective realise}
    (S : FMZSourceSemantics U D P realise realise_injective) :
    finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1 =
      (Subgroup.normalizer (realise P.1 : Set Gbar)).comap
        (frobeniusFixedSubgroup F).subtype := by
  ext h
  rw [mem_finiteNormalizer_iff]
  change ((MulAut.conj h) • P.1 = P.1) ↔
    (h : Gbar) ∈ Subgroup.normalizer (realise P.1 : Set Gbar)
  constructor
  · intro hlabel
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    simpa only using
      (S.realise_inner h).symm.trans (congrArg realise hlabel)
  · intro hnormal
    apply realise_injective
    rw [S.realise_inner h]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormal

/-- The source-shaped torus and Levi semantics, together with the published
FMZ normaliser equality, produce the compact E5 interface used downstream.
No normaliser transport, normality assertion, or action-intertwining equation
is an input. -/
theorem FMZSourceSemantics.toFMZIdentification
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    {realise : A → Subgroup Gbar}
    {realise_injective : Function.Injective realise}
    (S : FMZSourceSemantics U D P realise realise_injective)
    (fmzNormalizer : FMZNormalizerEquality S) :
    FMZIdentification U D P where
  normalizer_eq := by
    calc
      finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1 =
          (Subgroup.normalizer (realise P.1 : Set Gbar)).comap
            (frobeniusFixedSubgroup F).subtype :=
        S.finiteNormalizer_eq_realisedNormalizer
      _ = (Subgroup.normalizer
            (Subgroup.centralizer
              (realise P.1 : Set Gbar) : Set Gbar)).comap
            (frobeniusFixedSubgroup F).subtype := fmzNormalizer
      _ = U.selectedFixedNormalizer := by
        rw [S.centralizer_eq_selected]
        rfl
  levi_image_eq := by
    calc
      (D.levi P.1).map
          (finiteNormalizer (H := frobeniusFixedSubgroup F)
            (A := A) P.1).subtype =
          fixedLevi F
            (Subgroup.centralizer (realise P.1 : Set Gbar)) :=
        S.levi_image_eq_fixedCentralizer
      _ = U.selectedFiniteLevi := by
        rw [S.centralizer_eq_selected]
        rfl

/-- The literal FMZ Levi mapped into the ambient finite group and then
identified with the canonical selected finite Levi. -/
noncomputable def FMZIdentification.fmzLeviEquivSelected
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P) :
    D.levi P.1 ≃* U.selectedFiniteLevi :=
  ((D.levi P.1).equivMapOfInjective
      (finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1).subtype
      (finiteNormalizer (H := frobeniusFixedSubgroup F)
        (A := A) P.1).subtype_injective).trans
    (MulEquiv.subgroupCongr I.levi_image_eq)

@[simp]
theorem FMZIdentification.fmzLeviEquivSelected_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P) (x : D.levi P.1) :
    (((I.fmzLeviEquivSelected x : U.selectedFiniteLevi) :
        frobeniusFixedSubgroup F) : Gbar) =
      ((((x : D.levi P.1) :
        finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1) :
          frobeniusFixedSubgroup F) : Gbar) :=
  rfl

/-- The canonical standard-finite-Levi equivalence with the literal FMZ
Levi. -/
noncomputable def FMZIdentification.standardFiniteLeviEquivFMZ
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P) :
    U.standardFiniteLevi ≃* D.levi P.1 :=
  U.finiteLeviEquiv.trans I.fmzLeviEquivSelected.symm

@[simp]
theorem FMZIdentification.standardFiniteLeviEquivFMZ_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P) (x : U.standardFiniteLevi) :
    (((((I.standardFiniteLeviEquivFMZ x : D.levi P.1) :
        finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1) :
          frobeniusFixedSubgroup F) : Gbar)) =
      U.langElement * (x : Gbar) * U.langElement⁻¹ := by
  change
    (((((I.fmzLeviEquivSelected.symm (U.finiteLeviEquiv x) :
        D.levi P.1) :
          finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1) :
            frobeniusFixedSubgroup F) : Gbar)) =
      U.langElement * (x : Gbar) * U.langElement⁻¹
  have hselected := I.fmzLeviEquivSelected_coe
    (I.fmzLeviEquivSelected.symm (U.finiteLeviEquiv x))
  rw [I.fmzLeviEquivSelected.apply_symm_apply] at hselected
  rw [← hselected, U.finiteLeviEquiv_coe]

/-- The canonical standard-fixed-normaliser equivalence with the literal
FMZ finite normaliser. -/
def FMZIdentification.standardNormalizerEquivFMZ
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P) :
    U.standardFixedNormalizer ≃*
      finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1 :=
  U.fixedNormalizerEquiv.trans
    (MulEquiv.subgroupCongr I.normalizer_eq.symm)

@[simp]
theorem FMZIdentification.standardNormalizerEquivFMZ_coe
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P) (x : U.standardFixedNormalizer) :
    (((I.standardNormalizerEquivFMZ x :
        finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1) :
          frobeniusFixedSubgroup F) : Gbar) =
      U.langElement * (x : Gbar) * U.langElement⁻¹ :=
  rfl

/-- The literal FMZ Levi is normal in the literal FMZ finite normaliser.
This is derived from the two ambient subgroup identifications and the fact
that an algebraic Levi is normal in its algebraic normaliser. -/
theorem FMZIdentification.fmzLevi_normal
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P) : (D.levi P.1).Normal where
  conj_mem n hn g := by
    have hnSelected :
        ((n : finiteNormalizer
          (H := frobeniusFixedSubgroup F) (A := A) P.1) :
            frobeniusFixedSubgroup F) ∈ U.selectedFiniteLevi := by
      have hnImage :
          ((n : finiteNormalizer
            (H := frobeniusFixedSubgroup F) (A := A) P.1) :
              frobeniusFixedSubgroup F) ∈
            (D.levi P.1).map
              (finiteNormalizer (H := frobeniusFixedSubgroup F)
                (A := A) P.1).subtype :=
        ⟨n, hn, rfl⟩
      rwa [I.levi_image_eq] at hnImage
    have hgSelected :
        ((g : finiteNormalizer
          (H := frobeniusFixedSubgroup F) (A := A) P.1) :
            frobeniusFixedSubgroup F) ∈ U.selectedFixedNormalizer := by
      rw [← I.normalizer_eq]
      exact g.property
    have hconjSelected :
        (((g * n * g⁻¹ :
          finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1) :
            frobeniusFixedSubgroup F)) ∈ U.selectedFiniteLevi := by
      change (g : Gbar) * (n : Gbar) * (g : Gbar)⁻¹ ∈ U.selectedLevi
      change (g : Gbar) ∈ U.selectedAlgebraicNormalizer at hgSelected
      change (n : Gbar) ∈ U.selectedLevi at hnSelected
      exact (Subgroup.mem_normalizer_iff.mp hgSelected (n : Gbar)).mp
        hnSelected
    have hconjImage :
        (((g * n * g⁻¹ :
          finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1) :
            frobeniusFixedSubgroup F)) ∈
          (D.levi P.1).map
            (finiteNormalizer (H := frobeniusFixedSubgroup F)
              (A := A) P.1).subtype := by
      rwa [I.levi_image_eq]
    rcases hconjImage with ⟨z, hz, hzeq⟩
    have heq : g * n * g⁻¹ = z := by
      apply Subtype.ext
      exact hzeq.symm
    rw [heq]
    exact hz

/-- The `RationalLeviNormalizerTransport` is derived from the unified witness
and the two ambient FMZ subgroup equalities. -/
noncomputable def FMZIdentification.relativeTransport
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P) :
    RationalLeviNormalizerTransport U.twistedFrobenius
      U.standardFixedNormalizer U.standardLevi
      (finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1)
      (D.levi P.1) where
  normalizerEquiv := I.standardNormalizerEquivFMZ
  baseEquiv := U.fixedBaseEquivStandardFiniteLevi.trans
    I.standardFiniteLeviEquivFMZ
  extendsBase x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [FMZIdentification.standardNormalizerEquivFMZ_coe]
    change U.langElement * (x : Gbar) * U.langElement⁻¹ =
      (((I.fmzLeviEquivSelected.symm
        (U.finiteLeviEquiv (U.fixedBaseEquivStandardFiniteLevi x)) :
          D.levi P.1) :
            finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1) :
              frobeniusFixedSubgroup F)
    have hselected := I.fmzLeviEquivSelected_coe
      (I.fmzLeviEquivSelected.symm
        (U.finiteLeviEquiv (U.fixedBaseEquivStandardFiniteLevi x)))
    rw [I.fmzLeviEquivSelected.apply_symm_apply] at hselected
    rw [← hselected, U.finiteLeviEquiv_coe,
      U.fixedBaseEquivStandardFiniteLevi_coe]

/-- The standard fixed normaliser action transports to the actual
finite-normaliser automorphism induced by the finite inner twist. -/
theorem FMZIdentification.normalizerEquiv_intertwines_tau
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P)
    (label_fixed : U.langData.tau • P.1 = P.1)
    (y : U.standardFixedNormalizer) :
    I.standardNormalizerEquivFMZ
        (restrictToStableSubgroup U.standardFixedNormalizer
          (frobeniusFixedSubgroupHom U.twistedFrobenius
            sigmaBar.toMonoidHom U.commute_twistedFrobenius)
          U.standardFixedNormalizer_stable y) =
      inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed
        (I.standardNormalizerEquivFMZ y) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [inducedFiniteNormalizerAut_coe]
  rw [U.langData_tau_coe,
    FMZIdentification.standardNormalizerEquivFMZ_coe,
    FMZIdentification.standardNormalizerEquivFMZ_coe]
  exact (innerTwistedAut_conjugate sigmaBar U.langElement (y : Gbar)).symm

/-- The coherent E8 package constructed from the unified rational-Levi
witness, the two E5 subgroup identifications, and the source-shaped Weyl
representative data.  No normaliser transport or intertwining equation is an
additional input. -/
noncomputable def FMZIdentification.e8Data
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P)
    (WeylNormalizer : Type u) [Group WeylNormalizer]
    (WeylLevi : Subgroup WeylNormalizer)
    (weyl : WeylRepresentativeData U.twistedFrobenius
      sigmaBar.toMonoidHom U.commute_twistedFrobenius
      U.standardFixedNormalizer U.standardFixedNormalizer_stable
      U.standardLevi WeylNormalizer WeylLevi) :
    EvenFieldGenericOrbitE8.Data sigmaBar.toMonoidHom U.langData.tau P.1
      U.standardLevi (D.levi P.1) WeylNormalizer where
  F := U.twistedFrobenius
  commute := U.commute_twistedFrobenius
  standardNormalizer := U.standardFixedNormalizer
  standardNormalizer_stable := U.standardFixedNormalizer_stable
  WeylLevi := WeylLevi
  weyl := weyl
  transport := I.relativeTransport
  intertwines := I.normalizerEquiv_intertwines_tau

/-- The exact E8 relative-difference conclusion derived from the unified
construction. -/
theorem FMZIdentification.relativeDifference_of_weylData
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P)
    (WeylNormalizer : Type u) [Group WeylNormalizer]
    (WeylLevi : Subgroup WeylNormalizer)
    (weyl : WeylRepresentativeData U.twistedFrobenius
      sigmaBar.toMonoidHom U.commute_twistedFrobenius
      U.standardFixedNormalizer U.standardFixedNormalizer_stable
      U.standardLevi WeylNormalizer WeylLevi) :
    ∀ (label_fixed : U.langData.tau • P.1 = P.1)
      (x : finiteNormalizer
        (H := frobeniusFixedSubgroup F) (A := A) P.1),
      x⁻¹ * inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed x ∈
        D.levi P.1 :=
  (I.e8Data WeylNormalizer WeylLevi weyl).relativeDifference

/-- Concrete E8 endpoint for the actual relative Weyl quotient
`Q = N_W(W_I) / W_I`.  Since the denominator has already been divided out,
the general E8 adapter is instantiated with the bottom subgroup of `Q`.
No lift from the algebraic normaliser to `N_W(W_I)` is required. -/
theorem FMZIdentification.relativeDifference_of_relativeWeylQuotientData
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    (I : FMZIdentification U D P)
    (Q : Type u) [Group Q]
    (quotient : RelativeWeylQuotientData U.twistedFrobenius
      sigmaBar.toMonoidHom U.commute_twistedFrobenius
      U.standardFixedNormalizer U.standardFixedNormalizer_stable
      U.standardLevi Q) :
    ∀ (label_fixed : U.langData.tau • P.1 = P.1)
      (x : finiteNormalizer
        (H := frobeniusFixedSubgroup F) (A := A) P.1),
      x⁻¹ * inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed x ∈
        D.levi P.1 :=
  I.relativeDifference_of_weylData Q ⊥
    (quotient.toWeylRepresentativeData U.twistedFrobenius
      sigmaBar.toMonoidHom U.commute_twistedFrobenius
      U.standardFixedNormalizer U.standardFixedNormalizer_stable
      U.standardLevi Q)

/-- The automorphism induced on the literal FMZ Levi after the E8
relative-difference calculation. -/
noncomputable def FMZIdentification.fmzBaseAut
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    [Fintype (finiteNormalizer
      (H := frobeniusFixedSubgroup F) (A := A) P.1)]
    (I : FMZIdentification U D P)
    (WeylNormalizer : Type u) [Group WeylNormalizer]
    (WeylLevi : Subgroup WeylNormalizer)
    (weyl : WeylRepresentativeData U.twistedFrobenius
      sigmaBar.toMonoidHom U.commute_twistedFrobenius
      U.standardFixedNormalizer U.standardFixedNormalizer_stable
      U.standardLevi WeylNormalizer WeylLevi)
    (label_fixed : U.langData.tau • P.1 = P.1) :
    MulAut (D.levi P.1) :=
  let alphaN := inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed
  restrictAut (D.levi P.1) alphaN
    (subgroup_stable_of_difference (D.levi P.1) alphaN
      (I.relativeDifference_of_weylData WeylNormalizer WeylLevi weyl
        label_fixed))

/-- The canonical standard-to-FMZ finite-Levi equivalence intertwines the
standard field action with the induced FMZ base automorphism.  The proof uses
the normaliser intertwining equation and the fact that the normaliser
transport restricts to the finite-Levi transport. -/
theorem FMZIdentification.standardFiniteLeviEquivFMZ_intertwines
    {F : Gbar →* Gbar} {sigmaBar : MulAut Gbar}
    {commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x)}
    {U : Data F sigmaBar commute}
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    {D : Definitions k (frobeniusFixedSubgroup F) A Block}
    {P : LocalPair k (frobeniusFixedSubgroup F) A}
    [Fintype (finiteNormalizer
      (H := frobeniusFixedSubgroup F) (A := A) P.1)]
    (I : FMZIdentification U D P)
    (WeylNormalizer : Type u) [Group WeylNormalizer]
    (WeylLevi : Subgroup WeylNormalizer)
    (weyl : WeylRepresentativeData U.twistedFrobenius
      sigmaBar.toMonoidHom U.commute_twistedFrobenius
      U.standardFixedNormalizer U.standardFixedNormalizer_stable
      U.standardLevi WeylNormalizer WeylLevi)
    (label_fixed : U.langData.tau • P.1 = P.1)
    (x : U.standardFiniteLevi) :
    I.standardFiniteLeviEquivFMZ (U.standardFieldAut x) =
      I.fmzBaseAut WeylNormalizer WeylLevi weyl label_fixed
        (I.standardFiniteLeviEquivFMZ x) := by
  let xb : fixedBase U.twistedFrobenius U.standardFixedNormalizer
      U.standardLevi := U.fixedBaseEquivStandardFiniteLevi.symm x
  let xbSigma : fixedBase U.twistedFrobenius U.standardFixedNormalizer
      U.standardLevi :=
    U.fixedBaseEquivStandardFiniteLevi.symm (U.standardFieldAut x)
  let alphaStandard : U.standardFixedNormalizer →* U.standardFixedNormalizer :=
    restrictToStableSubgroup U.standardFixedNormalizer
      (frobeniusFixedSubgroupHom U.twistedFrobenius
        sigmaBar.toMonoidHom U.commute_twistedFrobenius)
      U.standardFixedNormalizer_stable
  have hstandard : alphaStandard (xb : U.standardFixedNormalizer) =
      (xbSigma : U.standardFixedNormalizer) := by
    apply Subtype.ext
    apply Subtype.ext
    change sigmaBar (x : Gbar) = sigmaBar (x : Gbar)
    rfl
  have hnormalizer := I.normalizerEquiv_intertwines_tau label_fixed
    (xb : U.standardFixedNormalizer)
  change
    I.standardNormalizerEquivFMZ
        (alphaStandard (xb : U.standardFixedNormalizer)) =
      inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed
        (I.standardNormalizerEquivFMZ
          (xb : U.standardFixedNormalizer)) at hnormalizer
  rw [hstandard] at hnormalizer
  have hbase := I.relativeTransport.extendsBase xb
  have hbaseSigma := I.relativeTransport.extendsBase xbSigma
  have hbase_x :
      I.standardNormalizerEquivFMZ
          (xb : U.standardFixedNormalizer) =
        (((I.standardFiniteLeviEquivFMZ x : D.levi P.1) :
          finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1)) := by
    simpa [FMZIdentification.relativeTransport, xb] using hbase
  have hbase_sigma :
      I.standardNormalizerEquivFMZ
          (xbSigma : U.standardFixedNormalizer) =
        (((I.standardFiniteLeviEquivFMZ (U.standardFieldAut x) :
            D.levi P.1) :
          finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1)) := by
    simpa [FMZIdentification.relativeTransport, xbSigma] using hbaseSigma
  rw [hbase_x, hbase_sigma] at hnormalizer
  apply Subtype.ext
  change
    (((I.standardFiniteLeviEquivFMZ (U.standardFieldAut x) :
      D.levi P.1) :
        finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1)) =
      inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed
        (((I.standardFiniteLeviEquivFMZ x : D.levi P.1) :
          finiteNormalizer (H := frobeniusFixedSubgroup F) (A := A) P.1))
  exact hnormalizer

end FMZ

end ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
